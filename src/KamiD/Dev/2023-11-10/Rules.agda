{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2023-11-10.Rules where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-10.Core

Name = String

data Kind : 𝒰₀ where
  𝑆 : Kind

data Ctx : 𝒰₀
data _⊢Type!_ : (Γ : Ctx) -> Kind -> 𝒰₀
-- data _⊢Type : (Γ : Ctx) -> 𝒰₀
-- data _⊢Var!_ : (Γ : Ctx) ->  -> 𝒰₀
data _⊢Shapes! : (Γ : Ctx) -> 𝒰₀
data _⊢!_ : ∀{k} -> (Γ : Ctx) -> Γ ⊢Type! k -> 𝒰₀
data _⊇_ : (Γ : Ctx) (Δ : Ctx) -> 𝒰₀

infixl 40 _⊇_

record _⊢Type_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
  inductive
  pattern
  constructor _⊩_
  field ctx : Ctx
  field {{jni}} : Γ ⊇ ctx
  field typ : ctx ⊢Type! k

infixl 50 _⊩_

open _⊢Type_ public

instance
  hasNotation-!:⊢Type : ∀{Γ k} -> hasNotation-! (Γ ⊢Type k) (λ x -> x .ctx ⊢Type! k)
  hasNotation-!:⊢Type = record { _! = λ a → a .typ }


data Ctx where
  [] : Ctx
  _,[_∶_] : (Γ : Ctx) -> Name -> ∀{k} -> _⊢Type_ Γ k -> Ctx

infixl 50 _,[_∶_]

len-Ctx : Ctx -> ℕ
len-Ctx [] = 0
len-Ctx (Γ ,[ x ∶ x₁ ]) = suc (len-Ctx Γ)

instance
  Notation-Absolute-Ctx : Notation-Absolute Ctx ℕ
  Notation-Absolute-Ctx = record { ∣_∣ = len-Ctx }

data _⊇_ where
  empty : [] ⊇ []
  take : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ ,[ x ∶ Ε ⊩ A ]
  skip : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ

isTop-⊇-[] : ∀{Γ} -> Γ ⊇ []
isTop-⊇-[] {[]} = empty
isTop-⊇-[] {Γ ,[ x ∶ Ε ⊩ A ]} = skip {{isTop-⊇-[]}} {{it}}

id-⊇ : ∀{Γ} -> Γ ⊇ Γ
id-⊇ {[]} = empty
id-⊇ {Γ ,[ x ∶ Ε ⊩ A ]} = take {{id-⊇}} {{it}}


pattern _⊩⁺_ Ε A = _⊩_ Ε {{skip}} A

data _⊢_isKind_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (k : Kind) -> Set where
  zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind k
  suc : ∀{Γ x k i j} -> {A : Γ ⊢Type k} -> {{_ : Γ ⊢ i isKind j}} -> Γ ,[ x ∶ A ] ⊢ suc i isKind j

module isKindInstances where
  instance
    isKind:zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind k
    isKind:zero = _⊢_isKind_.zero

    isKind:suc : ∀{Γ x k i j} -> {A : Γ ⊢Type k} -> {{_ : Γ ⊢ i isKind j}} -> Γ ,[ x ∶ A ] ⊢ suc i isKind j
    isKind:suc = suc

module _ where
  open isKindInstances
  data _⊢_isType_ : (Γ : Ctx) -> ∀ i -> ∀{k} -> {{_ : Γ ⊢ i isKind k}} -> Γ ⊢Type k -> Set where
    zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type! k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType (_⊩⁺_ Ε A)
    suc : ∀{Γ Ε Η x k j i} -> {{_ : Γ ⊢ i isKind k}} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊢ i isType (Ε ⊩ A)}}
                -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type! j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType (Ε ⊩⁺ A)


module _ where
  private instance
    _ = isTop-⊇-[]
    _ = id-⊇
  data _↤_∪_ : (Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> 𝒰₀ where
    emptyleft : ∀{Γ} -> Γ ↤ Γ ∪ []
    emptyright : ∀{Γ} -> Γ ↤ [] ∪ Γ
    takeleft : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type! k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) Ε {{take}} {{skip}}
    takeright : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type! k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) Δ (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{skip}} {{take}}
    takeboth : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type! k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{take}} {{take}}

-- record WithVar {Ε k} (A : Ε ⊢Type! k) : 𝒰₀ where
--   field name : Name

--   private instance _ = id-⊇

--   getCtxWithVar : Ctx
--   getCtxWithVar = Ε ,[ name ∶ Ε ⊩ A ]

-- open WithVar public

-- instance
--   Notation-Absolute-WithVar : ∀{Ε k} -> {A : Ε ⊢Type! k} -> Notation-Absolute (WithVar A) Ctx
--   Notation-Absolute-WithVar = record { ∣_∣ = getCtxWithVar }


_∶!_ : ∀ x -> ∀ {Ε k} (A : Ε ⊢Type! k) -> Ctx
_∶!_ x {Ε} A = Ε ,[ x ∶ Ε ⊩ A ]
  where instance _ = id-⊇

-- mergeType : ∀{Γ k} -> (A : Γ ⊢Type k) -> Ctx
-- mergeType (Ε ⊩ A) = (_ ∶! A)

-- record _⊢Var_∶_ {k} (Γ : Ctx) (i : Γ ⊢Varkind k) {Ε : Ctx} (A : Ε ⊢Type! k) : Set where
--   constructor var_by_
--   inductive
--   field name : Name
--   field ⟨_⟩ : Γ ⊇ (name ∶! A)

-- open _⊢Var_∶_ public

data _⊢Type!_ where
  -- Shape : [] ⊢Type!
  𝒮 : ∀{Γ} -> Γ ⊢Shapes! -> Γ ⊢Type! 𝑆

data _⊢Shapes! where
  [] : [] ⊢Shapes!
  _&_ : ∀{Γ Δ} -> {{_ : Γ ⊇ Δ}}
        -> Δ ⊢Shapes!
        -> {A : Γ ⊢Type 𝑆}
        -> ∀ i -> {{_ : Γ ⊢ i isKind 𝑆}} -> {{_ : Γ ⊢ i isType A}}
        -- -> {{X : Γ ⊇ (x ∶! A)}}
        -> let instance _ = jni A
           in {{_ : Γ ↤ Δ ∪ (ctx A)}}
           -- in {{_ : Γ ↤ Δ ∪ (_ ∶! A)}}
        -- -> {{_ : Γ ↤ Δ ∪ ctx A}}
        -> Γ ⊢Shapes!

infixl 40 _&_

data _⊢!_ where
  -- 𝒮 : ∀

--------------------------------------------------------------------

wk₀-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
wk₀-⊢Type (Ε ⊩ B) = _⊩_ Ε {{skip }} B




