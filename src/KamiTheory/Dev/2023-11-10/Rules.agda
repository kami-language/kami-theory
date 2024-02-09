{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2023-11-10.Rules where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiTheory.Dev.2023-11-10.Core

Name = ℕ

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
  suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isKind j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isKind j

data _⊢_isName_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (x : Name) -> Set where
  zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isName x
  suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isName j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isName j

-- module isKindInstances where
--   instance
--     isKind:zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind k
--     isKind:zero = _⊢_isKind_.zero

--     isKind:suc : ∀{Γ x k i j} -> {A : Γ ⊢Type k} -> {{_ : Γ ⊢ i isKind j}} -> Γ ,[ x ∶ A ] ⊢ suc i isKind j
--     isKind:suc = suc

module _ where
  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> Γ ⊢Type k -> Set where
  --   zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type! k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType (_⊩⁺_ Ε A)
  --   suc : ∀{Γ Ε Η x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type! k} -> (Γ ⊢ i isType (Ε ⊩ A))
  --               -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type! j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType (Ε ⊩⁺ A)

  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> ∀{Ε} -> Ε ⊢Type! k -> Set where
  --   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isType typ A
  --   suc : ∀{Γ Ε x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {A : Ε ⊢Type! k} -> (Γ ⊢ i isType (A))
  --               -> {B : Γ ⊢Type j} -> Γ ,[ x ∶ B ] ⊢ (suc i) isType (A)

  data _⊢_isType_ : (Γ : Ctx) -> ∀{k} -> (i : Fin ∣ Γ ∣) -> ∀{Ε} -> Ε ⊢Type! k -> Set where
    zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type! k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType A
    suc : ∀{Γ Ε Η x k j i} -> {A : Ε ⊢Type! k} -> (Γ ⊢ i isType (A))
                -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type! j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType A


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

record _⊢Var_∶_ {k} (Γ : Ctx) (i : Fin ∣ Γ ∣) {Ε : Ctx} (A : Ε ⊢Type! k) : Set where
  constructor var_by_and_
  inductive
  pattern
  field name : Name
  field isType:var : Γ ⊢ i isType A
  field isName:var : Γ ⊢ i isName name

open _⊢Var_∶_ public

to-⊇-⊢Type : ∀{Γ i k Ε} -> {A : Ε ⊢Type! k} -> Γ ⊢ i isType A -> Γ ⊇ Ε
to-⊇-⊢Type zero = skip
to-⊇-⊢Type (suc x) = skip {{to-⊇-⊢Type x}}

module _ where
  instance _ = id-⊇
  to-⊇-⊢Type-Var : ∀{Γ i k x Ε} -> {A : Ε ⊢Type! k} -> Γ ⊢ i isType A -> Γ ⊢ i isName x -> Γ ⊇ (Ε ,[ x ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var zero zero = take
  to-⊇-⊢Type-Var (suc x) (suc y) = skip {{to-⊇-⊢Type-Var x y}}

  to-⊇-⊢Type-Var2 : ∀{Γ i k Ε} -> {A : Ε ⊢Type! k} -> (z : Γ ⊢Var i ∶ A) -> Γ ⊇ (Ε ,[ name z ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var2 (var name₁ by P1 and P2) = to-⊇-⊢Type-Var P1 P2


data _⊢Type!_ where
  -- Shape : [] ⊢Type!
  𝒮 : ∀{Γ} -> Γ ⊢Shapes! -> Γ ⊢Type! 𝑆

data _⊢Shapes! where
  [] : [] ⊢Shapes!
  _&_ : ∀{Γ Δ Ε} -- -> {{_ : Γ ⊇ Δ}}
        -> Δ ⊢Shapes!
        -> {A : Ε ⊢Type! 𝑆}
        -> {x : Name}
        -> ∀ i -> {{z : Γ ⊢ i isType A}}
        -> {{_ : Γ ⊢ i isName x}}
        -- -> {{X : Γ ⊇ (x ∶! A)}}
        -- -> let instance _ = to-⊇-⊢Type-Var it it
        --    in {{_ : Γ ↤ Δ ∪ (x ∶! A)}}
           -- in {{_ : Γ ↤ Δ ∪ (_ ∶! A)}}
        -- -> {{_ : Γ ↤ Δ ∪ Ε}}
        -> Γ ⊢Shapes!

infixl 40 _&_

data _⊢!_ where
  -- 𝒮 : ∀

--------------------------------------------------------------------

wk₀-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
wk₀-⊢Type (Ε ⊩ B) = _⊩_ Ε {{skip }} B




