
module KamiD.Dev.2023-11-09.Main where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Relation.Nullary.Decidable.Core

module _ {A : 𝒰 𝑖} where
  -- data _!≣_ : A -> A -> 𝒰 𝑖 where
  --   irrefl : ∀{a b} -> {{_ : {a ≣ b} -> 𝟘-𝒰}} -> a !≣ b

-- data Name : 𝒰₀ where
--   a b c d e f p q r α β γ δ : Name

Name = ℕ
a b c d p q r : Name
a = 0
b = 1
c = 2
d = 3
p = 4
q = 5
r = 6


-- data hasDiff : (a b : ℕ) (c : Bool) -> 𝒰₀ where
--   instance same : hasDiff 0 0 false
--   instance takeleft : ∀{a} -> hasDiff (suc a) 0 true
--   instance takeright : ∀{a} -> hasDiff 0 (suc a) true
--   instance step : ∀{a b c} -> {{_ : hasDiff a b c}} -> hasDiff (suc a) (suc b) c


-- data Uneq (x y : ℕ) {z : ℕ} {{A : hasDiff x y false}} : 𝒰₀ where

-- data Bla : (x y : ℕ) (z : Bool) -> 𝒰₀ where
--   instance left : ∀{x} -> Bla x x false
--   instance right : ∀{x y z} -> {{_ : hasDiff x y z}} -> Bla x y true



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
  constructor _⊩_
  field ctx : Ctx
  field {{jni}} : Γ ⊇ ctx
  field typ : ctx ⊢Type! k

infixl 50 _⊩_

open _⊢Type_ public

data Ctx where
  [] : Ctx
  -- _,[_⊢_] : (Γ : Ctx) -> (Δ : Ctx) -> {{_ : Γ ⊇ Δ}} -> ∀{k} -> (A : Δ ⊢Type! k) -> Ctx
  _,[_∶_] : (Γ : Ctx) -> Name -> ∀{k} -> _⊢Type_ Γ k -> Ctx -- (Δ : Ctx) -> {{_ : Γ ⊇ Δ}} -> ∀{k} -> (A : Δ ⊢Type! k) -> Ctx

infixl 50 _,[_∶_]

ctxl : Ctx -> ℕ
ctxl [] = 0
ctxl (Γ ,[ x ∶ x₁ ]) = suc (ctxl Γ)

record _⊢Var_∶_ {k} (Γ : Ctx) (x : Name) (A : Γ ⊢Type k) : 𝒰₀ where
  field prefix : Ctx
  field {{jni}} : Γ ⊇ prefix
  field {{jni2}} : prefix ⊇ A .ctx
  field pf : Γ ⊇ prefix ,[ x ∶ A .ctx ⊩ A .typ ]

-- instance
--   postulate _ : ∀{Γ Δ Ε} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> Γ ⊇ Ε

data _⊇_ where
  instance empty : [] ⊇ []
  -- instance empty : ∀{Γ} -> Γ ⊇ Γ
  -- instance bot : ∀{Γ} -> Γ ⊇ []
  instance take : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ ,[ x ∶ Ε ⊩ A ]
  instance skip : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ


data _⊢Type!_ where
  -- Shape : [] ⊢Type!
  𝒮 : ∀{Γ} -> Γ ⊢Shapes! -> Γ ⊢Type! 𝑆

data _⊢Shapes! where
  [] : [] ⊢Shapes!
  _,_ : ∀{Γ Δ Ε} -> {{_ : Γ ⊇ Δ}} -> Δ ⊢Shapes! -> {{_ : Γ ⊇ Ε}} -> Ε ⊢Type! 𝑆 -> Γ ⊢Shapes! -- TODO!: Missing that Δ and Ε cover Γ

data _⊢!_ where
  -- 𝒮 : ∀

--------------------------------------------------
-- Helper

module _ where
  private instance
    _ = isTop-⊇-[]
    _ = id-⊇
  data _↤_∪_ : (Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> 𝒰₀ where
    instance emptyleft : ∀{Γ} -> Γ ↤ Γ ∪ []
    instance emptyright : ∀{Γ} -> Γ ↤ [] ∪ Γ
    instance takeleft : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k}
              -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> {{_ : Δ ⊇ Ε}}
              -> {{_ : Γ ↤ Δ ∪ Ε}}
              -> _↤_∪_ (Γ ,[ x ∶ Ε ⊩ A ]) (Δ ,[ x ∶ Ε ⊩ A ]) Ε {{take}} {{skip}}
    instance takeright : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k}
              -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> {{_ : Δ ⊇ Ε}}
              -> {{_ : Γ ↤ Δ ∪ Ε}}
              -> _↤_∪_ (Γ ,[ x ∶ Ε ⊩ A ]) Δ (Ε ,[ x ∶ Ε ⊩ A ]) {{skip}} {{take}}
    instance takeboth : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k}
              -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> {{_ : Δ ⊇ Ε}}
              -> {{_ : Γ ↤ Δ ∪ Ε}}
              -> _↤_∪_ (Γ ,[ x ∶ Ε ⊩ A ]) (Δ ,[ x ∶ Ε ⊩ A ]) (Ε ,[ x ∶ Ε ⊩ A ]) {{take}} {{take}}


  data VarCtx : (Γ Δ : Ctx) -> {{_ : Γ ⊇ Δ}} -> Fin (ctxl Γ) -> 𝒰₀ where
    instance take : ∀{Γ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Ε}} -> VarCtx (Γ ,[ x ∶ Ε ⊩ A ]) (Ε ,[ x ∶ Ε ⊩ A ]) {{take}} zero
    instance skip : ∀{Γ Δ Ε k n y} -> {A : Ε ⊢Type! k} -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}} -> {{_ : VarCtx Γ Δ n}} -> VarCtx (Γ ,[ y ∶ Ε ⊩ A ]) Δ {{skip}} (suc n)


data GetVar : ∀{k} -> (Γ : Ctx) -> (x : Name) -> (A : Γ ⊢Type k) -> (Γ ⊢Var x ∶ A) -> 𝒰₀ where

data Rist (A : 𝒰 𝑖) : 𝒰 𝑖 where
  [] : Rist A
  _,_ : Rist A -> A -> Rist A

module _ where
  private instance _ = isTop-⊇-[]

  findVar : Name -> (Γ : Ctx) -> Maybe (Fin (ctxl Γ))
  findVar x [] = nothing
  findVar x (Γ ,[ y ∶ x₂ ]) with (Data.Nat._≟_ x y) .does
  ... | false = map-Maybe suc (findVar x Γ)
  ... | true = just zero

  data VarsCtxHelper : (Γ Δ : Ctx) -> {{_ : Γ ⊇ Δ}} -> Rist Name -> 𝒰₀ where
    instance empty : ∀{Γ} -> VarsCtxHelper Γ [] []
    instance step : ∀{Γ Δ₀ Δ₁ Δ₂ xs x i}
                  -> {{_ : Γ ⊇ Δ₀}}
                  -> {{_ : Γ ⊇ Δ₂}}
                  -> {{_ : VarsCtxHelper Γ Δ₀ xs}}
                  -> {{_ : findVar x Γ ≣ just i}}
                  -> {{_ : Γ ⊇ Δ₁}} -> {{_ : VarCtx Γ Δ₁ i}}
                  -> {{_ : Δ₂ ⊇ Δ₀}}
                  -> {{_ : Δ₂ ⊇ Δ₁}}
                  -> {{_ : Δ₂ ↤ Δ₀ ∪ Δ₁}}
                  -> VarsCtxHelper Γ Δ₂ (xs , x)

-- subCtxByName : Rist Name -> (Γ : Ctx) -> ∑ λ (Δ : Ctx) -> Γ ⊇ Δ
-- subCtxByName = {!!}

_?⊩_ : ∀{Γ Δ k} -> {{_ : Γ ⊇ Δ}} -> (xs : Rist Name) -> {{_ : VarsCtxHelper Γ Δ xs}} -> Δ ⊢Type! k -> Γ ⊢Type k
_?⊩_ {Δ = Δ} xs tp = Δ ⊩ tp

--------------------------------------------------
-- Examples

module Ex1 where
  -- private instance _ = isTop-⊇-[]

  Pt : ∀{Γ} -> {{_ : Γ ⊇ []}} -> _⊢Type_ Γ 𝑆
  Pt = [] ⊩ 𝒮 []

  pt : Ctx
  pt = [] ,[ a ∶ Pt ]

  twopt : Ctx
  twopt = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ]

  -- line : Ctx
  -- line = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ] ,[ p ∶ ([] , a)?⊩ {!!} ]



  -- line : Ctx
  -- line = [] ,[ [] ⊢ 𝒮 [] ] ,[ [] ⊢ 𝒮 [] ]




