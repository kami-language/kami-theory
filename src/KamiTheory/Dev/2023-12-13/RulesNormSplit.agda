{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check #-}

module KamiTheory.Dev.2023-12-13.RulesNormSplit where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

-- open import Cubical.Core.Everything
-- open import KamiTheory.Dev.2023-12-05.Core

{-# BUILTIN REWRITE _≡_ #-}


data Test : 𝒰₀ where
  incl : ℕ -> Test
  _⋆_ : Test -> Test -> Test
  T0 : Test

postulate
  unit-l-Test : ∀{t : Test} -> T0 ⋆ t ≡ t

{-# REWRITE unit-l-Test #-}




Name = ℕ

---------------------------------------------------------------
-- Current goal (2023-12-10):
--
-- Types are indexed by their spatial space and their number
-- of time steps.
-- The topology is always Space x Time. There is, for now,
-- a distinction between the topological context and the
-- value context.
--
-- A variant which merges both might be developed in the future.
-- Types are formally maps on the points, and terms are maps
-- on the arrows.
--
-- A type is given by:
--  1. An assignment of types on the spatial arrow,
--  2. An assignment of types locally on the subset
--
-- We can write local types which describe the behaviour at
-- exactly a single role. And we can write types which describe
-- the down-connecting behaviour. A full type at a point contains:
-- a local type and for each down-arrow a type for that arrow.
--
-- We can project down-arrow types to types at the lower location.
-- An implementation for a full type mapping is given by giving an
-- implementation of the head, and then giving implementations for
-- the sum of the down projections...
--
-- Types can be given for upper sets. Once we have types for higher
-- open sets, we can construct a type for a lower open set (which is
-- bigger) by giving down-arrow-types for the next down arrows.
-- => Only top-level elements can have open local types...
-- => I can glue such a type together only if this local type matches
-- >>exactly<< with the down projection(s) from above.
--
-- Though there are also time-boundaries to the bottom... (maybe there
-- are not!) And they can only be there for the current top-level points
-- which are the actual processes we care about!
--
-- We can implement a type by implementing the local projections for each
-- point. These projections might give you negative or positive obligations,
-- where such a term is introduced by many lambdas, and at the end a series
-- of obligation-closers, where for each obligation we can only use variables
-- which are below...
--
-- Every term has to consume all negative variables, by filling them.
-- To fill a negative variable, you can only use part of the context
-- which is (≤) below you. By default every type can only be used at their
-- time point... A term always happens at a point in time.
--
-- Basic types might be positive or negative. Variables in the context
-- can be negative or positive or mixed. Mixed means I have to use them at their
-- time location (because they might be negative). We could say that positivity
-- is a modality, so that I can restrict the context to positive, and use those
-- further on... Also types can only depend on the positive subcontext...
--
-- A sequence of terms has to end in a purely positive context. For this we can
-- destructure the types in the context... Functions consume their input wholy.
-- Normal var projections mark a variable as "used". The app-rule makes sure that
-- it cannot be that both sides use the same variable. The var* projection rule
-- does not mark any variable as used. There is only one function type, since
-- it is enough to provide the correct matching type.
--
-- There are two var projections, one gives you the proper var, and says so in
-- the context. The other projects only the positive fragment, and says so in
-- the context. Then all rules which have two subterms, ensure that the resulting
-- context is a join where all possibly negative parts only appear on a single
-- side.
--
-- If a variable is purely positive, its split is irrelevant, in the sense that
-- it might be given to the left or to the right term.
--
-- For dependent types, we can depend on the positivitization of the context.
-- This means that we can use both positive and negative variables in types.
--
-- We have the restriction to positive fragments which happens when splitting
-- the context, and we have the positivitization for variables occuring in types,
-- that is in "dull" locations. => There is the dullification of a type, as
-- well as the positivitization.
--
-- We have a splitting of the context where we can choose for each variable:
--   -- we keep it whole in exactly one subcontext
--   -- we look at paths inside it, and decide for each path individually
--
-- This means in particular that the positive fragmentation which occurs in the
-- context is path-based. We don't change the types in the context, but we add
-- fragmentation cues. In this sense, the dullification breaks these cues again.
--
-- For the fragmentation in the type, we only allow full-neg-deletion. (for now)
--
-- Variables can be projected, this constructs a fragmentation annotation for the context.
--
--
-- Considering the context structure:
-- We have global (multi-) types and local types. Multitypes are "choreographies",
-- though they might of course be also simply assignments of values to different
-- locations. We can only access variables whose location-set is subset of our
-- current term goal location-set. There is a projection term-constructor which
-- projects from a set to a subset.
--
-- Goal: every multi-typed term is equivalent to the "sum" of its projected components.
-- In general the quantifiers take multi-types.
--
--
-- About variables/types which contain both positive and negative parts. When
-- we fill the negative parts, we have to substitute everything which depended on
-- that negative variable part with that value. But: When we give a negative value
-- into a function, we don't know how that function is going to fill that negative
-- variable. This means that there are three states for (X (Ψ[ x ↦ Y ] Z)):
--
--  - at X: we see that the inner term has filled the full x variable, but
--    we don't know which value is inside
--  - at Y: we cannot access x, because we are setting its value
--  - at Z: we don't have the x value, we have substituted it for Y
--
-- OR: The filling operation creates a proof of value.




-- spaces
-- data Space : 𝒰₀
-- data _⊢Subspace : Space -> 𝒰₀
-- data _⊢Pt : Space -> 𝒰₀
-- data _⊢Ln_⇾_ : (Σ : Space) -> (a b : Σ ⊢Pt) -> 𝒰₀

-- private variable
--   Σ : Space

-- times
-- data Time : 𝒰₀
-- data _⊢T : Time -> 𝒰₀
-- data _⊢TExt : Time -> 𝒰₀
-- data _⊢T_ : (Τ : Time) -> Τ ⊢TExt -> 𝒰₀
-- data _⊢_<T_ : (Τ : Time) -> ∀{X} -> (s t : Τ ⊢T X) -> 𝒰₀

-- private variable
--   Τ : Time

-------------------
-- we have a layer system for the context argument

Layer : 𝒰₀

private variable
  K L : Layer


-- types
data Ctxₛ : Layer -> 𝒰₀
data Ctx : Layer -> 𝒰₀

private variable
  Γ Δ : Ctx L

data _⇛_ : Ctx L -> Ctx L -> 𝒰₀

data _⊢Type : ∀ (Γ : Ctx L) -> 𝒰₀
data _⊢Typeₛ : ∀ (Γ : Ctx L) -> 𝒰₀
-- -- data _⊢VType_,_ : ∀ Σ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> ℕ -> 𝒰₀
-- data _⊢PtType_ : ∀ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> 𝒰₀
-- data _⊢PtBase_ : ∀ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> 𝒰₀
-- data _⊢LnType_ : ∀ (Γ : Ctx Σ Τ) -> ∀{a b} -> Σ ⊢Ln a ⇾ b -> 𝒰₀

data _⊢TypeOp : (Γ : Ctx L) -> 𝒰₀

-- terms
data _⊢Var_ : ∀ (Γ : Ctx L) -> (A : Γ ⊢Type) -> 𝒰₀
data _⊢_ : ∀ (Γ : Ctx L) -> (A : Γ ⊢Type) -> 𝒰₀

-- private variable
--   U V : Σ ⊢Subspace
--   x y : Σ ⊢Pt

-- _↷_ : Γ ⊢TypeOp -> Γ ⊢Type -> Γ ⊢Type



---------------------------------------------
-- parameters for basic types
-- data Charge : 𝒰₀ where
--   ⁺ ⁻ : Charge

data Chargelike : 𝒰₀ where
  ◌ +- : Chargelike

data Timelike : 𝒰₀ where
  𝟙 : Timelike

private variable
  τ : Timelike

-- data _⇌_ : Layer -> Layer -> 𝒰₀ where
--   ⁺ ⁻ : 𝟙 ⇌ ℂ

Layer = Chargelike ×-𝒰 Timelike

---------------------------------------------
-- types

⏏-Ctx : Ctxₛ L -> Ctx L

data Ctxₛ where
  [] : Ctxₛ L

  -- this should actually also contain the fragmentation
  -- assignment
  _,[_] : ∀ (Γ : Ctxₛ L) -> ⏏-Ctx Γ ⊢Type -> Ctxₛ L

  -- ⟨_⦙_ : K ⇌ L -> Ctx L -> Ctx K



  --------------
  -- Normalizable
  -- wkT : ∀ T -> Ctx Σ Τ -> Ctx Σ (Τ , T)
  -- _⟨_⟩ : Ctx Σ Τ -> Τ ⊢T -> Ctx Σ Τ

-- {-# REWRITE testeq #-}

Dull-Ctx : Ctx (+- , τ) -> Ctx (◌ , τ)
Dull-Type : ∀{Γ : Ctx (+- , τ)} -> Γ ⊢Type -> Dull-Ctx Γ ⊢Type


Restr-Ctx : (Γ : Ctx L) -> ∀{X} -> Γ ⊢Var X -> Ctx L
Restr-Type : {Γ : Ctx L} -> ∀(X : Γ ⊢Type) -> (v : Γ ⊢Var X) -> Restr-Ctx Γ v ⊢Type

data Ctx where
  ⏏ : Ctxₛ L -> Ctx L

  _,[_] : ∀ (Γ : Ctx L) -> Γ ⊢Type -> Ctx L

  Restr : (Γ : Ctx L) -> ∀{X} -> Γ ⊢Var X -> Ctx L

  _[_≔_] : ∀(Γ : Ctx (+- , τ)) {X} -> (v : Γ ⊢Var X) -> Restr-Ctx Γ v ⊢ Restr-Type X v -> Ctx (+- , τ)
  -- _[_≔_] : ∀(Γ : Ctx L) {X} -> Γ ⊢Var X -> Γ ⊢ X -> Ctx (L)

  Dull : Ctx (+- , τ) -> Ctx (◌ , τ)

  _&_wit_ : ∀(Γ : Ctx L) -> (A : Γ ⊢Type) -> Γ ⊢ A -> Ctx L


postulate
  β-Dull : ∀{Γ : Ctx (+- , τ)} {A}
         -> Dull (Γ ,[ A ]) ≡ Dull-Ctx Γ ,[ Dull-Type A ]

{-# REWRITE β-Dull #-}
  -- β-, : ∀{Γ A} -> ⏏-Ctx Γ ,[ A ] ≡ ⏏ (Γ ,[ A ])


Dull-Ctx = Dull
Restr-Ctx = Restr
⏏-Ctx = ⏏

infixl 40 _,[_]
-- infixl 60 ⟨_⦙_

⏏-Type : Γ ⊢Typeₛ -> Γ ⊢Type

data _⇛_ where
  id : ∀{Γ : Ctx L} -> Γ ⇛ Γ
  π₁ : ∀{Γ Δ : Ctx L} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ

Dull-⇛ : (Γ ⇛ Δ) -> Dull Γ ⇛ Dull Δ
Dull-⇛ = {!!}


ι-subst-Ctx : ∀{A : Γ ⊢Type} {v} {x : Restr Γ v ⊢ Restr-Type A v} -> Γ ⇛ (Γ [ v ≔ x ])
ι-subst-Ctx = {!!}

-- σ-subst-Ctx : ∀{A : Γ ⊢Type} {x : Γ ⊢ A} {v} -> (Γ [ v ≔ x ]) ⇛ Γ
-- σ-subst-Ctx = {!!}

wk : ∀{Γ : Ctx L} {A : Γ ⊢Type} -> (Γ ,[ A ] ⇛ Γ)
wk = π₁ id

data _⊢Typeₛ where
  -- gen : (ϕ : K ⇌ L) -> ⟨ ϕ ⦙ Γ ⊢Type -> Γ ⊢Type
  D⁻ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Typeₛ
  D⁺ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Typeₛ
  ⨇ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Typeₛ) -> Γ ⊢Typeₛ
  ⨈ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Typeₛ) -> Γ ⊢Typeₛ
  NN : ∀{Γ : Ctx (◌ , τ)} -> Γ ⊢Typeₛ
  End : ∀{Γ : Ctx (◌ , τ)} -> Γ ⊢Typeₛ
  Fam : Γ ⊢ ⏏-Type NN -> Γ ⊢Typeₛ

  -_ : Γ ⊢Typeₛ -> Γ ⊢Typeₛ

data _⊢Type where
  ⏏ : Γ ⊢Typeₛ -> Γ ⊢Type
  _[_] : Δ ⊢Type -> Γ ⇛ Δ -> Γ ⊢Type

  Dull : ∀{Γ : Ctx (+- , τ)} -> Γ ⊢Type -> Dull Γ ⊢Type
  RestrT : {Γ : Ctx L} -> ∀(X : Γ ⊢Type) -> (v : Γ ⊢Var X) -> Restr Γ v ⊢Type

⏏-Type = ⏏
Dull-Type = Dull
Restr-Type = RestrT

Dull-Var : {A : Dull Γ ⊢Type} -> Γ ⊢Var ⏏ (D⁻ A) -> Dull Γ ⊢Var A
Dull-Var = {!!}

postulate
  σ-Dull-Restr : {Γ : Ctx (+- , τ)} -> {A : Dull Γ ⊢Type} -> {v : Γ ⊢Var ⏏ (D⁻ A)} -> Dull (Restr Γ v) ≡ Restr-Ctx (Dull Γ) (Dull-Var v)

{-# REWRITE σ-Dull-Restr #-}

postulate
  subst-D⁺ : ∀{σ : Δ ⇛ Γ} {A : Dull Γ ⊢Type} -> ⏏ (D⁺ A) [ σ ] ≡ ⏏ (D⁺ (A [ Dull-⇛ σ ]))
  subst-D⁻ : ∀{σ : Δ ⇛ Γ} {A : Dull Γ ⊢Type} -> ⏏ (D⁻ A) [ σ ] ≡ ⏏ (D⁻ (A [ Dull-⇛ σ ]))
  subst-NN : ∀{σ : Δ ⇛ Γ} -> ⏏ NN [ σ ] ≡ ⏏ NN
  subst-End : ∀{σ : Δ ⇛ Γ} -> ⏏ End [ σ ] ≡ ⏏ End

  β-Dull-D⁻ : ∀{Γ : Ctx (+- , τ)} -> ∀{A : Dull Γ ⊢Type} -> Dull {Γ = Γ} (⏏ (D⁻ A)) ≡ A

  β-Restr-D⁻ : ∀{Γ : Ctx (+- , τ)} -> ∀{A : Dull Γ ⊢Type} -> ∀{v : Γ ⊢Var ⏏ (D⁻ A)} -> RestrT (⏏ (D⁻ A)) v ≡ ⏏ (D⁻ (Restr-Type A (Dull-Var v)))


{-# REWRITE subst-D⁺ subst-D⁻ subst-NN subst-End #-}
{-# REWRITE β-Dull-D⁻ #-}
{-# REWRITE β-Restr-D⁻ #-}





-- wk-Type : ∀{Γ : Ctx K} {A} -> Γ ⊢Type -> Γ ,[ A ] ⊢Type
-- wk-Type x = {!!}


-- inj : {X : Γ ⊢Type} -> {v : Γ ⊢Var X} -> ∀{x} -> Γ [ v ≔ x ] ⊢Type -> Γ ⊢Type
-- inj = {!!}



data _⊢TypeOp where
  Id : Γ ⊢TypeOp
  Inv : Γ ⊢TypeOp


-- pattern _⦙_⟩ A ϕ = gen ϕ A

-- infixr 60 _⦙_⟩

-- Id ↷ T = T
-- Inv ↷ T = - T

data _⊢Var_ where
  zero : ∀{A} -> Γ ,[ A ] ⊢Var (A [ wk ])
  suc : ∀{A B} -> Γ ⊢Var A -> Γ ,[ B ] ⊢Var (A [ wk ])

  -- Dull-Var : ∀{A : Dull Γ ⊢Type} -> Γ ⊢Var ⏏ (D⁻ A) -> Dull Γ ⊢Var A
-- Dull-Var v = {!!}


data _⊢_ where
  var : ∀{A} -> Γ ⊢Var A -> Γ ⊢ A
  -- γ_,_ : ∀(ϕ : K ⇌ L) {A}
  --     -> ⟨ ϕ ⦙ Γ ⊢ A
  --     -> Γ ⊢ A ⦙ ϕ ⟩
  Λ_ : ∀{X A} -> Γ ,[ X ] ⊢ ⏏ A -> Γ ⊢ ⏏ (⨇ X A)
  -- _,_ : ∀{A B} -> Γ ⊢ A -> Γ ,[ A ] ⊢ B -> Γ ⊢ ⨈ A B
  inv : ∀{X} -> Γ ⊢ ⏏ (D⁺ X) -> Γ ⊢ ⏏ (D⁻ X)
  -- [_≔_]_ : ∀{τ Γ} {X : Dull {τ = τ} Γ ⊢Type} -> (v : Γ ⊢Var ⏏ (D⁻ X)) -> (x : Γ ⊢ ⏏ (D⁺ X)) -> ∀{Y}
  --   -> (Γ [ v ≔ inv x ]) ⊢ Y
  --   -> Γ ⊢ (Y [ ι-subst-Ctx ])
  _[_]t : ∀{Γ Δ : Ctx L} -> ∀{A : Γ ⊢Type} -> Γ ⊢ A -> (σ : Δ ⇛ Γ) -> Δ ⊢ (A [ σ ])
  end : Γ ⊢ ⏏ (D⁺ (⏏ End))
  n0 : Γ ⊢ ⏏ NN

  -- WARNING: this is probably wrong because
  -- this means that we can use all negative
  -- things in Γ
  d⁺ : ∀{A} -> Dull Γ ⊢ A -> Γ ⊢ ⏏ (D⁺ A)

---------------------------------------------
-- rewriting for single substitution
postulate
  ssubst-zero : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A} {x : Restr (Γ ,[ A ]) zero ⊢ RestrT (A [ wk ]) zero} -> (Γ ,[ A ]) [ zero ≔ x ] ≡ Γ --  & A wit x
  -- ssubst-zero-End : ∀{τ}{Γ : Ctx (◌ , τ)} -> {x : Restr (Γ ,[ ⏏ End ]) zero ⊢ RestrT (⏏ End) zero} -> (Γ ,[ ⏏ End ]) [ zero ≔ x ] ≡ Γ
  -- ssubst-suc : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A B v} {x : Γ ⊢ B} -> (Γ ,[ A ]) [ suc v ≔ x [ wk ]t ] ≡ (Γ [ v ≔ x ]) ,[ A [ σ-subst-Ctx ] ]

{-# REWRITE ssubst-zero #-}
-- {-# REWRITE ssubst-zero ssubst-suc #-}
--
---------------------------------------------

-- {-# REWRITE subst-D⁺ #-}

---------------------------------------------
-- Special rewriting rules involving terms

postulate
  subst-Fam : ∀{σ : Δ ⇛ Γ} {x : Γ ⊢ ⏏ NN} -> ⏏ (Fam x) [ σ ] ≡ ⏏ (Fam (x [ σ ]t))

--
---------------------------------------------

module Examples where
  ε : Ctx (+- , 𝟙)
  ε = ⏏ []

  -- F1 : ε ⊢ ⏏ (⨇ (⏏ (D⁺ (⏏ NN))) (⨇ (⏏ (D⁻ (⏏ NN))) (D⁺ (⏏ End))))
  -- F1 = Λ (Λ ([ zero ≔ var (suc zero) ] end) )

  -- T1 : (ε ,[ ⏏ (D⁻ (⏏ NN)) ]) [ zero ≔ inv (d⁺ n0) ] ≡ ε
  -- T1 = {!refl-≡!}

  -- F2 : ε ⊢ ⏏ (⨇ (⏏ (D⁻ (⏏ NN))) (⨇ (⏏ (D⁺ (⏏ (Fam (var zero))))) (D⁺ (⏏ (Fam (n0))))))
  -- F2 = Λ (Λ ([ suc zero ≔ d⁺ n0 ] {!var zero!}) )

  -- Λ (Λ ([ zero ≔ var (suc zero) ] end))




