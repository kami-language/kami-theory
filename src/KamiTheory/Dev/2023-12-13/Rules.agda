{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2023-12-13.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiTheory.Dev.2023-12-05.Core

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
data Ctx : Layer -> 𝒰₀

private variable
  Γ Δ : Ctx L

data _⇛_ : Ctx L -> Ctx L -> 𝒰₀

data _⊢Type : ∀ (Γ : Ctx L) -> 𝒰₀
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

_↷_ : Γ ⊢TypeOp -> Γ ⊢Type -> Γ ⊢Type



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

data Ctx where
  [] : Ctx L

  -- this should actually also contain the fragmentation
  -- assignment
  _,[_] : ∀ (Γ : Ctx L) -> Γ ⊢Type -> Ctx L

  -- ⟨_⦙_ : K ⇌ L -> Ctx L -> Ctx K

  _[_≔_] : ∀(Γ : Ctx (+- , τ)) {X} -> Γ ⊢Var X -> Γ ⊢ X -> Ctx (+- , τ)

  Dull : Ctx (+- , τ) -> Ctx (◌ , τ)

  --------------
  -- Normalizable
  -- wkT : ∀ T -> Ctx Σ Τ -> Ctx Σ (Τ , T)
  -- _⟨_⟩ : Ctx Σ Τ -> Τ ⊢T -> Ctx Σ Τ


infixl 40 _,[_]
-- infixl 60 ⟨_⦙_


data _⊢Type where
  -- gen : (ϕ : K ⇌ L) -> ⟨ ϕ ⦙ Γ ⊢Type -> Γ ⊢Type
  D⁻ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Type
  D⁺ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Type
  -_ : Γ ⊢Type -> Γ ⊢Type
  ⨇ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  ⨈ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  NN : ∀{Γ : Ctx (◌ , τ)} -> Γ ⊢Type
  End : ∀{Γ : Ctx (◌ , τ)} -> Γ ⊢Type

wk-Type : ∀{Γ : Ctx K} {A} -> Γ ⊢Type -> Γ ,[ A ] ⊢Type
wk-Type x = {!!}


inj : {X : Γ ⊢Type} -> {v : Γ ⊢Var X} -> ∀{x} -> Γ [ v ≔ x ] ⊢Type -> Γ ⊢Type
inj = {!!}



data _⊢TypeOp where
  Id : Γ ⊢TypeOp
  Inv : Γ ⊢TypeOp


-- pattern _⦙_⟩ A ϕ = gen ϕ A

-- infixr 60 _⦙_⟩

Id ↷ T = T
Inv ↷ T = - T

data _⊢Var_ where
  zero : ∀{A} -> Γ ,[ A ] ⊢Var wk-Type A
  suc : ∀{A B} -> Γ ⊢Var A -> Γ ,[ B ] ⊢Var wk-Type A

data _⊢_ where
  var : ∀{A} -> Γ ⊢Var A -> Γ ⊢ A
  -- γ_,_ : ∀(ϕ : K ⇌ L) {A}
  --     -> ⟨ ϕ ⦙ Γ ⊢ A
  --     -> Γ ⊢ A ⦙ ϕ ⟩
  Λ_ : ∀{X A} -> Γ ,[ X ] ⊢ A -> Γ ⊢ ⨇ X A
  _,_ : ∀{A B} -> Γ ⊢ A -> Γ ,[ A ] ⊢ B -> Γ ⊢ ⨈ A B
  inv : ∀{X} -> Γ ⊢ D⁺ X -> Γ ⊢ D⁻ X
  [_≔_]_ : ∀{Γ} {X : Dull Γ ⊢Type} -> (v : Γ ⊢Var D⁻ X) -> (x : Γ ⊢ D⁺ X ) -> ∀{Y} -> (Γ [ v ≔ inv x ]) ⊢ Y -> Γ ⊢ inj Y
  end : Γ ⊢ D⁺ End

-- module Examples where
--   F1 : [] ⊢ ⨇ (D⁺ NN) (⨇ (D⁻ NN) (D⁺ End))
--   F1 = Λ (Λ ([ zero ≔ var (suc zero) ] end))






{-



---------------------------------------------
-- spaces

data Space where
  [] : Space
  _,Fill_ : (Σ : Space) -> Σ ⊢Subspace -> Space

data _⊢Pt where
  top : (Σ ,Fill U) ⊢Pt

data _⊢Subspace where
  pt : Σ ⊢Pt -> Σ ⊢Subspace
  ∅ : Σ ⊢Subspace

data _⊢Ln_⇾_ where

---------------------------------------------
-- times
data Time where
  [] : Time
  _,_ : (Τ : Time) -> Τ ⊢TExt -> Time
  -- I⃗ : Time
  -- _,[_<_by_] : (Τ : Time) -> (s t : Τ ⊢T) -> Τ ⊢T s < t -> Time

data _⊢T where
  z : ∀{X} -> Τ ⊢T X -> Τ , X ⊢T
  s : ∀{X} -> Τ ⊢T -> Τ , X ⊢T

data _⊢TExt where
  I⃗ : Τ ⊢TExt
  _&_ : {Τ : Time} -> (X : Τ ⊢TExt) -> {s t : Τ ⊢T X} -> Τ ⊢ s <T t -> Τ ⊢TExt

data _⊢T_ where
  zero : Τ ⊢T I⃗
  one : Τ ⊢T I⃗
  weak : {X : Τ ⊢TExt} -> ∀{s t} -> {p : Τ ⊢ s <T t} -> Τ ⊢T X -> Τ ⊢T (X & p)
  split : {X : Τ ⊢TExt} -> ∀{s t} -> {p : Τ ⊢ s <T t} -> Τ ⊢T (X & p)

data _⊢_<T_ where
  arr : Τ ⊢ zero <T one







data _⊢Type_ where


  -- this should be different, probably this is
  -- actually the closure operation which takes
  -- a somewhat complete term and closes it over
  pt : Γ ⊢PtType x -> Γ ⊢Type pt x

-- data _⊢VType_,_ where
--   End : Γ ⊢PtType x -> Γ ⊢VType x , n
--   [_]▶_ : (A : Γ ⊢PtType x)
--             -> Γ ,[ pt x , n ⇜ pt A ] ⊢VType x , suc n
--             -> Γ ⊢VType x , n

-- infixl 40 [_]▶_

data _⊢PtType_ where
  -- sum/product
  ⨇ : (A : Γ ⊢PtType x) -> Γ ,[ pt x ⇜ pt A ] ⊢PtType x -> Γ ⊢PtType x

  -- we can restrict a type to a value at a time
  _⟨_⟩ : {Γ : Ctx Σ Τ} -> Γ ⊢PtType x -> Τ ⊢T -> Γ ⊢PtType x

  -- we can filter a type to contain only the positive parts
  -- ⁺_ : Γ ⊢PtType x -> Γ ⊢PtType x

  _⦗_⦘ : {Γ : Ctx Σ Τ} -> Γ ⊢PtBase x -> Param Σ Τ -> Γ ⊢PtType x


data _⊢PtBase_ where
  -- natural numbers
  Bℕ : Γ ⊢PtBase x

  -- time quantification
  B∀_,_ : ∀ T -> wkT T Γ ⊢PtType x -> Γ ⊢PtBase x

pattern ℕ⁺ x = Bℕ ⦗ ⁺ , x ⦘
pattern ℕ⁻ x = Bℕ ⦗ ⁻ , x ⦘
pattern ∀⁺⦗_⦘[_]_ t x y = (B∀ x , y) ⦗ ⁺ , t ⦘

pattern t₀ x = z x
pattern t₁ x = s (z x)
pattern t₂ x = s (s (z x))

-- pattern Nat⁺ x = Nat (⁺ , x)

data _⊢LnType_ where

data _⊢Pt_ where
  -- abs : ⟨ Γ ⟩ t ⊢ 
  -- introducing new vars
  -- Λ : ∀{x A B}
  --     -> Γ ,[ pt x , n ⇜ pt A ] ⊢V B
  --     -> Γ ⊢V [ A ]▶ B

  -- discharging negative vars in the context
  -- we take a path to a var in the context,
  -- and change the context to have a value for that var
  -- Ψ : 


module Example where
  Σ₁ : Space
  Σ₁ = [] ,Fill ∅

  Τ₁ : Time
  Τ₁ = [] , I⃗

  fun : ∀{Γ : Ctx Σ₁ Τ₁} -> Γ ⊢PtType top
  fun = ∀⁺⦗ t₀ zero ⦘[ I⃗ ] ⨇ (ℕ⁻ (t₁ zero)) (ℕ⁺ (t₁ one))

  f1 : [] ⊢Pt fun
  f1 = {!!}



{-
-- for spaces, though we keep this implicit

-- data TypeCtx : 𝒰₀
data Ctx : 𝒰₀

private variable
  Γ Δ : Ctx

data _⇛_ : Ctx -> Ctx -> 𝒰₀

data _⊢Subspace : Ctx -> 𝒰₀
data _⊢Var : Ctx -> 𝒰₀
data _⊢Point : Ctx -> 𝒰₀

private variable U V : Γ ⊢Subspace

data _⊢Subspace_⇝_ : ∀ Γ -> Γ ⊢Subspace -> Γ ⊢Subspace -> 𝒰₀
data _⊢Subspace_∼_ : ∀ Γ -> Γ ⊢Subspace -> Γ ⊢Subspace -> 𝒰₀

data _⊢_⊆_ : ∀ Γ -> (U V : Γ ⊢Subspace) -> 𝒰₀

-- this property should be decidable and propositional
-- data _⊢Subspace_⊆_ : ∀ Γ -> (U V : Γ ⊢Subspace) -> 𝒰₀


-- this might be both:
-- either a space extension or a space cover
-- data _⊢Space_ : ∀ Γ -> Γ ⊢Subspace -> 𝒰₀
data _⊢Projected_ : ∀ Γ -> Γ ⊢Subspace -> 𝒰₀
-- data _⊢Extended : ∀ Γ -> 𝒰₀

data _⊢Projected_⇝_ : ∀ Γ {U V} -> Γ ⊢Projected U -> Γ ⊢Projected V -> 𝒰₀
data _⊢Projected_∼_ : ∀ Γ {U V} -> Γ ⊢Projected U -> Γ ⊢Projected V -> 𝒰₀


private variable
  X : Γ ⊢Projected U
  Y : Γ ⊢Projected V

data _⊢Point_ : ∀ Γ {U} -> Γ ⊢Projected U -> 𝒰₀
data _⊢Subspace_ : ∀ Γ {U} -> Γ ⊢Projected U -> 𝒰₀

private variable
  S : Γ ⊢Subspace X
  T : Γ ⊢Subspace Y

data _⊢Section_ : ∀ Γ {U} -> Γ ⊢Projected U -> 𝒰₀
-- data _⊢Closed_ : ∀ Γ {U} -> Γ ⊢Projected U -> 𝒰₀

-- TODO: unclear
-- data _⊢Pt : Ctx -> 𝒰₀

-- private variable X : Γ ⊢Space U

-- data _⊢Type_ : ∀ (Γ : Ctx) -> (X : Γ ⊢Subspace) -> 𝒰₀

-- A universe over a subspace U of a context
-- means that this universe can only be used
-- for sums which are at least over this subspace (?)
--
-- A universe has an attached partitioning scheme
data _⊢Universe_ : ∀ (Γ : Ctx) -> (X : Γ ⊢Subspace) -> 𝒰₀

data Ctx where
  [] : Ctx
  _,[_↞_] : ∀ Γ -> ∀ U -> Γ ⊢Projected U -> Ctx
  -- _&_ : ∀ Γ -> Γ ⊢Extended -> Ctx

-- infixl 30 _&_

infixl 40 _,[_↞_]

data _⇛_ where
  π₀ : Γ ⇛ Δ ,[ U ↞ X ] -> Γ ⇛ Δ

  id : Γ ⇛ Γ

data _⊢Var where
  zero : Γ ,[ U ↞ X ] ⊢Var
  -- ezero : ∀ {Γ X} -> Γ & X ⊢Var
  suc : Γ ⊢Var -> Γ ,[ U ↞ X ] ⊢Var
  -- ∞ : Γ ⊢Var

data _⊢Point where
  ∞ : Γ ⊢Point

-- a subspace of the context 
data _⊢Subspace where
  -- ∞ : Γ ⊢Subspace

  -- a variable contains exactly the subspace which it was created with
  var : Γ ⊢Var -> Γ ⊢Subspace

  pt : Γ ⊢Point -> Γ ⊢Subspace
  ∅ : Γ ⊢Subspace

  -- interiour
  °_ : Γ ⊢Subspace -> Γ ⊢Subspace

  -- boundary
  ∂_ : (x : Γ ⊢Subspace) -> Γ ⊢Subspace

  -- closure
  ⟮_⟯ : Γ ⊢Subspace -> Γ ⊢Subspace

  _∪_ : Γ ⊢Subspace -> Γ ⊢Subspace -> Γ ⊢Subspace

  -- the subspace U extended by exactly the points of X which get added in (Γ , X)
  _◁_ : (U : Γ ⊢Subspace) -> (X : Γ ⊢Projected U) -> Γ ,[ U ↞ X ] ⊢Subspace

  -- The embedded subspace of X as added in Γ
  Emb : (X : Γ ⊢Projected U) -> Γ ,[ U ↞ X ] ⊢Subspace

  --pullback of subspaces
  _[_] : Γ ⊢Subspace -> Δ ⇛ Γ -> Δ ⊢Subspace

  -- not normal forms
  -- weak : ∀{X : Γ ⊢Projected U} -> Γ ⊢Subspace -> Γ ,[ U ↞ X ] ⊢Subspace

infixl 100 _[_]
infixl 50 _∪_
infixl 150 °_ ∂_

data _⊢_⊆_ where
  inj-° : Γ ⊢ ° U ⊆ U

-- data _⊢Extended where
--   -- the one point compactification
--   _* : ∀ (U : Γ ⊢Subspace) -> Γ ⊢Extended

--   -- sum for extensions
--   ∫ : (X : Γ ⊢Extended) -> Γ & X ⊢Extended -> Γ ⊢Extended


data _⊢Projected_ where
  -- the flat modality (discretization of space)
  _♭ : ∀ U -> Γ ⊢Projected U

  -- sum (and compactification ?)
  ∫ : (X : Γ ⊢Projected U) -> Γ ,[ U ↞ X ] ⊢Projected (Emb X) -> Γ ⊢Projected U

  -- product
  -- ∮ : (X : Γ ⊢Projected U) -> Γ ,[ U ↞ X ] ⊢Projected var zero -> Γ ⊢Projected U

  -- sum over a subspace U
  _⊕'_ : (X Y : Γ ⊢Projected U) -> Γ ⊢Projected U
  -- ∐


  Univ : ∀{x} -> Γ ⊢Projected var x

  ---- Not normal

  -- restriction along inclusion
  _⇂[_by_] : Γ ⊢Projected V -> ∀ U -> Γ ⊢ U ⊆ V -> Γ ⊢Projected U

  -- computes as restriction
  °_ : Γ ⊢Projected U -> Γ ⊢Projected ° U

  -- extension of section to closure of space
  -- computes by using the restriction maps and ⋀-ing the resulting subspaces
  Sub : (X : Γ ⊢Projected U) -> Γ ⊢Section X -> Γ ⊢Projected ⟮ U ⟯


  -- the identity projected space over U
  -- this is probably not normal
  Id : Γ ⊢Projected U

  -- the empty space over any subspace U
  ⊥ : Γ ⊢Projected U


  -- pullback of projected spaces
  _[_] : (X : Δ ⊢Projected U) -> (σ : Γ ⇛ Δ) -> Γ ⊢Projected U [ σ ]

  ---- Experimental
  -- converting an extension space to a projected space over ∞
  -- [_by_]* : ∀ (U : Γ ⊢Subspace) -> (Γ ⊢ U ⊆ ∂ ⟮ pt ∞ ⟯) -> Γ ⊢Projected (pt ∞)

  -- the new extension type (this only works over a pt since we need somewhere to
  -- project the new point to)
  _∠_ : (X : Γ ⊢Projected U) -> (V : Γ ⊢Subspace X) -> Γ ⊢Projected U

  _⟨_⟩ᵣ : Γ ⊢Projected U -> Γ ⊢Subspace U ∼ V -> Γ ⊢Projected V


infixl 30 _⇂[_by_]
infixl 40 _∠_
infixl 50 _⟨_⟩ᵣ

data _⊢Projected_⇝_ where

data _⊢Projected_∼_ where
  subspace : (X : Γ ⊢Projected U) -> (α : Γ ⊢Subspace U ∼ V) -> Γ ⊢Projected X ∼ X ⟨ α ⟩ᵣ

data _⊢Point_ where
  base : Γ ⊢Point X -> Γ ⊢Point (X ∠ S)
  ext : Γ ⊢Point (X ∠ S)


data _⊢Subspace_ where
  pt : Γ ⊢Point X -> Γ ⊢Subspace X
  _∨_ : (S T : Γ ⊢Subspace X) -> Γ ⊢Subspace X
  ∅ : Γ ⊢Subspace X

-- data _⊢Closed_ where
  -- zero : Γ ,[ U ↞ X ] ⊢Closed {!!}

_⇂° : Γ ⊢Projected U -> Γ ⊢Projected ° U
_⇂° {U = U} X = X ⇂[ ° U by {!!} ]

infixl 200 _⇂°


data _⊢Section_ where
  -- π₁ : (σ : Γ ⇛ Δ ,[ U ↞ X ]) -> Γ ⊢Section (X [ π₀ σ ])

  -- a section can be constructed by splitting the source space into interiour and boundary
  split : ∀{U} -> {X : Γ ⊢Projected U}
          -> (s : Γ ⊢Section X ⇂°)
          -> Γ ⊢Section Sub _ s
          -> Γ ⊢Section X

  _↦_ : ∀ a -> {X : Γ ⊢Projected pt a} -> Γ ⊢Point X -> Γ ⊢Section X

  _⟨_⟩ᵣ : {X : Γ ⊢Projected U} -> {Y : Γ ⊢Projected V}
        -> Γ ⊢Section X -> Γ ⊢Projected X ∼ Y -> Γ ⊢Section Y



-- wk-⇛ : Γ ,[ U ↞ X ] ⇛ Γ
-- wk-⇛ = π₀ id

-- vz : Γ ,[ U ↞ X ] ⊢Section X [ wk-⇛ ]
-- vz = π₁ id

-- vs : (Γ ⊢Section Y) -> (Γ ,[ U ↞ X ] ⊢Section Y [ wk-⇛ ])
-- vs = {!!}

data _⊢Universe_ where
  𝕌 : Γ ⊢Universe ∅










module Example where

  Tri : Γ ⊢Projected pt ∞
  Tri = ⊥ ∠ ∅ ∠ ∅ ∠ (pt (base ext) ∨ pt ext)

  Bi : ∀ U -> Γ ⊢Projected U
  Bi _ = ⊥ ∠ ∅ ∠ pt ext

  ff : [] ,[ pt ∞ ↞ Tri ] ⊢Section Bi (var zero)
  ff = split (({!!} ↦ {!!}) ⟨ {!!} ⟩ᵣ) {!!}

  -- the subspace created from a closed subset (a term / a section)
  -- Lift : {X : Γ ⊢Projected U} -> Γ ⊢Section X -> Γ ⊢Projected U
  -- Lift {X} s = {!!}

  -- Id : Γ ⊢Projected U
  -- Id = ∫ {!!} {!!}

  -- Tri : [] ⊢Projected (var ∞)
  -- Tri = ∫ Id (Id ⊕' Id)

  -- Bi : [] ⊢Projected _
  -- Bi = ∫ ([ ∅ by {!!} ]*) ({![ ? by ? ]*!})

  -- Tri : [] ⊢Projected (var ∞)
  -- Tri = Ex $ ∫ (∅ *) (∫ (∅ *) (var ezero ∪ var {!suc ?!} *))


  -- example: map Tri to Bi

  -- Poly : (L : Γ ⊢Projected var ∞) -> Γ ⊢Section ∮ {!!} Univ
  -- Poly = {!!}


-- data _⊢_ : ∀ (Γ : Ctx) -> ∀{U} -> Γ ⊢Type U -> 𝒰₀

-- base : Γ ⊢Type U -> Γ ⊢Space
-- base = {!!}
-}
-}
