-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2023-12-05.RulesFiniteSpaces where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiTheory.Dev.2023-12-05.Core

Name = ℕ



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
