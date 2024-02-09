{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2023-12-05.Rules where

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

{-
data isBase : Γ ⊢Type U -> Γ ⊢Space U -> 𝒰₀

-- data SpaceCtx where
--   [] : SpaceCtx
--   _,[_≤_] : ∀ Γ U -> Γ ⊢Space U -> SpaceCtx

data Ctx where
  [] : Ctx
  _,[_↞_] : ∀ (Γ : Ctx) -> ∀ (U : Γ ⊢Subspace) -> (A : Γ ⊢Type U) -> Ctx -- {{_ : isBase A X}} -> 

data _⊢Space_ where
  𝒮 : (U : Γ ⊢Subspace) -> Γ ⊢Space U
  -- Paths : Γ ⊢Subspace -> (V : Γ ⊢Subspace) -> Γ ⊢Space V

data _⊢Subspace where
  var : Γ ⊢Pt -> Γ ⊢Subspace

data _⊢Subspace_⊆_ where

data _⊢Type_ where
  Nat : ∀{i} -> Γ ⊢Type var i
  Flat : Γ ⊢Space U -> Γ ⊢Type U
  Point : ∀ U -> Γ ⊢Type U

  Paths : (U V : Γ ⊢Subspace) -> Γ ⊢Type V

  -- we also want to embed covers as types, since we need cover maps (in order to restrict types on covers...)
  -- or we use the path space for that

  Restr : ∀{U V} -> Γ ⊢Subspace U ⊆ V -> Γ ⊢Type V -> Γ ⊢Type U -- given a cover U, we can take a cover V, and look at a cover of the paths from U to V and give a corresponding type on V

data isBase where
  -- Flat : ∀{Γ} -> (X : Γ ⊢Space U) -> isBase {Γ = Γ} (Flat X) X -- TODO: link U with X, that is, the cover U should be the actual cover of X on the context...

-- data Ctx where
--   [] : Ctx
--   _,[_∶_] : (Γ : Ctx) -> Name -> ∀{X U} -> Γ ⊢Type X ≥ U -> Ctx
--   -- _↑ : Γ ⊢Ctx -> ∀{i S} -> (Γ ,[ i ∶ S ]) ⊢Ctx

infixr 25 _,[_∶_]

data _⊢_ where

{-
-}

{-
data _⊢Space where

  -- constructors
  ∅ : Γ ⊢Space
  sp : ∀{U} -> Γ ⊢Type X ≥ U -> Γ ⊢Space -- actually should be the whole cover
  _×_ : (X Y : Γ ⊢Space) -> Γ ⊢Space
  _⨿_ : (X Y : Γ ⊢Space) -> Γ ⊢Space
  𝒮 : ∀ X -> Γ ⊢Subspace X -> Γ ⊢Space

  -- normalizable
  Base : Γ ⊢Space -> Γ ⊢Space
  Paths : (x : Γ ⊢Pt X) -> Γ ⊢Space

  weak : Γ ⊢Space -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Space

  -- NOTES: We have to define functions between spaces which preserve
  --        the subspace / cover relation.


data _⊢Subspace_ where
  ∅ : Γ ⊢Subspace X
  var : Γ ⊢Pt X -> Γ ⊢Subspace X
  ⟮_⟯ : Γ ⊢Subspace X -> Γ ⊢Subspace X
  -- -- _⋎_ : Γ ⊢Subspace -> Γ ⊢Subspace -> Γ ⊢Subspace
  ∂ : Γ ⊢Subspace X -> Γ ⊢Subspace X
  int : Γ ⊢Subspace X -> Γ ⊢Subspace X


  -- normalizable
  ℧ : Γ ⊢Subspace X
  weak : Γ ⊢Subspace X -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Subspace weak X

data _⊢Type_≥_ where

  weak : (A : Γ ⊢Type X ≥ U) -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Type weak X ≥ weak U

  -- constructors
  Nat : ∀{i} -> Γ ⊢Type X ≥ var i
  Type : ∀{i} -> Γ ⊢Type X ≥ var i
  Point : ∀{i} -> Γ ⊢Space -> Γ ⊢Type X ≥ var i

  yo : (X : Γ ⊢Space) -> ∀{U} -> Γ ⊢Type X ≥ U
  _⇒_ : ∀{X U} -> (A B : Γ ⊢Type X ≥ U) -> Γ ⊢Type X ≥ U

  Paths : (U : Γ ⊢Subspace X) -> Γ ⊢Type X ≥ ⟮ U ⟯

  Restr : Γ ⊢Type X ≥ U -> (x : Γ ⊢Pt X) -> Γ ⊢Type X ≥ var x


  Fill : ∀{U} -> (Ts : Γ ⊢Type X ≥ ∂ U) -- the boundaries
              -> (T0 : Γ ⊢Type X ≥ int U) -- only the top
              -- here we want to require, (for every point `p : int U`),
              -- for every element x : T0 (which is at a certain point of `int U`),
              -- for every point `q : int (∂ U)`, for every path (p ⇝ q) in the space X,
              -- a value of Ts @ q
              -> Γ ,[ 0 ∶ T0 ] ⊢ Restr (weak Ts) {!!}


              -- -> (∀{i} -> (p : i ∈-Node j) -> Γ ⨾ Γ ,[ fresh Γ ∶ T0 ] ⊢ wk-Type (Ts p) ↓ {!!})
              -> Γ ⊢Type X ≥ U

  -- destructors
  _at_ : (X : Γ ⊢Space) -> (U : Γ ⊢Subspace Base X) -> Γ ⊢Type Base X ≥ U

data _⊢_ where
  

module Example where
  Pt : [] ⊢Space
  Pt = 𝒮 ∅ ∅

  Line : [] ⊢Space
  Line = 𝒮 (Pt ⨿ Pt) ℧


-- Question: what is the base space of the universe? => maybe there is no universe space?
-- But it can be created?


{-
--------------------------------------------------------------------
-- Plan: we need two contexts: one for shapes, one for types!
--
-- Reason: types exist sometimes in a role-restricted context,
-- i.e., to build this type, only variables existing at some
-- role are allowed. In order to restrict a context in the _⊢Type_
-- signature, we need to speak about roles here. This is only
-- possible if we don't define them as types of kind 𝑆.
--
-- Additionally: every type in the type context has a role at which it
-- lives, while a role does not have such an annotation...
--


data Shapes : 𝒰₀

private variable
  Γ : Shapes
data _⊢Shape : Shapes -> 𝒰₀
data _⊢NodeVar : Shapes -> 𝒰₀
data _⊢Subspace : Shapes -> 𝒰₀
data _⊢NodeVars : Shapes -> 𝒰₀


-- new types

-- abstract set
-- data ⊢Set : 𝒰₀ where
--   _×_ : ⊢Set -> ⊢Set -> ⊢Set
--   _＋_ : ⊢Set -> ⊢Set -> ⊢Set
--   ∅ : ⊢Set
--   𝟙 : ⊢Set

data Spaces : 𝒰₀

private variable
  Τ : Spaces

data _⊢Space : Spaces -> 𝒰₀



data _⊢Point_ : ∀ Τ -> Τ ⊢Space -> 𝒰₀
data _⊢Points_ : ∀ Τ -> Τ ⊢Space -> 𝒰₀

private variable
  X Y : Τ ⊢Space


-- data _<-NodeVar_ : (a b : Γ ⊢NodeVar) -> 𝒰₀
-- data _≤-Node_ : (a b : Γ ⊢Node) -> 𝒰₀
-- data ⊢_isNode : (Γ : Shapes) -> (i : Fin ∣ Γ ∣) -> 𝒰₀

data _⊢_∈-Node_ : ∀ Γ -> (a b : Γ ⊢NodeVar) -> 𝒰₀

data _⊆-Cover_ : (U V : Γ ⊢Subspace) -> 𝒰₀

data _⊢Ctx : Shapes -> 𝒰₀

data _⊢Subspace_⇾_ : ∀ Γ -> (U V : Γ ⊢Subspace) -> 𝒰₀


private variable
  Γ : Γ ⊢Ctx

fresh : Γ ⊢Ctx -> Name
fresh = {!!}

-- record RCtx : 𝒰₀ where
--   inductive
--   constructor _at_
--   field fst : Ctx
--   field snd : Γ ⊢Node

-- data _⊢Shapes : (Γ : Ctx) -> 𝒰₀
-- data _⊢Kind : (Γ : Ctx) -> 𝒰₀
data _⨾_⊢Type_ : ∀ Γ -> Γ ⊢Ctx -> Γ ⊢Subspace -> 𝒰₀
-- data _⊢Type : (Γ : Ctx) -> 𝒰₀
-- data _⊢Var!_ : (Γ : Ctx) ->  -> 𝒰₀
data _⨾_⊢_↓_ : ∀ Γ Γ -> ∀{i j} -> Γ ⨾ Γ ⊢Type j -> Γ ⊢Subspace i ⇾ j -> 𝒰₀
-- data _⊇_ : (Γ : Ctx) (Δ : Ctx) -> 𝒰₀

-- infixl 40 _⊇_


data _⊢NodeVars where
  [] : Γ ⊢NodeVars
  _&_ : Γ ⊢NodeVars -> Γ ⊢NodeVar -> Γ ⊢NodeVars

infixl 30 _&_


--------------------------------------------------------------------
-- New variant

data Spaces where
  [] : Spaces




-- -- selecting points inside a space to create a new space
data _⊢Points_ where
  [] : Τ ⊢Points X
  _&_ : Τ ⊢Points X -> Τ ⊢Point X -> Τ ⊢Points X


data _⊢Space where
  -- The empty space
  ∅ : Τ ⊢Space

  -- The singleton space
  𝟙 : Τ ⊢Space

  -- we select points in a single space and create a new space with more points
  𝒮 : ∀ X -> Τ ⊢Points X -> Τ ⊢Space

  _＋_ : Τ ⊢Space -> Τ ⊢Space -> Τ ⊢Space


infixl 30 _＋_

data _⊢Point_ where
  ∞ : {ps : Τ ⊢Points X} -> Τ ⊢Point 𝒮 X ps
  near : {ps : Τ ⊢Points X} -> Τ ⊢Point X -> Τ ⊢Point 𝒮 X ps

  left : Τ ⊢Point X -> Τ ⊢Point (X ＋ Y)
  right : Τ ⊢Point Y -> Τ ⊢Point (X ＋ Y)

  tt : Τ ⊢Point 𝟙



--------------------------------------------------------------------

data _⊢Shape where
  -- we select points in a single space and create a new space with more points
  𝒮 : Γ ⊢NodeVars -> Γ ⊢Shape

data Shapes where
  [] : Shapes
  _,[_∶_] : (Γ : Shapes) -> Name -> Γ ⊢Shape -> Shapes

data _⊢NodeVar where
  zero : ∀{x S} -> Γ ,[ x ∶ S ] ⊢NodeVar
  suc : ∀{x S} -> Γ ⊢NodeVar -> Γ ,[ x ∶ S ] ⊢NodeVar

-- data _⊢Node where
--   var : Γ ⊢NodeVar -> Γ ⊢Node
--   ∅ : Γ ⊢Node
--   ⩝_∶_,_ : ∀(x : Name) -> (S : Γ ⊢Shape) -> Γ ,[ x ∶ S ] ⊢Node -> Γ ⊢Node

data _⊢Subspace where
  var : Γ ⊢NodeVar -> Γ ⊢Subspace
  ⟮_⟯ : Γ ⊢Subspace -> Γ ⊢Subspace
  -- _⋎_ : Γ ⊢Subspace -> Γ ⊢Subspace -> Γ ⊢Subspace
  ∂ : Γ ⊢Subspace -> Γ ⊢Subspace
  int : Γ ⊢Subspace -> Γ ⊢Subspace

data _⊢_∈-NodeVars_ : ∀ Γ -> Γ ⊢NodeVar -> Γ ⊢NodeVars -> 𝒰₀ where
  take : ∀{vs v} -> Γ ⊢ v ∈-NodeVars vs & v
  step : ∀{vs v w} -> Γ ⊢ w ∈-NodeVars vs -> Γ ⊢ w ∈-NodeVars (vs & v)

data _⊢_∈-Node_ where
  incl : ∀{Vs} -> ∀{x : Name} -> {i : Γ ⊢NodeVar} -> Γ ⊢ i ∈-NodeVars Vs -> (Γ ,[ x ∶ 𝒮 Vs ]) ⊢ (suc i) ∈-Node zero
  step : ∀{x S i j} -> Γ ⊢ i ∈-Node j -> Γ ,[ x ∶ S ] ⊢ suc i ∈-Node suc j
  -- refl-≤-Node : ∀{a : Γ ⊢Node} -> a ≤-Node a

data _⊆-Cover_ where

data _⊢Subspace_⇾_ where

-- data _<-NodeVar_ where
--   -- base : 

-- data _≤-Node_ where
--   refl-≤-Node : ∀{a : Γ ⊢Node} -> a ≤-Node a

data _⊢Ctx where
  [] : Γ ⊢Ctx
  _,[_∶_] : (Γ : Γ ⊢Ctx) -> Name -> ∀ {i} -> Γ ⨾ Γ ⊢Type i -> Γ ⊢Ctx
  _↑ : Γ ⊢Ctx -> ∀{i S} -> (Γ ,[ i ∶ S ]) ⊢Ctx

infixl 50 _,[_∶_]

data _⨾_⊢Type_ where
  wk-Type : ∀{U V x} -> {X : Γ ⨾ Γ ⊢Type V} -> Γ ⨾ Γ ⊢Type U -> Γ ⨾ Γ ,[ x ∶ X ] ⊢Type U
  Universe : ∀{i} -> Γ ⨾ Γ ⊢Type var i
  FinType : ∀{i} -> List String -> Γ ⨾ Γ ⊢Type var i
  ∂ : ∀{j} -> Γ ⨾ Γ ⊢Type j -> Γ ⨾ Γ ⊢Type (∂ j)
  Space : (U : Γ ⊢Subspace) -> Γ ⨾ Γ ⊢Type ⟮ U ⟯
  Fill : ∀{j} -> (Ts : Γ ⨾ Γ ⊢Type ∂ j)
              -> (T0 : Γ ⨾ Γ ⊢Type int j)
              -- -> (∀{i} -> (p : i ∈-Node j) -> Γ ⨾ Γ ,[ fresh Γ ∶ T0 ] ⊢ wk-Type (Ts p) ↓ {!!})
              -> Γ ⨾ Γ ⊢Type j
  -- Fill : ∀{j} -> (Ts : ∀{i} -> Γ ⊢ i ∈-Node j -> Γ ⨾ Γ ⊢Type ⟮ i ⟯)
  --             -> (T0 : Γ ⨾ Γ ⊢Type only j)
  --             -- -> (∀{i} -> (p : i ∈-Node j) -> Γ ⨾ Γ ,[ fresh Γ ∶ T0 ] ⊢ wk-Type (Ts p) ↓ {!!})
  --             -> Γ ⨾ Γ ⊢Type ⟮ j ⟯
  Rt : ∀{U V} -> U ⊆-Cover V -> Γ ⨾ Γ ⊢Type V -> Γ ⨾ Γ ⊢Type U

data _⨾_⊢_↓_ where


module Example where
  Pt : Γ ⊢Shape
  Pt = 𝒮 []

  △₂ : Shapes
  △₂ = [] ,[ 0 ∶ Pt ] ,[ 1 ∶ 𝒮 ([] & zero)]

  -- Nat₀ : △₂ ⨾ [] ⊢Type ⟮ suc zero ⟯
  -- Nat₀ = Fill (λ { (step (incl ()))}) (FinType ("1" ∷ "ℕ" ∷ []))

  -- Nat₁ : △₂ ⨾ [] ⊢Type ⟮ zero ⟯
  -- Nat₁ = Fill (λ { (incl take) → Nat₀}) (FinType ("zero" ∷ "suc" ∷ []))

-- module Examples2 where
--   Pt : [] ⊢Space
--   Pt = 𝟙

--   Line : [] ⊢Space
--   Line = 𝒮 (Pt ＋ Pt) ([] & left tt & right tt)




{-
  ⩝_∶_,_ :  (x : Name) -> (S : Γ ⊢Shape)
         -> ∀{i} -> Γ ,[ x ∶ S ] ⨾ Γ ↑ at i ⊢Type
         -> Γ ⨾ Γ at (⩝ x ∶ S , i) ⊢Type

  ⨇[_≤_][_∶_]_ : (a p : Γ ⊢Node) -> {{_ : a ≤-Node p}}
                -> (x : Name) -> (A : Γ ⨾ Γ at a ⊢Type)
                -> Γ ⨾ (Γ ,[ x at a ∶ A ]) at p ⊢Type
                -> Γ ⨾ Γ at p ⊢Type


pattern ⨇[_≤_by_][_∶_]_ a b x y z W = ⨇[_≤_][_∶_]_ a b {{x}} y z W
-- pattern ⨇[ a ≤ b by x ][ y ∶ z ] W = ⨇[_≤_][_∶_]_ a b {{x}} y z W

  -- var : ∀{Γ i k} -> Γ ⊢ i isKind k -> Γ ⊢Type k
  -- Shape : [] ⊢Type
  -- 𝒮 : ∀{Γ} -> Γ ⊢Shapes -> Γ ⊢Type 𝑆
  -- 𝟘 : ∀{Γ} -> Γ ⊢Type 𝑆
  -- Unit : ∀{Γ} -> Γ ⊢Type 𝑇
  -- ⩝_∶_,_ : ∀{Γ} -> (x : Name) -> (S : Γ ⊢Type 𝑆) -> ∀{k} -> Γ ,[ x ∶ S ] ⊢Type k -> Γ ⊢Type (⩝ x ∶ S , k)



_⇒_ : ∀{a b x}
      -> (A : Γ ⨾ Γ at (var a) ⊢Type)
      -> (B : Γ ⨾ Γ at (var b) ⊢Type)
      -> Γ ,[ x ∶ 𝒮 ([] & a & b) ] ⨾ Γ ↑ at var zero ⊢Type
_⇒_ {a = a} {b} {x} A B = ⨇[ var (suc a) ≤ var zero by {!!} ][ 9 ∶ {!!} ] {!!}

-- _⇒_ : ∀{a b x}
--       -> (A : Γ ⨾ Γ at (var a) ⊢Type)
--       -> (B : Γ ⨾ Γ at (var b) ⊢Type)
--       -> Γ ⨾ Γ at (⩝ x ∶ 𝒮 ([] & a & b) , var zero) ⊢Type
-- _⇒_ {a = a} {b} {x} A B = ⩝ _ ∶ 𝒮 _ , {!⨇[ a ≤ zero by ? ][ ? ∶ ? ] ?!}
-- ⨇[ a ≤ p by ? ][ ? ∶ ? ] ?

module Example where
  Pt : Γ ⊢Shape
  Pt = 𝒮 []

  NN : [] ,[ 0 ∶ Pt ] ⨾ [] at {!!} ⊢Type
  NN = {!!}

  NN2 : [] ⨾ [] at ⩝ 0 ∶ Pt , ⩝ 1 ∶ 𝒮 ([] & zero) , var zero ⊢Type
  NN2 = ⩝ 0 ∶ Pt , (⩝ 1 ∶ _ , {!⨇[ ? ≤ ? ][ ? ∶ ? ] ?!} )



{-

-- data _⊢Kind where
--   𝑆 : ∀{Γ} -> Γ ⊢Kind
--   𝑇 : ∀{Γ} -> Γ ⊢Shapes -> Γ ⊢Kind
--   ⩝_∶_,_ : ∀{Γ} -> ∀ x -> {k : Γ ⊢Kind} -> (A : Γ ⊢Type k) -> Γ ,[ x ∶ A ] ⊢Kind -> Γ ⊢Kind
--   weak : ∀{Γ} -> ∀ {x} -> {k : Γ ⊢Kind} -> {A : Γ ⊢Type k} -> Γ ⊢Kind -> Γ ,[ x ∶ A ] ⊢Kind


len-Ctx : Ctx -> ℕ
len-Ctx [] = 0
len-Ctx (Γ ,[ x atr i ∶ x₁ ]) = suc (len-Ctx)

instance
  Notation-Absolute-Ctx : Notation-Absolute (Ctx) ℕ
  Notation-Absolute-Ctx = record { ∣_∣ = len-Ctx }

-- data _⊢_isShape : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Set where
--   zero : ∀{Γ x} -> {A : Γ ⊢Type 𝑆} -> Γ ,[ x ∶ A ] ⊢ zero isShape
--   suc : ∀{Γ x k i₀} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isShape) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isShape

-- data _⊢_isKind_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (k : Γ ⊢Kind) -> Set where
--   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind weak k
--   suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isKind j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isKind (weak j)

-- data _⊢_isName_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (x : Name) -> Set where
--   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isName x
--   suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isName j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isName j



{-
data _⊢Shapes where
  [] : ∀{Γ} -> Γ ⊢Shapes
  -- _&_ : ∀{Γ} -> Γ ⊢Shapes -> ∀ i -> {{_ : Γ ⊢ i isKind 𝑆}} -> Γ ⊢Shapes
  _&_ : ∀{Γ i} -> Γ ⊢Shapes -> Γ ⊢ i isKind 𝑆 -> Γ ⊢Shapes

  -- _&_ : ∀{Γ Δ Ε} -- -> {{_ : Γ ⊇ Δ}}
  --       -> Δ ⊢Shapes
  --       -> {A : Ε ⊢Type 𝑆}
  --       -> {x : Name}
  --       -> ∀ i -> {{z : Γ ⊢ i isType A}}
  --       -> {{_ : Γ ⊢ i isName x}}
  --       -- -> {{X : Γ ⊇ (x ∶! A)}}
  --       -- -> let instance _ = to-⊇-⊢Type-Var it it
  --       --    in {{_ : Γ ↤ Δ ∪ (x ∶! A)}}
  --          -- in {{_ : Γ ↤ Δ ∪ (_ ∶! A)}}
  --       -- -> {{_ : Γ ↤ Δ ∪ Ε}}
        -- -> Γ ⊢Shapes

infixl 40 _&_

data _⊢_ where
  -- ℧ : ∀{Γ} -> Γ ⊢ 
  -- 𝒮 : ∀


{-


{-
record _⊢Type_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
  inductive
  pattern
  constructor _⊩_
  field ctx : Ctx
  field {{jni}} : Γ ⊇ ctx
  field typ : ctx ⊢Type k

infixl 50 _⊩_

open _⊢Type_ public

instance
  hasNotation-!:⊢Type : ∀{Γ k} -> hasNotation-! (Γ ⊢Type k) (λ x -> x .ctx ⊢Type k)
  hasNotation-!:⊢Type = record { _! = λ a → a .typ }




data _⊇_ where
  empty : [] ⊇ []
  take : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ ,[ x ∶ Ε ⊩ A ]
  skip : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ

isTop-⊇-[] : ∀{Γ} -> Γ ⊇ []
isTop-⊇-[] {[]} = empty
isTop-⊇-[] {Γ ,[ x ∶ Ε ⊩ A ]} = skip {{isTop-⊇-[]}} {{it}}

id-⊇ : ∀{Γ} -> Γ ⊇ Γ
id-⊇ {[]} = empty
id-⊇ {Γ ,[ x ∶ Ε ⊩ A ]} = take {{id-⊇}} {{it}}


pattern _⊩⁺_ Ε A = _⊩_ Ε {{skip}} A

-- module isKindInstances where
--   instance
--     isKind:zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind k
--     isKind:zero = _⊢_isKind_.zero

--     isKind:suc : ∀{Γ x k i j} -> {A : Γ ⊢Type k} -> {{_ : Γ ⊢ i isKind j}} -> Γ ,[ x ∶ A ] ⊢ suc i isKind j
--     isKind:suc = suc

module _ where
  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> Γ ⊢Type k -> Set where
  --   zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType (_⊩⁺_ Ε A)
  --   suc : ∀{Γ Ε Η x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (Ε ⊩ A))
  --               -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType (Ε ⊩⁺ A)

  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> ∀{Ε} -> Ε ⊢Type k -> Set where
  --   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isType typ A
  --   suc : ∀{Γ Ε x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (A))
  --               -> {B : Γ ⊢Type j} -> Γ ,[ x ∶ B ] ⊢ (suc i) isType (A)

  data _⊢_isType_ : (Γ : Ctx) -> ∀{k} -> (i : Fin ∣ Γ ∣) -> ∀{Ε} -> Ε ⊢Type k -> Set where
    zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType A
    suc : ∀{Γ Ε Η x k j i} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (A))
                -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType A


module _ where
  private instance
    _ = isTop-⊇-[]
    _ = id-⊇
  data _↤_∪_ : (Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> 𝒰₀ where
    emptyleft : ∀{Γ} -> Γ ↤ Γ ∪ []
    emptyright : ∀{Γ} -> Γ ↤ [] ∪ Γ
    takeleft : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) Ε {{take}} {{skip}}
    takeright : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) Δ (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{skip}} {{take}}
    takeboth : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{take}} {{take}}

-- record WithVar {Ε k} (A : Ε ⊢Type k) : 𝒰₀ where
--   field name : Name

--   private instance _ = id-⊇

--   getCtxWithVar : Ctx
--   getCtxWithVar = Ε ,[ name ∶ Ε ⊩ A ]

-- open WithVar public

-- instance
--   Notation-Absolute-WithVar : ∀{Ε k} -> {A : Ε ⊢Type k} -> Notation-Absolute (WithVar A) Ctx
--   Notation-Absolute-WithVar = record { ∣_∣ = getCtxWithVar }


_∶!_ : ∀ x -> ∀ {Ε k} (A : Ε ⊢Type k) -> Ctx
_∶!_ x {Ε} A = Ε ,[ x ∶ Ε ⊩ A ]
  where instance _ = id-⊇

-- mergeType : ∀{Γ k} -> (A : Γ ⊢Type k) -> Ctx
-- mergeType (Ε ⊩ A) = (_ ∶! A)

record _⊢Var_∶_ {k} (Γ : Ctx) (i : Fin ∣ Γ ∣) {Ε : Ctx} (A : Ε ⊢Type k) : Set where
  constructor var_by_and_
  inductive
  pattern
  field name : Name
  field isType:var : Γ ⊢ i isType A
  field isName:var : Γ ⊢ i isName name

open _⊢Var_∶_ public

to-⊇-⊢Type : ∀{Γ i k Ε} -> {A : Ε ⊢Type k} -> Γ ⊢ i isType A -> Γ ⊇ Ε
to-⊇-⊢Type zero = skip
to-⊇-⊢Type (suc x) = skip {{to-⊇-⊢Type x}}

module _ where
  instance _ = id-⊇
  to-⊇-⊢Type-Var : ∀{Γ i k x Ε} -> {A : Ε ⊢Type k} -> Γ ⊢ i isType A -> Γ ⊢ i isName x -> Γ ⊇ (Ε ,[ x ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var zero zero = take
  to-⊇-⊢Type-Var (suc x) (suc y) = skip {{to-⊇-⊢Type-Var x y}}

  to-⊇-⊢Type-Var2 : ∀{Γ i k Ε} -> {A : Ε ⊢Type k} -> (z : Γ ⊢Var i ∶ A) -> Γ ⊇ (Ε ,[ name z ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var2 (var name₁ by P1 and P2) = to-⊇-⊢Type-Var P1 P2



--------------------------------------------------------------------

wk₀-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
wk₀-⊢Type (Ε ⊩ B) = _⊩_ Ε {{skip }} B

-}
-}
-}
-}
-}
-}
-}
-}
