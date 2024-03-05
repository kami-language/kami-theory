-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2023-11-27.Rules where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiTheory.Dev.2023-11-27.Core

Name = ℕ


-- a context contains both types, but is also the "base space"
-- for spaces, though we keep this implicit

-- data TypeCtx : 𝒰₀
data Ctx : 𝒰₀

private variable
  Γ : Ctx


data _⊢Cover : Ctx -> 𝒰₀

private variable U V : Γ ⊢Cover

-- this property should be decidable and propositional
data _⊢Cover_⊆_ : ∀ Γ -> (U V : Γ ⊢Cover) -> 𝒰₀

data _⊢Space_ : ∀ Γ -> Γ ⊢Cover -> 𝒰₀

-- TODO: unclear
data _⊢Pt : Ctx -> 𝒰₀

private variable X : Γ ⊢Space U

data _⊢Type_ : ∀ (Γ : Ctx) -> (X : Γ ⊢Cover) -> 𝒰₀

data _⊢_ : ∀ (Γ : Ctx) -> ∀{U} -> Γ ⊢Type U -> 𝒰₀

-- base : Γ ⊢Type U -> Γ ⊢Space
-- base = {!!}

data isBase : Γ ⊢Type U -> Γ ⊢Space U -> 𝒰₀

-- data SpaceCtx where
--   [] : SpaceCtx
--   _,[_≤_] : ∀ Γ U -> Γ ⊢Space U -> SpaceCtx

data Ctx where
  [] : Ctx
  _,[_↞_] : ∀ (Γ : Ctx) -> ∀ (U : Γ ⊢Cover) -> (A : Γ ⊢Type U) -> Ctx -- {{_ : isBase A X}} -> 

data _⊢Space_ where
  𝒮 : (U : Γ ⊢Cover) -> Γ ⊢Space U
  -- Paths : Γ ⊢Cover -> (V : Γ ⊢Cover) -> Γ ⊢Space V

data _⊢Cover where
  var : Γ ⊢Pt -> Γ ⊢Cover

data _⊢Cover_⊆_ where

data _⊢Type_ where
  Nat : ∀{i} -> Γ ⊢Type var i
  Flat : Γ ⊢Space U -> Γ ⊢Type U
  Point : ∀ U -> Γ ⊢Type U

  Paths : (U V : Γ ⊢Cover) -> Γ ⊢Type V

  -- we also want to embed covers as types, since we need cover maps (in order to restrict types on covers...)
  -- or we use the path space for that

  Restr : ∀{U V} -> Γ ⊢Cover U ⊆ V -> Γ ⊢Type V -> Γ ⊢Type U -- given a cover U, we can take a cover V, and look at a cover of the paths from U to V and give a corresponding type on V

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
  𝒮 : ∀ X -> Γ ⊢Cover X -> Γ ⊢Space

  -- normalizable
  Base : Γ ⊢Space -> Γ ⊢Space
  Paths : (x : Γ ⊢Pt X) -> Γ ⊢Space

  weak : Γ ⊢Space -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Space

  -- NOTES: We have to define functions between spaces which preserve
  --        the subspace / cover relation.


data _⊢Cover_ where
  ∅ : Γ ⊢Cover X
  var : Γ ⊢Pt X -> Γ ⊢Cover X
  ⟮_⟯ : Γ ⊢Cover X -> Γ ⊢Cover X
  -- -- _⋎_ : Γ ⊢Cover -> Γ ⊢Cover -> Γ ⊢Cover
  ∂ : Γ ⊢Cover X -> Γ ⊢Cover X
  int : Γ ⊢Cover X -> Γ ⊢Cover X


  -- normalizable
  ℧ : Γ ⊢Cover X
  weak : Γ ⊢Cover X -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Cover weak X

data _⊢Type_≥_ where

  weak : (A : Γ ⊢Type X ≥ U) -> ∀{x Y V} -> {B : Γ ⊢Type Y ≥ V} -> Γ ,[ x ∶ B ] ⊢Type weak X ≥ weak U

  -- constructors
  Nat : ∀{i} -> Γ ⊢Type X ≥ var i
  Type : ∀{i} -> Γ ⊢Type X ≥ var i
  Point : ∀{i} -> Γ ⊢Space -> Γ ⊢Type X ≥ var i

  yo : (X : Γ ⊢Space) -> ∀{U} -> Γ ⊢Type X ≥ U
  _⇒_ : ∀{X U} -> (A B : Γ ⊢Type X ≥ U) -> Γ ⊢Type X ≥ U

  Paths : (U : Γ ⊢Cover X) -> Γ ⊢Type X ≥ ⟮ U ⟯

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
  _at_ : (X : Γ ⊢Space) -> (U : Γ ⊢Cover Base X) -> Γ ⊢Type Base X ≥ U

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
data _⊢Cover : Shapes -> 𝒰₀
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

data _⊆-Cover_ : (U V : Γ ⊢Cover) -> 𝒰₀

data _⊢Ctx : Shapes -> 𝒰₀

data _⊢Cover_⇾_ : ∀ Γ -> (U V : Γ ⊢Cover) -> 𝒰₀


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
data _⨾_⊢Type_ : ∀ Γ -> Γ ⊢Ctx -> Γ ⊢Cover -> 𝒰₀
-- data _⊢Type : (Γ : Ctx) -> 𝒰₀
-- data _⊢Var!_ : (Γ : Ctx) ->  -> 𝒰₀
data _⨾_⊢_↓_ : ∀ Γ Γ -> ∀{i j} -> Γ ⨾ Γ ⊢Type j -> Γ ⊢Cover i ⇾ j -> 𝒰₀
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

data _⊢Cover where
  var : Γ ⊢NodeVar -> Γ ⊢Cover
  ⟮_⟯ : Γ ⊢Cover -> Γ ⊢Cover
  -- _⋎_ : Γ ⊢Cover -> Γ ⊢Cover -> Γ ⊢Cover
  ∂ : Γ ⊢Cover -> Γ ⊢Cover
  int : Γ ⊢Cover -> Γ ⊢Cover

data _⊢_∈-NodeVars_ : ∀ Γ -> Γ ⊢NodeVar -> Γ ⊢NodeVars -> 𝒰₀ where
  take : ∀{vs v} -> Γ ⊢ v ∈-NodeVars vs & v
  step : ∀{vs v w} -> Γ ⊢ w ∈-NodeVars vs -> Γ ⊢ w ∈-NodeVars (vs & v)

data _⊢_∈-Node_ where
  incl : ∀{Vs} -> ∀{x : Name} -> {i : Γ ⊢NodeVar} -> Γ ⊢ i ∈-NodeVars Vs -> (Γ ,[ x ∶ 𝒮 Vs ]) ⊢ (suc i) ∈-Node zero
  step : ∀{x S i j} -> Γ ⊢ i ∈-Node j -> Γ ,[ x ∶ S ] ⊢ suc i ∈-Node suc j
  -- refl-≤-Node : ∀{a : Γ ⊢Node} -> a ≤-Node a

data _⊆-Cover_ where

data _⊢Cover_⇾_ where

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
  Space : (U : Γ ⊢Cover) -> Γ ⨾ Γ ⊢Type ⟮ U ⟯
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
