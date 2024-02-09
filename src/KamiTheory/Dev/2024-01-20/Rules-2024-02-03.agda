
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2024-01-20.Rules-2024-02-03 where

open import Agora.Conventions hiding (Σ ; Lift ; k)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_ ; _≰_)
open import Relation.Nullary.Decidable.Core

open import KamiTheory.Dev.2024-01-20.Core hiding (_＠_)
open import KamiTheory.Dev.2024-01-20.UniqueSortedList hiding (img)
open import KamiTheory.Dev.2024-01-20.Space
open import KamiTheory.Dev.2024-01-20.Sheaf
open import KamiTheory.Dev.2024-01-20.Open
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base

-- We have type contexts and normal contexts which additionally
-- contain location assignments.

---------------------------------------------
-- Base type layer

data BaseType : 𝒰₀ where
  BB NN : BaseType


---------------------------------------------
-- Normal type system layer
data Ctx : 𝒰₀

private variable
  Γ : Ctx

-- setup of kinds for types and spaces
data Kind : 𝒰₀ where
  type : Kind
  space : Kind

private variable
  k l : Kind

data _⊢Sort_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀

private variable
  S : Γ ⊢Sort k
  T : Γ ⊢Sort l

TypeSyntax : ∀ Γ -> 𝒰 _
TypeSyntax Γ = Γ ⊢Sort type

syntax TypeSyntax Γ = Γ ⊢Type

private variable
  A : Γ ⊢Type
  B : Γ ⊢Type


SpaceSyntax : ∀ Γ -> 𝒰 _
SpaceSyntax Γ = Γ ⊢Sort space

syntax SpaceSyntax Γ = Γ ⊢Space


private variable
  X : Γ ⊢Space
  Y : Γ ⊢Space
  Z : Γ ⊢Space

-- We have a notion of term/open set of a space
data _⊢Atom_ : ∀ Γ -> Γ ⊢Space -> 𝒰₀

instance
  hasStrictOrder:Atom : hasStrictOrder (Γ ⊢Atom X)
  hasStrictOrder:Atom = {!!}

_⊢Open'_ : ∀ Γ -> Γ ⊢Space -> 𝒰₀
_⊢Open'_ Γ X = (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Γ ⊢Atom X) since hasStrictOrder:Atom)))

macro
  _⊢Open_ : ∀ Γ -> Γ ⊢Space -> _
  _⊢Open_ Γ X = #structureOn (Γ ⊢Open' X)
-- _⊢Open'_ : ∀ Γ -> Γ ⊢Space -> Space
-- _⨾_⊢Open_ : ∀ Γ Σ -> Γ ⊢Space -> Space

private variable
  U : Γ ⊢Open X
  V : Γ ⊢Open Y

pure-Open : Γ ⊢Atom X -> Γ ⊢Open X
pure-Open u = ⦗ u ⦘ ∷ [] since (IB.[] IB.∷ IB.[])

bind-Open : Γ ⊢Open X -> (Γ ⊢Atom X -> Γ ⊢Open Y) -> Γ ⊢Open Y
bind-Open x f = bind-Space f x

-- app-Open : Γ ⊢Open (X ⇒i Y) -> Γ ⊢Open X -> Γ ⊢Open Y
-- app-Open F U = bind-Open F λ f -> bind-Open U λ u -> pure-Open (appi f u)

atom : Γ ⊢Atom X -> Γ ⊢Open X
atom u = pure-Open u


data _⊢Sheaf_ : ∀ Γ -> Γ ⊢Space -> 𝒰₀



data _⊢Var_ : ∀ Γ -> Γ ⊢Sort k -> 𝒰₀
data _⊢_ : ∀ Γ -> Γ ⊢Sort k -> 𝒰₀



private variable
  u : Γ ⊢ X
  v : Γ ⊢ Y

data Ctx where
  [] : Ctx
  _,[_] : ∀ (Γ : Ctx) -> (A : Γ ⊢Sort k) -> Ctx

infixl 30 _,[_]


--------------------------------------------------------------
-- Context setup

data _⊢Ctx₊ : Ctx -> 𝒰₂

_⋆-Ctx₊_ : ∀ (Γ : Ctx) -> Γ ⊢Ctx₊ -> Ctx

data _⊢Ctx₊ where
  [] : Γ ⊢Ctx₊
  _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Sort k -> Γ ⊢Ctx₊

-- _⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

-- assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≡ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

-- Δ ⋆-Ctx₊₂ [] = Δ
-- Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≡ (cong-≡ _⇂_⊢Type (sym-≡ assoc-⋆-Ctx₊)) x ]

Γ ⋆-Ctx₊ [] = Γ
Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

-- instance
--   hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx) (_⊢Ctx₊) (λ _ _ -> Ctx)
--   hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }


{-

assoc-⋆-Ctx₊ {E = []} = refl-≡
assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
  let p = sym-≡ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
  in J1 p _⊢Type _,[_] x

{-# REWRITE assoc-⋆-Ctx₊ #-}
-}



infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_


-- End Context setup
--------------------------------------------------------------


wk-Sort : Γ ⊢Sort k -> Γ ,[ S ] ⊢Sort k
su-Sort : (t : Γ ⊢ S) -> Γ ,[ S ] ⊢Sort k -> Γ ⊢Sort k




{-# NO_POSITIVITY_CHECK #-}
data _⊢Sort_ where

  --------------------------------------------------------------
  -- Spaces
  -- One : Γ ⊢Space
  -- ⨆ : (X : Γ ⊢Space) -> (Y : Γ ,[ X ]ₛ ⊢Space) -> Γ ⊢Space
  -- ⨅ : (X : Γ ⊢Space) -> (Y : Γ ,[ X ]ₛ ⊢Space) -> Γ ⊢Space

  -- _⊗_ : (AX : Γ ⊢TS) -> (Y : Γ ,[ AX ] ⊢Space) -> Γ ⊢Space
  -- _[_]⇒_ : (AX : Γ ⊢Space) -> (A : Γ ⊢Type) -> (BY : Γ ,[ A over X ] ⊢Space) -> Γ ⊢Space

  _⇒i_ : (X Y : Γ ⊢Space) -> Γ ⊢Space

  Free : (A : Γ ⊢Type) -> Γ ⊢Space

  Sub : ∀ X -> (U : Γ ⊢Open X) -> Γ ⊢Space


  -- Sub : (AX : Γ ⊢Space) -> (U : List ((List (Σ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a)) -> Γ ⊢Space


  --------------------------------------------------------------
  -- Types

  Base : BaseType -> Γ ⊢Type
  ⨆ : (A : Γ ⊢Type) -> (B : Γ ,[ A ] ⊢Type) -> Γ ⊢Type
  ⨅ : (S : Γ ⊢Type) -> (B : Γ ,[ S ] ⊢Type) -> Γ ⊢Type

  -- ⨇ : (X : Γ ⊢Space) -> (F : Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  Ap : (F : Γ ⊢Sheaf X) -> Γ ⊢ X -> Γ ⊢Type

  _⇒_ : (A : Γ ⊢Type) -> (B : Γ ⊢Type) -> Γ ⊢Type

  One : Γ ⊢Type
  -- Forget : (Y : Γ ⊢Space) -> (Γ ⊢Atom (Y ⇒i X)) -> Γ ⊢Type X

  -- Ap : Γ ⊢Sheaf X -> Γ ⊢Open X -> Γ ⊢Type

  -- Sh : Γ ⊢Space -> Γ ⊢Type

  Type : Γ ⊢Type

  Spc : Γ ⊢Type


  --------------------------------------------------------------
  -- Spaces 2

  spc : (A : Γ ⊢ Spc) -> Γ ⊢Space


infixr 40 _⇒_
infixr 50 _⊗_

data _⊢Sheaf_ where
  _＠_ : (A : Γ ⊢Type) -> (U : Γ ⊢ X) -> Γ ⊢Sheaf X
  -- Inh : Γ ⊢Open X -> Γ ⊢Type
  -- Yo : Γ ⊢ X -> Γ ⊢ X -> Γ ⊢Type
  _⊗_ : (F G : Γ ⊢Sheaf X) -> Γ ⊢Sheaf X

  Po : (Γ ⊢ (X ⇒i Y)) -> Γ ⊢Sheaf X -> Γ ⊢Sheaf Y
  _⇒i_ : (F G : Γ ⊢Sheaf X) -> Γ ⊢Sheaf X

private variable
  F : Γ ⊢Sheaf X
  G : Γ ⊢Sheaf Y



data _⊢Var_ where
  zero : Γ ,[ S ] ⊢Var wk-Sort S
  suc : Γ ⊢Var S -> Γ ,[ T ] ⊢Var wk-Sort S


data _⊢Atom_ where
  val : Γ ⊢ A -> Γ ⊢Atom Free A
  var : Γ ⊢Var X -> Γ ⊢Atom X
  sub : Γ ⊢Atom (Sub X U) -> Γ ⊢Atom X

data _⊢_≼_ : ∀ Γ {X : Γ ⊢Space} -> (u v : Γ ⊢ X) -> 𝒰₀


data _⊢_ where
  ---------------------------------------------
  -- Opens
  gen : Γ ⊢Open X -> Γ ⊢ X

  ---------------------------------------------
  -- Terms
  var : Γ ⊢Var S -> Γ ⊢ S

  b0 : Γ ⊢ Base BB
  b1 : Γ ⊢ Base BB
  n0 : Γ ⊢ Base NN

  -- ap : Γ ⊢Partial F ＠ U -> Γ ⊢ Ap F U
  -- sh : Γ ⊢Sheaf X -> Γ ⊢ Sh X

  lam : Γ ,[ S ] ⊢ B -> Γ ⊢ ⨅ S B
  lami : Γ ,[ A ] ⊢ wk-Sort B -> Γ ⊢ A ⇒ B
  app : Γ ⊢ ⨅ T S -> (t : Γ ⊢ T) -> Γ ⊢ su-Sort t S

  -- inh : U ≰ ⊥ -> Γ ⊢ Inh U

  rest : (F : Γ ⊢Sheaf X) -> {u v : Γ ⊢ X} -> (ϕ : Γ ⊢ u ≼ v) -> Γ ⊢ Ap F v -> Γ ⊢ Ap F u

  -- glue : (F : Γ ,[ X ] ⊢Type) -> (u v : Γ ⊢ X) -> Γ ⊢ su-Sort u F -> Γ ⊢ su-Sort v F
  -- full : Γ ,[ Sub X ⊤ ]ₛ ⊢ special-su-top (sub (var zero)) A -> Γ ,[ X ]ₛ ⊢ A

  -- glue : (F : Γ ⊢ ⨅ₛ X A) -> (U V : Γ ⊢Open X) -> (Γ ⊢ App F U) -> Γ ⊢ App F V 

  preimg : Γ ⊢ (X ⇒i Y) -> Γ ⊢ Y -> Γ ⊢ X
  img : Γ ⊢ (X ⇒i Y) -> Γ ⊢ X -> Γ ⊢ Y

  loc : (Γ ⊢ u ≼ v -> Γ ⊢ A) -> Γ ⊢ Ap (A ＠ u) v
  po : ∀{F : Γ ⊢Sheaf X} {f : Γ ⊢ (X ⇒i Y)} -> Γ ⊢ Ap F (preimg f u) -> Γ ⊢ Ap (Po f F) u
  po⁻¹ : ∀{F : Γ ⊢Sheaf X} {f : Γ ⊢ (X ⇒i Y)} -> Γ ⊢ Ap (Po f F) (img f u) -> Γ ⊢ Ap F u
  lams : ∀{F G : Γ ⊢Sheaf X} -> Γ ,[ Ap F u ] ⊢ wk-Sort (Ap G u) -> Γ ⊢ Ap (F ⇒i G) u


  type : Γ ⊢Type -> Γ ⊢ Type


data _⊢_≼_ where
  gen : ∀{u v : Γ ⊢Open X} (ϕ : u ≤ v) -> Γ ⊢ gen u ≼ gen v




  -- elim-BB : Γ ⊢ A -> Γ ⊢ A -> Γ ⊢ Base BB ⇒ wk-Sort A

  -- lam : (t : Γ ,[ A over One ] ⊢ B) -> Γ ⊢ A ⇒ B
  -- app : (f : Γ ⊢ A ⇒ B) -> (t : Γ ⊢ A) -> Γ ⊢ su-Sort t B

  -- forget : List ((List (Γ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a) -> Γ ⊢ Forget X


------------------------------------------------------------------------
-- Weakening


{-# TERMINATING #-}
wk-Ctx₊ : (E : Γ ⊢Ctx₊) -> Γ ,[ S ] ⊢Ctx₊

wk-Sort,ind : ∀ E -> (S : Γ ⋆-Ctx₊ E ⊢Sort k) -> Γ ,[ T ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Sort k
-- wk-Term-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢ AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ wk-Sort,ind E AX
-- wk-Var-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢Var AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Var wk-Sort,ind E AX

wk-Ctx₊ [] = []
wk-Ctx₊ (E ,[ x ]) = wk-Ctx₊ E ,[ wk-Sort,ind E x ]


wk-Sort,ind E (X ⇒i Y) = {!!}
wk-Sort,ind E (Free A) = Free (wk-Sort,ind E A)
wk-Sort,ind E (Sub X U) = Sub (wk-Sort,ind E X) {!!}
wk-Sort,ind E (spc A) = spc {!!}
wk-Sort,ind E (Base x) = Base x
wk-Sort,ind E (⨆ A B) = {!!}
wk-Sort,ind E (⨅ S B) = ⨅ (wk-Sort,ind E S) (wk-Sort,ind (E ,[ S ]) B)
wk-Sort,ind E (A ⇒ B) = wk-Sort,ind E A ⇒ wk-Sort,ind E B
wk-Sort,ind E One = One
wk-Sort,ind E Type = Type
wk-Sort,ind E Spc = Spc
wk-Sort,ind E (Ap F U) = {!!}

-- wk-Comm,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Comm ) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Comm 
-- wk-Comm,ind E (⟮ U ↝ V ⨾ ϕ ⟯[ A ] Z) = ⟮ U ↝ V ⨾ ϕ ⟯[ wk-Sort,ind E A ] wk-Comm,ind (E ,[ Fill _ _ ]) Z
-- wk-Comm,ind E End = End
-- wk-Comm,ind E (El-Comm x) = El-Comm (wk-Term-ind E x)

-- wk-Sort : Γ ⊢Sort k -> Γ ,[ A ] ⊢Sort k
wk-Sort AX = wk-Sort,ind [] AX -- [ wk-⇛♮ id-⇛♮ ]-Type

-- wk-≤-Local,ind E (Base b {ϕ = ϕ}) = Base b {ϕ = ϕ}
-- wk-≤-Local,ind E (Fam ϕ m n) = Fam ϕ (wk-Term-ind E m) (wk-Term-ind E n)


-- wk-Term : {AX : Γ ⊢Sort k} -> Γ ⊢ AX -> Γ ,[ A ] ⊢ wk-Sort AX
-- wk-Term t = ? -- wk-Term-ind [] t


-- wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

-- weakening over a whole context
wks-Sort : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Sort k) -> Γ ⋆-Ctx₊ E ⊢Sort k
wks-Sort [] A = A
wks-Sort (E ,[ x ]) A = wk-Sort (wks-Sort E A)

-- β-wk-Sort,ind,empty : ∀{A : Γ ,[ B ] ⊢Sort k} -> wk-Sort,ind [] A ≡ A
-- β-wk-Sort,ind,empty = ?



-- End weakening
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Substitution

su-Ctx₊ : (Γ ⊢ T) -> Γ ,[ T ] ⊢Ctx₊ -> Γ ⊢Ctx₊

su-Sort,ind : (t : Γ ⊢ T) -> ∀ E -> (S : Γ ,[ T ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
-- su-≤-Local,ind : {Γ : Ctx}{A : Γ ⊢Sort k} -> ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Local U} {BY : Γ ⋆-Ctx₊ E ⇂ V ⊢Local} -> .{ϕ : V ≤ U} -> _ ⇂ ϕ ⊢ AX ≤-Local BY -> _ ⇂ ϕ ⊢ su-Sort,ind {A = A} E AX ≤-Local su-Sort,ind E BY
-- su-Term-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢ AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢ su-Sort,ind E AX
-- su-Var-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢Var AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢Var su-Sort,ind E AX

su-Ctx₊ t [] = []
su-Ctx₊ t (E ,[ x ]) = su-Ctx₊ t E ,[ su-Sort,ind t _ x ]

su-Sort,ind t E (X ⇒i Y) = {!!}
su-Sort,ind t E (Free A) = Free (su-Sort,ind t E A)
su-Sort,ind t E (Sub X U) = {!!}
su-Sort,ind t E (spc A) = {!!}
su-Sort,ind t E (Base x) = Base x
su-Sort,ind t E (⨆ A B) = {!!}
su-Sort,ind t E (⨅ S B) = ⨅ (su-Sort,ind t E S) (su-Sort,ind t (E ,[ S ]) B)
su-Sort,ind t E (A ⇒ B) = su-Sort,ind t E A ⇒ su-Sort,ind t E B
su-Sort,ind t E One = One
su-Sort,ind t E Type = Type
su-Sort,ind t E Spc = Spc
su-Sort,ind t E (Ap F U) = {!!}


su-Sort t T = su-Sort,ind t [] T


-- su-Ctx₊ : (E : Γ ,[ A ] ⊢Ctx₊) -> (t : Γ ⊢ A) -> Γ ⊢Ctx₊

-- su₂-Type,ind : ∀ E -> {A : Γ ⊢Sort k} -> (t : Γ ⋆-Ctx₊ E ⊢ wks-Sort E A) -> (Z : Γ ,[ A ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
-- su₂-Type,ind E t Y = ?

special-su-top : Γ ,[ B ] ⊢ wk-Sort A ->  Γ ,[ A ] ⊢Sort k -> Γ ,[ B ] ⊢Sort k
special-su-top t T = su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)

-- End Substitution
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Equality

data _⊢_≡_ : ∀ Γ {A : Γ ⊢Type} -> (a b : Γ ⊢ A) -> 𝒰₀ where
  -- β-rest-lam : ∀{F : Γ ,[ X ] ,[ A ] ⊢Type} {u v} (ϕ : Γ ⊢ u ≼ v) -> (t : Γ ,[ su-Sort v A ] ⊢ su-Sort,ind v _ F) -> Γ ⊢ rest (⨅ A F) ϕ (lam t) ≡ lam {!!}


-- End Equality
------------------------------------------------------------------------



-- _⊢Partial_＠_ : ∀ Γ {X} -> (F : Γ ⊢Sheaf X) -> (U : Γ ⊢Open X) -> 𝒰₀
-- Γ ⊢Partial F ⊗ G ＠ U = (Γ ⊢Partial F ＠ U) × (Γ ⊢Partial G ＠ U)
-- Γ ⊢Partial A ＠ V ＠ U = Restr (Const (Γ ⊢ A)) V U

-- data _⊢Partial_＠_ : ∀ Γ {X} -> (F : Γ ⊢Sheaf X) -> (U : Γ ⊢Open X) -> 𝒰₀

-- data _⊢_≡_Partial : ∀ Γ {X} {U} -> {F : Γ ⊢Sheaf X} -> (t s : Γ ⊢Partial F ＠ U) -> 𝒰₀

-- {-# NO_POSITIVITY_CHECK #-}
-- data _⊢Partial_＠_ where
--   loc : Restr (Const (Γ ⊢ A)) U V -> Γ ⊢Partial (A ＠ U) ＠ V
--   _,_ : Γ ⊢Partial F ＠ U -> Γ ⊢Partial G ＠ U -> Γ ⊢Partial (F ⊗ G) ＠ U

--   _⇂_ : Γ ⊢Partial F ＠ U -> V ≤ U -> Γ ⊢Partial F ＠ V

--   glueP : {F : Γ ⊢Sheaf X} (t : Γ ⊢Partial F ＠ U) -> (s : Γ ⊢Partial F ＠ V) -> Γ ⊢ (t ⇂ π₀-∧) ≡ (s ⇂ π₁-∧) Partial
--           -> Γ ⊢Partial F ＠ (U ∨ V)

--   tm : Γ ⊢ Ap F U -> Γ ⊢Partial F ＠ U

-- ev-Sheaf : Γ ⊢Partial F ＠ U -> ⟨ sheaf Γ F ⟩ U
-- ev-Sheaf (loc x) = x
-- ev-Sheaf (t , u) = ev-Sheaf t , ev-Sheaf u
-- ev-Sheaf (t , u) = ev-Sheaf t , ev-Sheaf u

-- re-Sheaf : ⟨ sheaf Γ F ⟩ U -> Γ ⊢Partial F ＠ U
-- re-Sheaf {F = F ⊗ G} (t , u) = re-Sheaf t , re-Sheaf u
-- re-Sheaf {F = A ＠ U} t = loc t

-- _⇂ᵉᵛ_ : Γ ⊢Partial F ＠ U -> V ≤ U -> Γ ⊢Partial F ＠ V
-- _⇂ᵉᵛ_ {Γ = Γ} {F = F} t ϕ = re-Sheaf (_↷_ {{_}} {{of sheaf Γ F}} ϕ (ev-Sheaf t))

-- special-su-top : Γ ,[ X ]ₛ ⊢Atom wkₛ-Space Y ->  Γ ,[ Y ]ₛ ⊢Type -> Γ ,[ X ]ₛ ⊢Type
-- special-su-top t Y = {!!} -- su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)



instance
  hasStrictOrder:Term : hasStrictOrder (Γ ⊢ A)
  hasStrictOrder:Term = {!!}



-- su-Atom-Space : Γ ⊢ A -> Γ ⊢Atom X -> Γ ,[ A over X ] ⊢Space -> Γ ⊢Space
-- su-Atom-Space = {!!}

  -- -- app : Σ ⊢Atom X ⇒ BY -> (a : Γ ⊢ A) -> (x : Σ ⊢Atom X) -> Σ ⊢Atom su-Atom-Space a x BY
  -- appi : Γ ⊢Atom (X ⇒i Y) -> (x : Γ ⊢Atom X) -> Γ ⊢Atom Y

  -- compi : (f : Γ ⊢Atom (X ⇒i Y)) -> (g : Γ ⊢Atom (Y ⇒i Z)) -> Γ ⊢Atom (X ⇒i Z)
  -- lami : Γ ,[ A over X ] ⊢Atom BY -> Γ ⊢Atom (AX [ A ]⇒ BY)

  -- liftfree : Γ ⊢ A ⇒ wk-Sort B -> Σ ⊢Atom (Free A ⇒i Free B)

  -- free : Γ ,[ A over Free A ] ⊢ Forget AX -> Γ ,[ A over Free A ] ⊢Atom X


-- Σ ⊢Open' X = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Σ ⊢Atom X) since hasStrictOrder:Atom))


-- su-Space : Γ ⊢ A -> ⟨ Σ ⊢Open AX ⟩ -> Γ ,[ A ] ,[ AX ] ⊢Space -> Γ ⊢Space
-- su-Space t s One = {!!}
-- su-Space t s (BY ⊗ BY₁) = {!!}
-- su-Space t s (AX ⇒ BY) = {!!}
-- su-Space t s (AX ⇒i BY) = {!!}
-- su-Space t s (Free A) = {!!}
-- su-Space t s (Sub BY U) = Sub ({!!}) {!!}



-- We have an assignment of locations in a space to a type
-- data _⊢_⨞_ : (Γ : Ctx) -> (X : Γ ⊢Space) -> Γ ⊢Type X -> 𝒰₂ where

--   -- _,dep_ : (Γ ⊢ A ＠ AX) -> Γ ,[ A ] ,[ AX ] ⊢ B ＠ BY -> Γ ⊢ (A ⊗ B) ＠ (AX ⊗ BY)

--   _,_ : (Γ ⊢ X ⨞ A) -> (Γ ,[ X under A ] ⊢ Y ⨞ B) -> Γ ⊢ (X under A ⊗ Y) ⨞ ((X under A) ⊗ B)

--   loc : Γ ⊢Open X -> Γ ⊢ X ⨞ A


-- We can interpret a sheaf as a sheaf


-- pu-Sheaf : (Γ ⊢Atom (⨅ X Y)) -> Γ ⊢Sheaf X -> Γ ,[ X ]ₛ ⊢Sheaf Y
-- pu-Sheaf f (F ⊗ G) = pu-Sheaf f F ⊗ pu-Sheaf f G
-- pu-Sheaf f (A ＠ U) = {!!} ＠ {!!}

module Examples where

  uu : Γ ⊢Open Free (Base BB)
  uu = ⦗ val b0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])

  vv : Γ ⊢Open Free (Base BB)
  vv = ⦗ val b1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])


  -- T0 : [] ⊢ ⨅ (Free (Base BB)) Type
  -- T0 = lam (type (Inh (u ∧ atom (var zero)) ⇒ Base NN))

  T0 : [] ⊢Sheaf (Free (Base BB))
  T0 = Base NN ＠ gen uu

  -- T1 : [] ,[ Free (Base BB) ] ⊢Type
  -- T1 = Yo (gen u) (var zero) ⇒ Base NN

  t0 : [] ⊢ Ap T0 (gen (uu ∨ vv))
  t0 = loc λ a -> n0

  t1 : [] ⊢ Ap T0 (gen uu)
  t1 = rest T0 (gen ι₀-∨) t0

  t2 : [] ⊢ Ap ((Base NN ＠ gen uu) ⇒i ((Base NN ＠ gen uu) ⊗ (Base NN ＠ gen vv))) (gen (uu ∨ vv))
  t2 = {!!}

  -- T0 : [] ⊢Sheaf (Free (Base BB))
  -- T0 = (Base NN ＠ u) ⊗ (Base BB ＠ v)

  -- t0 : [] ⊢ Ap T0 u
  -- t0 = ap ((loc (λ x → n0)) , (loc (λ x → b0)))

  -- t1 : [] ⊢ Ap T0 v
  -- t1 = ap ((loc (λ x → n0)) , (loc (λ x → b0)))

  -- t2 : [] ⊢ Ap T0 (u ∨ v)
  -- t2 = ap (glueP {U = u} {V = v} (tm t0) ((tm t1)) {!!})

  -- t3 : [] ⊢ ⨅ₛ (Free (Base BB)) (Ap (Base NN ＠ (u ∧ v)) (atom (var zero)) ⇒ Ap (Base NN ＠ (u ∧ v)) ((atom (var zero))))
  -- t3 = lamₛ (lami (ap (tm (var zero))))



  -- t3 : [] ⊢ ⨅ Spc (⨅ (Sh (spc (var zero))) (Ap (shf (var zero)) ⊥))
  -- t3 = {!!}

  -- TN : [] ⊢Type
  -- TN = (Base NN over Free (Base BB)) ⊗ Base NN
  -- tn : [] ⊢ TN ＠ Free (Base BB)
  -- tn = loc u , loc (v ∧ u)




{-
data _⊢_∶_ : ∀ Γ {X} {A} -> (t : Γ ⊢ A) -> (l : Γ ⊢ X ⨞ A) -> 𝒰₂ where

-- also we can build a generic sheaf (it should be the same)
-- on open sets:
sheaf2 : Γ ⊢ X ⨞ A -> Sheaf (Γ ⊢Open' X) _
sheaf2 {Γ = Γ} F = (λ U -> ∑ λ t -> Γ ⊢ t ∶ F) since {!!}

-- Now we can compute the etale space E of that sheaf,
-- and the prime filters of E. They should be given by
-- prime filters of (Γ ⊢Open X) together with matching terms.
--
-- I can interpret 







--------------------------------------------------------------


-- We have A over X and want to restrict to A over a smaller BY
-- For that we need to give a map BY -> AX (or AX -> BY) which describes this
-- restriction

-- bind-Open : ⟨ Σ ⊢Open AX ⟩ -> 

-- map-loc2 : Γ ⊢ A ＠ AX -> Σ ⊢Atom (BY ⇒i AX) -> Γ ⊢ A ＠ BY
-- map-loc2 = {!!}

-- map-loc : Γ ⊢ A ＠ X -> Γ ⊢Atom (X ⇒i Y) -> Γ ⊢ A ＠ X
-- map-loc (L , M) f = map-loc L f , map-loc M f
-- map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)

-- su-Space : Γ ⊢ A -> Γ ⊢Open X -> Γ ,[ A over X ] ⊢Space -> Γ ⊢Space
-- su-Space = {!!}

wk-Space : Γ ⊢Space -> Γ ,[ X under A ] ⊢Space
wk-Space = {!!}

-- map-loc : Γ ⊢ A ＠ AX -> Σ ⊢Atom (AX ⇒i BY) -> Γ ⊢ A ＠ BY
-- map-loc (L , M) f = map-loc L f , map-loc M f
-- map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)


_⊢Sheaf_ : ∀ Γ X -> _
Γ ⊢Sheaf X = ∑ λ (A : Γ ⊢Type X) -> Γ ⊢ X ⨞ A

pu-Type : (Γ ⊢Atom (X ⇒i Y)) -> Γ ⊢Sheaf X -> Γ ⊢Sheaf Y
pu-Type f (.(_ under _ ⊗ _) , (F , F₁)) = {!? ⊗ ?!} , {!!}
pu-Type f (A , loc x) = {!!}
-- pu-Type f (Base x) = {!Base x!}
-- pu-Type f (X under A ⊗ T) = {!? ⊗ ?!} -- _ under (pu-Type f A) ⊗ {!!}
-- pu-Type f One = {!!}
-- pu-Type f (Forget X g) = Forget X (compi g f)

-- restr : Γ ⊢ X ⨞ A -> (f : Γ ⊢Atom (X ⇒i Y)) -> Γ ⊢ Y ⨞ pu-Type f A
-- restr T f = {!!}

-- restr (t , s) F = {!!}
-- restr (loc U) F = loc (app-Open F U)

{-

-}

  -- T0 : [] ⊢Space
  -- T0 = Free (Base BB) [ Base BB ]⇒ Free (Base BB)
  -- t0 : [] ⊢Atom T0
  -- t0 = lami (free (app (elim-BB {A = Forget (Free (Base BB))} (forget (⦗ val b0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[]))) (forget (⊤))) (var zero)))


{-

---------------------------------------------
-- Space layer

-- There is a notion of spatial extension of a type context
data SCtx : Ctx -> 𝒰₀

private variable
  Σ : SCtx Γ

-- We have a notion of space over a space context
data _⨾_⊢Space : ∀ Γ -> (Σ : SCtx Γ) -> 𝒰₀

private variable
  AX : Γ ⊢Space
  BY : Γ ⊢Space

-- We have a notion of term/open set of a space
data _⊢Atom_ : ∀ Σ -> Γ ⊢Space -> 𝒰₀

_⊢Open_ : ∀ Σ -> Γ ⊢Space -> Space
_⨾_⊢Open_ : ∀ Γ Σ -> Γ ⊢Space -> Space

instance
  hasStrictOrder:Atom : hasStrictOrder (Σ ⊢Atom X)
  hasStrictOrder:Atom = {!!}

data SCtx where
  [] : SCtx []
  _,[_] : (Σ : SCtx Γ) -> Γ ⊢Space -> SCtx (Γ ,[ A ])

data _⨾_⊢Space where
  One : Γ ⊢Space

  _⊗_ : (AX : Γ ⊢Space) -> (BY : Γ ,[ A ] ,[ AX ] ⊢Space) -> Γ ⊢Space
  _⇒_ : (AX : Γ ⊢Space) -> (BY : Γ ,[ A ] ,[ AX ] ⊢Space) -> Γ ⊢Space

  _⇒i_ : (AX BY : Γ ⊢Space) -> Γ ⊢Space

  Free : (A : Γ ⊢Type) -> Γ ⊢Space

  Sub : (AX : Γ ⊢Space) -> (U : List ((List (Σ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a)) -> Γ ⊢Space
  -- Sub : (AX : Γ ⊢Space) -> (U : List ((List (Σ ⊢Atom X) :& isUniqueSorted)) :& (isIndependent2Base λ a b -> ∑ λ x -> (x ∈ ⟨ a ⟩) ×-𝒰 (x ∉ ⟨ b ⟩) )) -> Γ ⊢Space
  -- Sub : (AX : Γ ⊢Space) -> (U : 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Σ ⊢Atom X) since hasStrictOrder:Atom))) -> Γ ⊢Space

su-Atom-Space : Γ ⊢ A -> Σ ⊢Atom X -> Γ ,[ A ] ,[ AX ] ⊢Space -> Γ ⊢Space
su-Atom-Space = {!!}

data _⊢Atom_ where
  val : Γ ⊢ A -> Σ ⊢Atom Free A
  app : Σ ⊢Atom X ⇒ BY -> (a : Γ ⊢ A) -> (x : Σ ⊢Atom X) -> Σ ⊢Atom su-Atom-Space a x BY
  appi : Σ ⊢Atom (AX ⇒i BY) -> (x : Σ ⊢Atom X) -> Σ ⊢Atom BY

  liftfree : Γ ⊢ A ⇒ wk-Sort B -> Σ ⊢Atom (Free A ⇒i Free B)

  -- free : ⟨ Γ ,[ A ] ,[ Free A ] ⊢Open AX ⟩ -> Σ ,[ Free A ] ⊢Atom X


Σ ⊢Open AX = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Σ ⊢Atom X) since hasStrictOrder:Atom))


su-Space : Γ ⊢ A -> ⟨ Σ ⊢Open AX ⟩ -> Γ ,[ A ] ,[ AX ] ⊢Space -> Γ ⊢Space
su-Space t s One = {!!}
su-Space t s (BY ⊗ BY₁) = {!!}
su-Space t s (AX ⇒ BY) = {!!}
su-Space t s (AX ⇒i BY) = {!!}
su-Space t s (Free A) = {!!}
su-Space t s (Sub BY U) = Sub ({!!}) {!!}

-- data _⨾_⊢Open_ where

-- _≤-SCtx_ : SCtx -> SCtx -> 

---------------------------------------------
-- Location layer

-- We have an assignment of locations in a space to a type
data _⨾_⊢_＠_ : (Γ : Ctx) -> (Σ : SCtx Γ) -> Γ ⊢Type -> Γ ⊢Space -> 𝒰₂ where

  -- _,dep_ : (Γ ⊢ A ＠ AX) -> Γ ,[ A ] ,[ AX ] ⊢ B ＠ BY -> Γ ⊢ (A ⊗ B) ＠ (AX ⊗ BY)

  _,_ : (Γ ⊢ A ＠ AX) -> (Γ ⊢ B ＠ AX) -> Γ ⊢ (A ∥ B) ＠ AX

  loc : ∀{A} -> ⟨ Σ ⊢Open AX ⟩ -> Γ ⊢ (Base A) ＠ AX

-- If we have a location assignment, we can restrict it along a ?


-- We have A over X and want to restrict to A over a smaller BY
-- For that we need to give a map BY -> AX (or AX -> BY) which describes this
-- restriction

-- bind-Open : ⟨ Σ ⊢Open AX ⟩ -> 

map-loc2 : Γ ⊢ A ＠ AX -> Σ ⊢Atom (BY ⇒i AX) -> Γ ⊢ A ＠ BY
map-loc2 = {!!}

map-loc : Γ ⊢ A ＠ AX -> Σ ⊢Atom (AX ⇒i BY) -> Γ ⊢ A ＠ BY
map-loc (L , M) f = map-loc L f , map-loc M f
map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)



-- restr : Γ ⊢ A ＠ AX -> ⟨ Σ ,[ AX ] ⊢Open BY ⟩ -> Γ ⊢ A ＠ su-Space {!!} {!!} BY
-- restr = {!!}


-- -- And a context "extension" which assigns locations 
-- data LCtx : (Γ : Ctx) -> Γ ⊢Space -> 𝒰₂



module Example where
  T0 : [] ⊢Type
  T0 = Base NN ∥ Base NN

  T1 : [] ⨾ [] ⊢ T0 ＠ Free (Base BB)
  T1 = loc (⦗ val b0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) , loc (⦗ val b1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[]))



---------------------------------------------
-- types

-- private variable
--   U V : ⟨ L ⟩





{-


-- KindedPartialType : (Γ : Ctx) -> {U V : UniqueSortedList R} -> .(ψ : U ≤ V) -> 𝒰₁
-- KindedPartialType Γ ψ = Γ ⇂ Partial ψ ⊢Type


-- syntax KindedPartialType Γ ψ = Γ ⇂ ψ ⊢Partial

KindedLocalType : (Γ : Ctx) -> (U : ⟨ L ⟩) -> 𝒰₂
KindedLocalType Γ U = Γ ⊢ Local U Type

syntax KindedLocalType Γ U = Γ ⊢Local U

KindedGlobalType : (Γ : Ctx) -> 𝒰₂
KindedGlobalType Γ = Γ ⊢ Global Type

syntax KindedGlobalType Γ = Γ ⊢Global



-- KindedCommType : ∀ R -> (Γ : Ctx) -> 𝒰₁
-- KindedCommType R Γ = Γ ⊢Comm 

-- syntax KindedCommType L Γ = Γ ⊢Comm L Type



private variable
  AX : Γ ⊢Sort k
  BY : Γ ⊢Sort k

data _⊢Var_ : ∀ (Γ : Ctx) -> (A : Γ ⊢Sort k) -> 𝒰₂
data _⊢_ : ∀ (Γ : Ctx) -> (A : Γ ⊢Sort k) -> 𝒰₂



























infixl 40 _,[_]

-- _[_]-Type : Δ ⊢Sort k -> Γ ⇛♮ Δ -> Γ ⇂ {!!} ⊢Type

-- ♮-⇛ : Γ ⇛ Δ -> Γ ⇛♮ Δ
-- ♮-⇛ = {!!}

-- data _⇛_ where
--   id : ∀{Γ : Ctx} -> Γ ⇛ Γ
--   π₁ : ∀{Γ Δ : Ctx} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ
--   _,_ : ∀{Γ Δ : Ctx} -> (δ : Γ ⇛ Δ) -> ∀{A} -> Γ ⊢ (A [ ♮-⇛ δ ]-Type) -> Γ ⇛ Δ ,[ A ]
--   _◆-⇛_ : ∀{Γ Δ Ε : Ctx} -> Γ ⇛ Δ -> Δ ⇛ Ε -> Γ ⇛ Ε
--   ε : Γ ⇛ []

-- data _⇛♮_ where
--   ε : Γ ⇛♮ []
--   _,_ : ∀{A} -> (σ : Γ ⇛♮ Δ) -> Γ ⊢ (A [ σ ]-Type) -> Γ ⇛♮ Δ ,[ A ]











-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx) -> {A B : Γ ⊢Type} -> (A ≡ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≡ (cong-≡ (Γ ⊢_) p) x

-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx) -> {A B : Γ ⊢Type} -> (A ≡ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≡ (cong-≡ (Γ ⊢_) p) x

-- _∥⊢Type↷_ : Γ ≡ Δ -> Γ ⊢Type -> Δ ⊢Type
-- _∥⊢Type↷_ p A = transp-≡ (cong-≡ (_⊢Type) p) A


------------------------------------------------------------------------
-- Filtering (Definition)

{-
_⇂_ : Ctx -> UniqueSortedList R -> Ctx Partial
_⇂-Type_ : Γ ⊢ R Type -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢ Partial Type

[] ⇂ U = []
Γ ,[ A ] ⇂ U = Γ ⇂ ψ ,[ A ⇂-Type U ]

_⇂-Ctx₊_ : {Γ : Ctx} -> Γ ⊢Ctx₊ -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢Ctx₊
filter-Type,Ctx₊ : {Γ : Ctx} -> (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E ⊢Type) -> (U : UniqueSortedList R) -> (Γ ⇂ ψ) ⋆-Ctx₊ (E ⇂-Ctx₊ U) ⊢Type

[] ⇂-Ctx₊ U = []
E ,[ x ] ⇂-Ctx₊ U = E ⇂-Ctx₊ U ,[ filter-Type,Ctx₊ E x U ]

σ-⋆,⇂,Ctx : ∀ E U -> ((Γ ⋆-Ctx₊ E) ⇂ U) ≡ (Γ ⇂ ψ ⋆-Ctx₊ E ⇂-Ctx₊ U)
filter-Type,Ctx₊ {Γ = Γ} E A U = σ-⋆,⇂,Ctx E U ∥⊢Type↷ (A ⇂-Type U)

σ-⋆,⇂,Ctx [] U = refl-≡
σ-⋆,⇂,Ctx (E ,[ x ]) U = sym-≡ $ J1 (σ-⋆,⇂,Ctx E U) _⊢Type _,[_] (x ⇂-Type U)

{-# REWRITE σ-⋆,⇂,Ctx #-} -- we need this for `wk-Sort,ind` and for `σ-wk-⇂-Ctx₊`

-- we also need to reduce `σ-⋆,⇂,Ctx` to refl:
isRefl:σ-⋆,⇂,Ctx : ∀ {E : Γ ⊢Ctx₊} {U} -> σ-⋆,⇂,Ctx E U ≡ refl-≡
isRefl:σ-⋆,⇂,Ctx = K1 _

{-# REWRITE isRefl:σ-⋆,⇂,Ctx #-}


infixl 40 _⇂_ _⇂-Type_ _⇂-Ctx₊_

_⇂-Partial_ : {U V : UniqueSortedList R} -> Γ ⇂ V ⊢ Partial Type -> (U ≤ V) -> Γ ⇂ ψ ⊢ Partial Type
_⇂-Partial_ = {!!}

filter-Partial : (U V : UniqueSortedList R) -> Γ ⇂ V ⊢ Partial Type -> Γ ⇂ ψ ⊢ Partial Type
filter-Partial U V A = {!!}
  -- we have to check that U ≤ V, if that is the case,
  -- we can restrict all things in the context properly. If that is not the case,
  -- we can return 𝟙 because this means that our current type is not filterable
  -- to U

-}
-- End Filtering (Definition)
------------------------------------------------------------------------

-- Flat : Γ ⊢Comm -> Γ ⊢Global

-- Restrict-Local : (ϕ : U ≤ V) -> Γ ⇂ V ⊢Local -> Γ ⊢Local U
-- local : {U V : 𝒫ᶠⁱⁿ R} .{ϕ : U ≤ V} -> Γ ⇂ ϕ ⊢Partial -> Γ ⇂ V ⊢Local

data BaseType : 𝒰₀ where
  NN End : BaseType
  AA : BaseType

-- data _⇂_⊢_≤-Local_ : ∀ Γ -> .(V ≤ U) -> (Γ ⊢Local U) -> (Γ ⇂ V ⊢Local) -> 𝒰₁
-- data _⇂_⊢_≤-Term_ : ∀ (Γ : Ctx) -> .{ϕ : V ≤ U} -> {A : Γ ⊢Local U} {B : Γ ⇂ V ⊢Local} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ A -> (Γ ⊢ B) -> 𝒰₁

data _⊢_⇂_↦_ : ∀ (Γ : Ctx) -> (AX : Γ ⊢Global) -> (U : ⟨ L ⟩) -> (A : Γ ⊢Local U) -> 𝒰₂ where

data _⊢domain_↦_ : ∀ (Γ : Ctx) -> (AX : Γ ⊢Global) -> (U : ⟨ L ⟩) -> 𝒰₂ where

data _⊢_≡_Type : ∀(Γ : Ctx) -> (AX BY : Γ ⊢Sort k) -> 𝒰₂ where
data _⊢_≡_∶_ : ∀(Γ : Ctx) -> {AX BY : Γ ⊢Sort k} (x : Γ ⊢ AX) (y : Γ ⊢ BY) -> (Γ ⊢ AX ≡ BY Type) -> 𝒰₂ where

data _⊢_Type where

  Base : BaseType -> Γ ⊢ Local U Type

  -- A local type can be embedded as global type
  Loc : ∀ U -> Γ ⊢ Local U Type -> Γ ⊢ Global Type

  -- A global type can be restricted to an open set
  _⇂_ : {Γ : Ctx} -> Γ ⊢ Global Type -> (U : ⟨ L ⟩) -> Γ ⊢Local U


  _⊗_ : (AX BY : Γ ⊢Sort k) -> Γ ⊢Sort k
  -- _⊗_ : (AX BY : Γ ⊢Global) -> Γ ⊢Global
  -- _⊠_ : (AX : Γ ⊢Local U) (BY : Γ ⊢Local V) -> Γ ⊢Local (U ∨ V)
  _⇒_ : (AX : Γ ⊢Global) -> (BY : Γ ,[ AX ] ⊢Global) -> Γ ⊢Global

  _⇒ₗ_ : (AX : Γ ⊢Local U) -> (BY : Γ ,[ Loc U AX ] ⊢Local U) -> Γ ⊢Local U



infixr 50 _⊗_
infixr 40 _⇒_ _⇒ₗ_
infixl 35 _⇂_

{-
  located : (U : 𝒫ᶠⁱⁿ R) -> (A : Γ ⊢Local U) -> Γ ⊢Global --V ≤ ?)

  Base : BaseType -> Γ ⊢Local U

  _⇒_ : (A : Γ ⊢Sort k) -> (B : Γ ,[ A ] ⊢Sort k) -> Γ ⊢Sort k
  _⊗_ : (A : Γ ⊢Sort k) -> (B : Γ ,[ A ] ⊢Sort k) -> Γ ⊢Sort k

  Unit : Γ ⊢Sort k

  Val : {U V : 𝒫ᶠⁱⁿ R} .(ϕ : U ≤ V) -> {A : Γ ⇂ V ⊢Local} -> {B : Γ ⊢Local U} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ located U B -> Γ ⇂ ϕ ⊢Partial -- next step: Use relation here instead of restrict-local function

  Fill : .(ϕ : U ≤ V) -> Γ ⇂ ϕ ⊢Partial -> Γ ⊢Global

  Fam : ∀ (U : 𝒫ᶠⁱⁿ R) -> Γ ⊢ (located U (Base NN)) -> Γ ⊢Local U

  U-Comm : Γ ⊢Global

  Comm : (Y : Γ ⊢Comm ) -> Γ ,[ Flat Y ] ⊢Global -> Γ ⊢Global


  -------------------
  -- Normalizable:

  -- [_]⇂_ : 


data _⇂_⊢_≤-Term_ where

data _⇂_⊢_≤-Local_ where
  Base : ∀ b -> .{ϕ : U ≤ V} -> Γ ⇂ ϕ ⊢ Base b ≤-Local Base b
  Fam : ∀ {U V : 𝒫ᶠⁱⁿ R} -> .(ϕ : V ≤ U)
      -> (m : Γ ⊢ (located U (Base NN))) -> (n : Γ ⊢ (located V (Base NN)))
      -- -> (Γ ⇂ ? ⊢ m ≤-Term n)
      -> Γ ⇂ ϕ ⊢ Fam U m ≤-Local Fam V n
  -- Γ ⊢ (located U (Base NN)) -> Γ ⊢Local U

-}


syntax Loc A Y = Y ＠ A


{-
Restrict-Local ϕ (Base x) = Base x
Restrict-Local ϕ (A ⇒ A₁) = {!!}
Restrict-Local ϕ (A ⊗ A₁) = {!!}
Restrict-Local ϕ Unit = {!!}
Restrict-Local ϕ (Fam _ x) = {!!}

local (A ⇒ A₁) = {!!}
local Unit = {!!}
local (Val ϕ {A = A} Φ x) = A



data _⊢Comm where
  ⟮_↝_⨾_⟯[_]_ : (U V : 𝒫ᶠⁱⁿ R) -> {W : 𝒫ᶠⁱⁿ R} -> .(ϕ : W ≤ U) -> (A : Γ ⇂ (ϕ ⟡ ι₀-∨ {b = V}) ⊢Partial) -> Γ ,[ Fill (ϕ ⟡ ι₀-∨ {b = V}) A ] ⊢Comm -> Γ ⊢Comm 
  -- ⩒⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ (reflexive ∶ ⦗ a ⦘ ≤ ⦗ a ⦘) ⊢ R Type) -> Γ ,[ A ] ⊢Comm -> Γ ⊢Comm 
  -- ⩑⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ (reflexive ∶ ⦗ a ⦘ ≤ ⦗ a ⦘) ⊢ R Type) -> Γ ,[ A ] ⊢Comm -> Γ ⊢Comm 
  End : Γ ⊢Comm

  El-Comm : Γ ⊢ U-Comm -> Γ ⊢Comm



-}











data _⊢Var_ where
  zero : Γ ,[ A ] ⊢Var (wk-Sort A)
  suc : Γ ⊢Var A -> Γ ,[ B ] ⊢Var (wk-Sort A)

-- data _⊢Var : Ctx -> 𝒰₀ where
--   zero : Γ ,[ A ] ⊢Var
--   suc : Γ ⊢Var -> Γ ,[ A ] ⊢Var

-- KindedLocalTerm : ∀ (Γ : Ctx) -> ∀ U -> (A : Γ ⊢Local U) -> 𝒰 _
-- KindedLocalTerm Γ U A = Γ ⊢ A

-- syntax KindedLocalTerm Γ U A = Γ ⇂ U ⊢ A


data _⊢_ where

  -- we have variables
  var : Γ ⊢Var A -> Γ ⊢ A

  -- we can take a global computation and use it in a more local context
  global : {U : ⟨ L ⟩} -> {AX : Γ ⊢Global} -> Γ ⊢ AX -> Γ ⊢ AX ⇂ U

  -- we can construct Loc terms
  loc : (U : ⟨ L ⟩) -> (BY : Γ ⊢ Local U Type) -> Γ ⊢ BY -> Γ ⊢ Loc U BY
  local : {Γ : Ctx} (U : ⟨ L ⟩) -> (AX : Γ ⊢Global) -> Γ ⊢domain AX ↦ U -> (BY : Γ ⊢Local U)
          -> Γ ⊢ AX ⇂ U -> Γ ⊢ AX

  glue : {Γ : Ctx} -> {AX : Γ ⊢Global} -> (U V : ⟨ L ⟩)
          -> Γ ⊢ AX ⇂ U -> Γ ⊢ AX ⇂ V
          -> Γ ⊢ AX ⇂ (U ∨ V)

  ev-⊗ : Γ ⊢ (AX ⊗ BY) ⇂ U -> Γ ⊢ (AX ⇂ U) ⊗ (BY ⇂ U)
  ve-⊗ : ∀{Γ : Ctx} -> {AX BY : Γ ⊢Global} -> {U : ⟨ L ⟩}
         -> Γ ⊢ (AX ⇂ U) ⊗ (BY ⇂ U) -> Γ ⊢ (AX ⊗ BY) ⇂ U

  ev-⇒ : Γ ⊢ (AX ⇒ BY) ⇂ U -> Γ ⊢ (AX ⇂ U) ⇒ₗ (special-su-top {!!} BY ⇂ U)

  -- functions
  lam : Γ ,[ A ] ⊢ B -> Γ ⊢ A ⇒ B
  app : Γ ⊢ A ⇒ B -> (t : Γ ⊢ A) -> Γ ⊢ su-Sort t B



module Examples where
  open import KamiTheory.Dev.2024-01-20.Open
  open import KamiTheory.Dev.2024-01-20.StrictOrder.Base

  AXXA : hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁} (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))
  AXXA = it

  LL : _ :& hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁}
  LL = (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))

  ε : CtxL
  ε = []

  u v uv : 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))
  u = ⦗ # 0 ⦘ ∷ [] since ([] ∷ [])
  v = ⦗ # 1 ⦘ ∷ [] since ([] ∷ [])
  uv = u ∨ v
  -- uv = ⦗ # 0 ⦘ ∷ ⦗ # 1 ⦘ ∷ []

  Ni : ∀{Γ : CtxL} -> 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)) -> Γ ⊢ Global Type
  Ni w = Loc (w) (Base NN)

  T1 : ∀{Γ : CtxL} -> Γ ⊢ Global Type
  T1 = Loc u (Base NN) ⊗ Loc v (Base NN)

  T2 : ∀{Γ : CtxL} -> Γ ⊢ Global Type
  T2 = Ni u ⇒ wk-Sort T1

  t2 : ε ,[ T2 ] ⊢ Ni u ⇒ Ni u ⇒ Ni v
  t2 = lam (lam (local uv (Ni v) {!!} {!!} (glue u v (global {!!}) {!!})))

{-
-}
  -- lam (local uv (wk-Sort T1) {!!} (Base NN ⊗ₗ Base NN) {!!} {!!})


-}
-}


-}
