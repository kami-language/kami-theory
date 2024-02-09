
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Rules-2024-01-29 where

open import Agora.Conventions hiding (Σ ; Lift ; k)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.UniqueSortedList hiding (it)



-------------------
-- we have a layer system for the context argument

-- data Layer : 𝒰₁ where
--   Partial : Layer
--   Global : (A : StrictOrder ℓ₀) -> Layer

Layer = Preorder (ℓ₁ , ℓ₁ , ℓ₁) :& hasFiniteJoins



private variable
  K L : Layer

-- Open : Layer -> 𝒰 _
-- Open L = List ⟨ L ⟩

-- macro
--   𝒪 : ∀ L -> _
--   ⟨ L ⟩ = #structureOn (Open L)



---------------------------------------------
-- context morphisms

-- data _⇛_ : Ctx k -> Ctx k -> 𝒰₁
-- data _⇛♮_ : Ctx k -> Ctx k -> 𝒰₁


---------------------------------------------
-- types

-- private variable
--   R S : StrictOrder ℓ₀

private variable
  U V : ⟨ L ⟩
  -- ψ : ∀{U V : Open L} -> U ≤-𝒪 V


data Kind (L : Layer) : 𝒰 ℓ₁ where
  -- Partial : {U V : UniqueSortedList R} -> .(ψ : U ≤ V) -> Kind L
  Local : (U : ⟨ L ⟩) -> Kind L
  Global : Kind L
  -- Comm : (A : StrictOrder ℓ₀) -> Kind

private variable
  k l : Kind L

-- types
data Ctx {L : Layer} : (k : Kind L) -> 𝒰₂

private variable
  Γ Δ : Ctx k

data TypeOfKind {L : Layer} : ∀ (k : Kind L) (Γ : Ctx k) -> 𝒰₂

syntax TypeOfKind k Γ = Γ ⊢ k Type




-- KindedPartialType : (Γ : Ctx k) -> {U V : UniqueSortedList R} -> .(ψ : U ≤ V) -> 𝒰₁
-- KindedPartialType Γ ψ = Γ ⇂ Partial ψ ⊢Type


-- syntax KindedPartialType Γ ψ = Γ ⇂ ψ ⊢Partial

KindedLocalType : (U : ⟨ L ⟩) -> (Γ : Ctx {L = L} (Local U)) -> 𝒰₂
KindedLocalType U Γ = Γ ⊢ Local U Type

syntax KindedLocalType Γ U = Γ ⊢Local U

KindedGlobalType : (Γ : Ctx {L = L} Global) -> 𝒰₂
KindedGlobalType Γ = Γ ⊢ Global Type

syntax KindedGlobalType Γ = Γ ⊢Global



-- KindedCommType : ∀ R -> (Γ : Ctx k) -> 𝒰₁
-- KindedCommType R Γ = Γ ⊢Comm 

-- syntax KindedCommType L Γ = Γ ⊢Comm L Type



private variable
  A : Γ ⊢ k Type
  B : Γ ⊢ k Type

  X : Γ ⊢ k Type
  Y : Γ ⊢ k Type

data _⊢Var_ : ∀ (Γ : Ctx k) -> (A : Γ ⊢ k Type) -> 𝒰₂
data _⊢_ {L : Layer} : {k : Kind L} -> (Γ : Ctx k) -> (A : Γ ⊢ k Type) -> 𝒰₂





data Ctx where
  [] : Ctx k
  _,[_] : ∀ (Γ : Ctx k) -> (A : Γ ⊢ k Type) -> Ctx k





data _⊢Ctx₊ : Ctx k -> 𝒰₂

_⋆-Ctx₊_ : ∀ (Γ : Ctx k) -> Γ ⊢Ctx₊ -> Ctx k

data _⊢Ctx₊ where
  [] : Γ ⊢Ctx₊
  _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢ Global Type -> Γ ⊢Ctx₊

_⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≣ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

-- Δ ⋆-Ctx₊₂ [] = Δ
-- Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≣ (cong-≣ _⇂_⊢Type (sym-≣ assoc-⋆-Ctx₊)) x ]

Γ ⋆-Ctx₊ [] = Γ
Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

-- instance
--   hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx k) (_⊢Ctx₊) (λ _ _ -> Ctx k)
--   hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }


{-

assoc-⋆-Ctx₊ {E = []} = refl-≣
assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
  let p = sym-≣ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
  in J1 p _⊢Type _,[_] x

{-# REWRITE assoc-⋆-Ctx₊ #-}
-}



infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_

















infixl 40 _,[_]

-- _[_]-Type : Δ ⊢ k Type -> Γ ⇛♮ Δ -> Γ ⇂ {!!} ⊢Type

-- ♮-⇛ : Γ ⇛ Δ -> Γ ⇛♮ Δ
-- ♮-⇛ = {!!}

-- data _⇛_ where
--   id : ∀{Γ : Ctx k} -> Γ ⇛ Γ
--   π₁ : ∀{Γ Δ : Ctx k} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ
--   _,_ : ∀{Γ Δ : Ctx k} -> (δ : Γ ⇛ Δ) -> ∀{A} -> Γ ⊢ (A [ ♮-⇛ δ ]-Type) -> Γ ⇛ Δ ,[ A ]
--   _◆-⇛_ : ∀{Γ Δ Ε : Ctx k} -> Γ ⇛ Δ -> Δ ⇛ Ε -> Γ ⇛ Ε
--   ε : Γ ⇛ []

-- data _⇛♮_ where
--   ε : Γ ⇛♮ []
--   _,_ : ∀{A} -> (σ : Γ ⇛♮ Δ) -> Γ ⊢ (A [ σ ]-Type) -> Γ ⇛♮ Δ ,[ A ]











-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx k) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx k) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

-- _∥⊢Type↷_ : Γ ≣ Δ -> Γ ⊢Type -> Δ ⊢Type
-- _∥⊢Type↷_ p A = transp-≣ (cong-≣ (_⊢Type) p) A


------------------------------------------------------------------------
-- Filtering (Definition)

{-
_⇂_ : Ctx k -> UniqueSortedList R -> Ctx Partial
_⇂-Type_ : Γ ⊢ R Type -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢ Partial Type

[] ⇂ U = []
Γ ,[ A ] ⇂ U = Γ ⇂ ψ ,[ A ⇂-Type U ]

_⇂-Ctx₊_ : {Γ : Ctx k} -> Γ ⊢Ctx₊ -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢Ctx₊
filter-Type,Ctx₊ : {Γ : Ctx k} -> (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E ⊢Type) -> (U : UniqueSortedList R) -> (Γ ⇂ ψ) ⋆-Ctx₊ (E ⇂-Ctx₊ U) ⊢Type

[] ⇂-Ctx₊ U = []
E ,[ x ] ⇂-Ctx₊ U = E ⇂-Ctx₊ U ,[ filter-Type,Ctx₊ E x U ]

σ-⋆,⇂,Ctx : ∀ E U -> ((Γ ⋆-Ctx₊ E) ⇂ U) ≣ (Γ ⇂ ψ ⋆-Ctx₊ E ⇂-Ctx₊ U)
filter-Type,Ctx₊ {Γ = Γ} E A U = σ-⋆,⇂,Ctx E U ∥⊢Type↷ (A ⇂-Type U)

σ-⋆,⇂,Ctx [] U = refl-≣
σ-⋆,⇂,Ctx (E ,[ x ]) U = sym-≣ $ J1 (σ-⋆,⇂,Ctx E U) _⊢Type _,[_] (x ⇂-Type U)

{-# REWRITE σ-⋆,⇂,Ctx #-} -- we need this for `wk-Type,ind` and for `σ-wk-⇂-Ctx₊`

-- we also need to reduce `σ-⋆,⇂,Ctx` to refl:
isRefl:σ-⋆,⇂,Ctx : ∀ {E : Γ ⊢Ctx₊} {U} -> σ-⋆,⇂,Ctx E U ≣ refl-≣
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
-- data _⇂_⊢_≤-Term_ : ∀ (Γ : Ctx k) -> .{ϕ : V ≤ U} -> {A : Γ ⊢Local U} {B : Γ ⇂ V ⊢Local} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ A -> (Γ ⊢ B) -> 𝒰₁

-- data _⊢_⇂_↦_ : ∀ (Γ : Ctx k) -> (X : Γ ⊢Global) -> (U : ⟨ L ⟩) -> (A : Γ ⊢Local U) -> 𝒰₂ where

-- data _⊢domain_↦_ : ∀ (Γ : Ctx k) -> (X : Γ ⊢Global) -> (U : ⟨ L ⟩) -> 𝒰₂ where

_⇂-Ctx_ : Ctx {L = L} Global -> (U : ⟨ L ⟩) -> Ctx {L = L} (Local U)

data _⊢_≡_Type : ∀(Γ : Ctx k) -> (X Y : Γ ⊢ k Type) -> 𝒰₂ where
data _⊢_≡_∶_ : ∀(Γ : Ctx k) -> {X Y : Γ ⊢ k Type} (x : Γ ⊢ X) (y : Γ ⊢ Y) -> (Γ ⊢ X ≡ Y Type) -> 𝒰₂ where

data TypeOfKind where

  Base : BaseType -> Γ ⊢ Local U Type

  -- A local type can be embedded as global type
  Loc : ∀ U -> Γ ⇂-Ctx U ⊢ Local U Type -> Γ ⊢ Global Type

  -- A global type can be restricted to an open set
  _⇂_by[_] : Γ ⊢ Global Type -> ∀ U -> ∀{Γ'} -> (Γ ⇂-Ctx U) ≣ Γ' -> Γ' ⊢ Local U Type


  _⊗_ : (X Y : Γ ⊢ k Type) -> Γ ⊢ k Type
  -- _⊗_ : (X Y : Γ ⊢Global) -> Γ ⊢Global
  -- _⊠_ : (X : Γ ⊢Local U) (Y : Γ ⊢Local V) -> Γ ⊢Local (U ∨ V)
  _⇒_ : (X : Γ ⊢ k Type) -> (Y : Γ ,[ X ] ⊢ k Type) -> Γ ⊢ k Type


pattern _⇂_ Γ U = Γ ⇂ U by[ refl-≣ ]


infixr 60 _⊗_
infixr 50 _⇒_ _⇒ₗ_
infixl 45 _⇂_ _⇂-Ctx_

[] ⇂-Ctx U = []
(Γ ,[ A ]) ⇂-Ctx U = Γ ⇂-Ctx U ,[ A ⇂ U ]


{-
  located : (U : 𝒫ᶠⁱⁿ R) -> (A : Γ ⊢Local U) -> Γ ⊢Global --V ≤ ?)

  Base : BaseType -> Γ ⊢Local U

  _⇒_ : (A : Γ ⊢ k Type) -> (B : Γ ,[ A ] ⊢ k Type) -> Γ ⊢ k Type
  _⊗_ : (A : Γ ⊢ k Type) -> (B : Γ ,[ A ] ⊢ k Type) -> Γ ⊢ k Type

  Unit : Γ ⊢ k Type

  Val : {U V : 𝒫ᶠⁱⁿ R} .(ϕ : U ≤ V) -> {A : Γ ⇂ V ⊢Local} -> {B : Γ ⊢Local U} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ located U B -> Γ ⇂ ϕ ⊢Partial -- next step: Use relation here instead of restrict-local function

  Fill : .(ϕ : U ≤ V) -> Γ ⇂ ϕ ⊢Partial -> Γ ⊢Global

  Fam : ∀ (U : 𝒫ᶠⁱⁿ R) -> Γ ⊢ (located U (Base NN)) -> Γ ⊢Local U

  U-Comm : Γ ⊢Global

  Comm : (T : Γ ⊢Comm ) -> Γ ,[ Flat T ] ⊢Global -> Γ ⊢Global


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


syntax Loc A T = T ＠ A


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

------------------------------------------------------------------------
-- Weakening


{-# TERMINATING #-}
wk-Ctx₊ : (E : Γ ⊢Ctx₊) -> Γ ,[ A ] ⊢Ctx₊

wk-Type,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢ k Type) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ k Type
-- wk-≤-Local,ind : {Γ : Ctx k}{A : Γ ⊢ k Type} -> ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢Local U} {Y : Γ ⋆-Ctx₊ E ⊢Local V} -> .{ϕ : V ≤ U} -> _ ⇂ ϕ ⊢ X ≤-Local Y -> _ ⇂ ϕ ⊢ wk-Type,ind {A = A} E X ≤-Local wk-Type,ind E Y
wk-Term-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢ k Type} -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ wk-Type,ind E X
wk-Var-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢ k Type} -> Γ ⋆-Ctx₊ E ⊢Var X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Var wk-Type,ind E X

wk-Ctx₊ [] = []
wk-Ctx₊ (E ,[ x ]) = wk-Ctx₊ E ,[ wk-Type,ind E x ]


wk-Type,ind = {!!}
-- wk-Type,ind E (located U A) = located U (wk-Type,ind E A) -- let A' = (wk-Type,ind (E ⇂-Ctx₊ U) A) in located U {!!} -- located U (wk-Type,ind (E ⇂-Ctx₊ U) A) -- (wk-Type,ind (E ⇂-Ctx₊ U) ?)
-- wk-Type,ind E (Base x) = Base x
-- wk-Type,ind E (T ⇒ B) = wk-Type,ind E T ⇒ wk-Type,ind (E ,[ T ]) B
-- wk-Type,ind E (T ⊗ B) = wk-Type,ind E T ⊗ wk-Type,ind (E ,[ T ]) B
-- wk-Type,ind E Unit = Unit
-- wk-Type,ind E (Val ϕ Φ x) = Val ϕ (wk-≤-Local,ind E Φ) (wk-Term-ind E x)
-- wk-Type,ind E (Fill ϕ A) = Fill ϕ (wk-Type,ind E A)
-- wk-Type,ind E (Fam U n) = Fam U (wk-Term-ind E n)
-- wk-Type,ind E (U-Comm) = U-Comm

-- wk-Comm,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Comm ) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Comm 
-- wk-Comm,ind E (⟮ U ↝ V ⨾ ϕ ⟯[ A ] Z) = ⟮ U ↝ V ⨾ ϕ ⟯[ wk-Type,ind E A ] wk-Comm,ind (E ,[ Fill _ _ ]) Z
-- wk-Comm,ind E End = End
-- wk-Comm,ind E (El-Comm x) = El-Comm (wk-Term-ind E x)

wk-Type : Γ ⊢ k Type -> Γ ,[ A ] ⊢ k Type
wk-Type X = wk-Type,ind [] X -- [ wk-⇛♮ id-⇛♮ ]-Type

-- wk-≤-Local,ind E (Base b {ϕ = ϕ}) = Base b {ϕ = ϕ}
-- wk-≤-Local,ind E (Fam ϕ m n) = Fam ϕ (wk-Term-ind E m) (wk-Term-ind E n)


wk-Term : {X : Γ ⊢ k Type} -> Γ ⊢ X -> Γ ,[ A ] ⊢ wk-Type X
wk-Term t = wk-Term-ind [] t


-- wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

-- weakening over a whole context
wks-Type : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢ k Type) -> Γ ⋆-Ctx₊ E ⊢ k Type
wks-Type [] A = A
wks-Type (E ,[ x ]) A = wk-Type (wks-Type E A)

-- β-wk-Type,ind,empty : ∀{A : Γ ,[ B ] ⊢ k Type} -> wk-Type,ind [] A ≣ A
-- β-wk-Type,ind,empty = ?



-- End weakening
------------------------------------------------------------------------





------------------------------------------------------------------------
-- Substitution

su-Ctx₊ : (Γ ⊢ A) -> Γ ,[ A ] ⊢Ctx₊ -> Γ ⊢Ctx₊

-- su-Type₂,ind : ∀{Γ'} -> Γ' ⇂-Ctx U ≣ (Γ ,[ A ] ⋆-Ctx₊ E)
--                -> (t : Γ ⇂-Ctx U ⊢ A)
--                -> ∀ E -> (Z : Γ ,[ A ] ⋆-Ctx₊ E ⊢ k Type) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢ k Type
-- su-Type₂,ind = ?

su-Type,ind : (t : Γ ⊢ A) -> ∀ E -> (Z : Γ ,[ A ] ⋆-Ctx₊ E ⊢ k Type) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢ k Type
-- su-≤-Local,ind : {Γ : Ctx k}{A : Γ ⊢ k Type} -> ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢Local U} {Y : Γ ⋆-Ctx₊ E ⇂ V ⊢Local} -> .{ϕ : V ≤ U} -> _ ⇂ ϕ ⊢ X ≤-Local Y -> _ ⇂ ϕ ⊢ su-Type,ind {A = A} E X ≤-Local su-Type,ind E Y
-- su-Term-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢ k Type} -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢ su-Type,ind E X
-- su-Var-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢ k Type} -> Γ ⋆-Ctx₊ E ⊢Var X -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢Var su-Type,ind E X

su-Ctx₊ t [] = []
su-Ctx₊ t (E ,[ x ]) = su-Ctx₊ t E ,[ su-Type,ind t _ x ]

su-Type,ind t E (Base x) = Base x
su-Type,ind t E (Loc U X) = Loc U {!!}
su-Type,ind t E (X ⇂ U by[ x ]) = {!su-Type,ind ? ? X!} ⇂ {!!} by[ {!!} ]
su-Type,ind t E (X ⊗ X₁) = {!!}
su-Type,ind t E (X ⇒ X₁) = {!!}

-- su-Type,ind t E (located U A) = located U (su-Type,ind t E A)
-- su-Type,ind t E (Base x) = Base x
-- su-Type,ind t E (A ⇒ B) = su-Type,ind t E A ⇒ su-Type,ind t _ B
-- su-Type,ind t E Unit = Unit
-- su-Type,ind t E (Val ϕ x x₁) = {!!}
-- su-Type,ind t E (Fill ϕ x) = {!!}
-- su-Type,ind t E (Fam U x) = {!!}
-- su-Type,ind t E U-Comm = U-Comm

su-Type : (t : Γ ⊢ A) -> Γ ,[ A ] ⊢ k Type -> Γ ⊢ k Type
su-Type t T = su-Type,ind t [] T



-- special-su-top : Γ ,[ B ] ⊢ wk-Type A ->  Γ ,[ A ] ⊢ k Type -> Γ ,[ B ] ⊢ k Type
-- special-su-top t T = su-Type t (wk-Type,ind ([] ,[ _ ]) T)

-- End Substitution
------------------------------------------------------------------------





data _⊢Var_ where
  zero : Γ ,[ A ] ⊢Var (wk-Type A)
  suc : Γ ⊢Var A -> Γ ,[ B ] ⊢Var (wk-Type A)

-- data _⊢Var : Ctx k -> 𝒰₀ where
--   zero : Γ ,[ A ] ⊢Var
--   suc : Γ ⊢Var -> Γ ,[ A ] ⊢Var

-- KindedLocalTerm : ∀ (Γ : Ctx k) -> ∀ U -> (A : Γ ⊢Local U) -> 𝒰 _
-- KindedLocalTerm Γ U A = Γ ⊢ A

-- syntax KindedLocalTerm Γ U A = Γ ⇂ U ⊢ A


data _⊢_ where

  -- we have variables
  var : Γ ⊢Var A -> Γ ⊢ A

  -- we can take a global computation and use it in a more local context
  global : Γ ⊢ X -> Γ ⇂-Ctx U ⊢ X ⇂ U

  -- we can construct Loc terms
  -- loc : (U : ⟨ L ⟩) -> (Y : Γ ⊢ Local U Type) -> Γ ⊢ Y -> Γ ⊢ Loc U Y

  local : {Γ : Ctx Global} -> ∀ U  -> (X : Γ ⊢Global) -- -> Γ ⊢domain X ↦ U
          -> Γ ⇂-Ctx U ⊢ X ⇂ U -> Γ ⊢ X

  glue : ∀ U V -> Γ ⇂-Ctx U ⊢ X ⇂ U -> Γ ⇂-Ctx V ⊢ X ⇂ V
          -> Γ ⇂-Ctx (U ∨ V) ⊢ X ⇂ (U ∨ V)

  ev-⊗ : Γ ⇂-Ctx U ⊢ (X ⊗ Y) ⇂ U -> Γ ⇂-Ctx U ⊢ (X ⇂ U) ⊗ (Y ⇂ U)

  ve-⊗ : Γ ⇂-Ctx U ⊢ (X ⇂ U) ⊗ (Y ⇂ U) -> Γ ⇂-Ctx U ⊢ (X ⊗ Y) ⇂ U

  ev-⇒ : Γ ⇂-Ctx U ⊢ (X ⇒ Y) ⇂ U -> Γ ⇂-Ctx U ⊢ (X ⇂ U) ⇒ (Y ⇂ U)

  -- functions
  lam_ : Γ ,[ A ] ⊢ B -> Γ ⊢ A ⇒ B
  app : Γ ⊢ A ⇒ B -> (t : Γ ⊢ A) -> Γ ⊢ su-Type t B



module Examples where
  open import KamiD.Dev.2024-01-20.Open
  open import KamiD.Dev.2024-01-20.StrictOrder.Base

  XX : hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁} (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))
  XX = it

  LL : _ :& hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁}
  LL = (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))

  ε : Ctx {L = LL} k
  ε = []

  u v uv : 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))
  u = ⦗ # 0 ⦘ ∷ [] since ([] ∷ [])
  v = ⦗ # 1 ⦘ ∷ [] since ([] ∷ [])
  uv = u ∨ v
  -- uv = ⦗ # 0 ⦘ ∷ ⦗ # 1 ⦘ ∷ []

  Ni : ∀{Γ : Ctx {L = LL} Global} -> 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)) -> Γ ⊢ Global Type
  Ni w = Loc (w) (Base NN)

  T1 : ∀{Γ : Ctx {L = LL} Global} -> Γ ⊢ Global Type
  T1 = Loc u (Base NN) ⊗ Loc v (Base NN)

  T2 : ∀{Γ : Ctx Global} -> Γ ⊢ Global Type
  T2 = Ni u ⇒ wk-Type T1

  t2 : ε ,[ T2 ] ⊢ Ni u ⇒ Ni u ⇒ Ni v
  t2 = lam lam local uv (Ni v) (glue u v (app (ev-⇒ (var (suc (suc zero)))) {!!}) {!!})
  -- lam (lam (local uv (Ni v) {!!} {!!} (glue u v (global {!!}) {!!})))

{-
{-
-}
  -- lam (local uv (wk-Type T1) {!!} (Base NN ⊗ₗ Base NN) {!!} {!!})



-}

