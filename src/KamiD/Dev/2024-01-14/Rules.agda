{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-14.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Data.Fin hiding (_-_ ; _+_)
open import Data.Nat hiding (_! ; _+_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-14.Core hiding (_＠_)
open import KamiD.Dev.2024-01-14.UniqueSortedList




-------------------
-- we have a layer system for the context argument

-- data Layer : 𝒰₁ where
--   Local : Layer
--   Global : (A : StrictOrder (ℓ₀ , ℓ₀)) -> Layer

Layer = StrictOrder (ℓ₀ , ℓ₀)

private variable
  K L : Layer


-- types
data Ctx : Layer -> 𝒰₁

private variable
  Γ Δ : Ctx L

---------------------------------------------
-- context morphisms

data _⇛_ : Ctx L -> Ctx L -> 𝒰₁
data _⇛♮_ : Ctx L -> Ctx L -> 𝒰₁


---------------------------------------------
-- types

private variable
  R S : StrictOrder (ℓ₀ , ℓ₀)

private variable
  U V : UniqueSortedList R

data _⇂_⊢Type : ∀ (Γ : Ctx R) -> (U : UniqueSortedList R) -> 𝒰₁
data _⊢CommType : (Γ : Ctx R) -> 𝒰₁

data Kind : 𝒰₁ where
  Local : Kind
  Global : (A : StrictOrder (ℓ₀ , ℓ₀)) -> Kind
  Comm : (A : StrictOrder (ℓ₀ , ℓ₀)) -> Kind

-- toLayer : Kind -> Layer
-- toLayer Local = Local
-- toLayer R = Global R
-- toLayer (Comm R) = Global R

KindedType : ∀ R -> (Γ : Ctx R) -> (U : UniqueSortedList R) -> 𝒰₁
KindedType R Γ U = Γ ⇂ U ⊢Type
-- KindedType Local Γ = Γ ⊢Type
-- KindedType R Γ = Γ ⊢Type
-- KindedType (Comm R) Γ = Γ ⊢CommType

syntax KindedType L Γ U = Γ ⇂ U ⊢ L Type


KindedCommType : ∀ R -> (Γ : Ctx R) -> 𝒰₁
KindedCommType R Γ = Γ ⊢CommType

syntax KindedCommType L Γ = Γ ⊢Comm L Type


private variable
  A : Γ ⇂ U ⊢Type
  B : Γ ⇂ U ⊢Type

data _⊢Var_ : ∀ (Γ : Ctx L) -> (A : Γ ⇂ U ⊢Type) -> 𝒰₁
data _⊢_ : ∀ (Γ : Ctx L) -> (A : Γ ⇂ U ⊢Type) -> 𝒰₁





data Ctx where
  [] : Ctx L
  _,[_] : ∀ (Γ : Ctx L) -> (A : Γ ⇂ U ⊢Type) -> Ctx L





data _⊢Ctx₊ : Ctx L -> 𝒰₁

_⋆-Ctx₊_ : ∀ (Γ : Ctx L) -> Γ ⊢Ctx₊ -> Ctx L

data _⊢Ctx₊ where
  [] : Γ ⊢Ctx₊
  _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⇂ U ⊢Type -> Γ ⊢Ctx₊

_⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≣ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

{-
Δ ⋆-Ctx₊₂ [] = Δ
Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≣ (cong-≣ _⇂_⊢Type (sym-≣ assoc-⋆-Ctx₊)) x ]

Γ ⋆-Ctx₊ [] = Γ
Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

instance
  hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx L) (_⊢Ctx₊) (λ _ _ -> Ctx L)
  hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }


assoc-⋆-Ctx₊ {E = []} = refl-≣
assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
  let p = sym-≣ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
  in J1 p _⊢Type _,[_] x

{-# REWRITE assoc-⋆-Ctx₊ #-}
-}



infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_

{-
[_]Ctx₊∷_ : ∀ A -> Δ ,[ A ] ⊢Ctx₊ -> Δ ⊢Ctx₊
[_]Ctx₊∷_ {Δ = Δ} A E =
  let X : Δ ⊢Ctx₊
      X = [] ,[ A ]
  in X ⋆-Ctx₊₂ E
-}















infixl 40 _,[_]

_[_]-Type : Δ ⇂ U ⊢Type -> Γ ⇛♮ Δ -> Γ ⇂ {!!} ⊢Type

♮-⇛ : Γ ⇛ Δ -> Γ ⇛♮ Δ
♮-⇛ = {!!}

-- data _⇛_ where
--   id : ∀{Γ : Ctx L} -> Γ ⇛ Γ
--   π₁ : ∀{Γ Δ : Ctx L} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ
--   _,_ : ∀{Γ Δ : Ctx L} -> (δ : Γ ⇛ Δ) -> ∀{A} -> Γ ⊢ (A [ ♮-⇛ δ ]-Type) -> Γ ⇛ Δ ,[ A ]
--   _◆-⇛_ : ∀{Γ Δ Ε : Ctx L} -> Γ ⇛ Δ -> Δ ⇛ Ε -> Γ ⇛ Ε
--   ε : Γ ⇛ []

-- data _⇛♮_ where
--   ε : Γ ⇛♮ []
--   _,_ : ∀{A} -> (σ : Γ ⇛♮ Δ) -> Γ ⊢ (A [ σ ]-Type) -> Γ ⇛♮ Δ ,[ A ]









_⊢Role : ℕ -> 𝒰₀
_⊢Role n = Fin n


-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx L) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

-- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx L) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
-- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

-- _∥⊢Type↷_ : Γ ≣ Δ -> Γ ⊢Type -> Δ ⊢Type
-- _∥⊢Type↷_ p A = transp-≣ (cong-≣ (_⊢Type) p) A


------------------------------------------------------------------------
-- Filtering (Definition)

{-
_⇂_ : Ctx R -> UniqueSortedList R -> Ctx Local
_⇂-Type_ : Γ ⊢ R Type -> (U : UniqueSortedList R) -> Γ ⇂ U ⊢ Local Type

[] ⇂ U = []
Γ ,[ A ] ⇂ U = Γ ⇂ U ,[ A ⇂-Type U ]

_⇂-Ctx₊_ : {Γ : Ctx R} -> Γ ⊢Ctx₊ -> (U : UniqueSortedList R) -> Γ ⇂ U ⊢Ctx₊
filter-Type,Ctx₊ : {Γ : Ctx R} -> (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E ⊢Type) -> (U : UniqueSortedList R) -> (Γ ⇂ U) ⋆-Ctx₊ (E ⇂-Ctx₊ U) ⊢Type

[] ⇂-Ctx₊ U = []
E ,[ x ] ⇂-Ctx₊ U = E ⇂-Ctx₊ U ,[ filter-Type,Ctx₊ E x U ]

σ-⋆,⇂,Ctx : ∀ E U -> ((Γ ⋆-Ctx₊ E) ⇂ U) ≣ (Γ ⇂ U ⋆-Ctx₊ E ⇂-Ctx₊ U)
filter-Type,Ctx₊ {Γ = Γ} E A U = σ-⋆,⇂,Ctx E U ∥⊢Type↷ (A ⇂-Type U)

σ-⋆,⇂,Ctx [] U = refl-≣
σ-⋆,⇂,Ctx (E ,[ x ]) U = sym-≣ $ J1 (σ-⋆,⇂,Ctx E U) _⊢Type _,[_] (x ⇂-Type U)

{-# REWRITE σ-⋆,⇂,Ctx #-} -- we need this for `wk-Type,ind` and for `σ-wk-⇂-Ctx₊`

-- we also need to reduce `σ-⋆,⇂,Ctx` to refl:
isRefl:σ-⋆,⇂,Ctx : ∀ {E : Γ ⊢Ctx₊} {U} -> σ-⋆,⇂,Ctx E U ≣ refl-≣
isRefl:σ-⋆,⇂,Ctx = K1 _

{-# REWRITE isRefl:σ-⋆,⇂,Ctx #-}


infixl 40 _⇂_ _⇂-Type_ _⇂-Ctx₊_

_⇂-Local_ : {U V : UniqueSortedList R} -> Γ ⇂ V ⊢ Local Type -> (U ⊆ V) -> Γ ⇂ U ⊢ Local Type
_⇂-Local_ = {!!}

filter-Local : (U V : UniqueSortedList R) -> Γ ⇂ V ⊢ Local Type -> Γ ⇂ U ⊢ Local Type
filter-Local U V A = {!!}
  -- we have to check that U ⊆ V, if that is the case,
  -- we can restrict all things in the context properly. If that is not the case,
  -- we can return 𝟙 because this means that our current type is not filterable
  -- to U

-}
-- End Filtering (Definition)
------------------------------------------------------------------------

-- Flat : Γ ⊢Comm R Type -> Γ ⊢ R Type
-- Flat = {!!}

data BaseType : 𝒰₀ where
  NN End : BaseType

data _⇂_⊢Type where
  located : (V ⊆ U) -> (A : Γ ⇂ U ⊢Type) -> Γ ⇂ V ⊢ R Type

  Base : BaseType -> Γ ⇂ U ⊢ R Type

  _⇒_ : (A : Γ ⇂ U ⊢ R Type) -> (B : Γ ,[ A ] ⇂ U ⊢ R Type) -> Γ ⇂ U ⊢ R Type

  Unit : Γ ⇂ U ⊢Type

  Val : (ϕ : V ⊆ U) -> (A : Γ ⇂ U ⊢ R Type) -> Γ ⊢ located ϕ A -> Γ ⇂ U ⊢ R Type

  -------------------
  -- Normalizable:

  -- [_]⇂_ : 




syntax located A T = T ＠ A


data _⊢CommType where
  ⟮_↝_⟯[_]_ : (a b : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ∪ ⦗ b ⦘ ⊢ R Type) -> Γ ,[ A ] ⊢CommType -> Γ ⊢CommType
  ⩒⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ⊢ R Type) -> Γ ,[ A ] ⊢CommType -> Γ ⊢CommType
  ⩑⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ⊢ R Type) -> Γ ,[ A ] ⊢CommType -> Γ ⊢CommType
  End : Γ ⊢CommType

-- data _⊢CommType where
--   ⟮_↝_⟯[_]_ : (a b : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ∪ ⦗ b ⦘ ⊢ Local Type) -> Γ ,[ A ＠ ⦗ a ⦘ ∪ ⦗ b ⦘ ] ⊢Comm R Type -> Γ ⊢Comm R Type
--   ⩒⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ⊢ Local Type) -> Γ ,[ A ＠ ⦗ a ⦘ ] ⊢Comm R Type -> Γ ⊢Comm R Type
--   ⩑⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ ⦗ a ⦘ ⊢ Local Type) -> Γ ,[ A ＠ ⦗ a ⦘ ] ⊢Comm R Type -> Γ ⊢Comm R Type
--   End : Γ ⊢Comm R Type


--------------------------------------------------------------
-- Filtering (Impl types)
-- located V A ⇂-Type U = filter-Local U V {!!}
-- (T ⇒ B) ⇂-Type U = (T ⇂-Type U) ⇒ (B ⇂-Type U)
-- Unit ⇂-Type U = Unit


-- End Filtering (Impl types)
--------------------------------------------------------------


--------------------------------------------------------------
-- Projection

private
  Img = image-UniqueSortedList
  map-Img = map-image-UniqueSortedList
  _⟶_ = StrictOrderHom

_↷-Ctx_ : (f : R ⟶ S) -> Ctx R -> Ctx S
_↷-Comm_ : (f : R ⟶ S) -> Γ ⊢Comm R Type -> f ↷-Ctx Γ ⊢Comm S Type
_↷-Type_ : (f : R ⟶ S) -> Γ ⇂ U ⊢ R Type -> f ↷-Ctx Γ ⇂ Img f U ⊢ S Type
_↷-Term_ : (f : R ⟶ S) -> ∀{A : Γ ⇂ U ⊢ R Type} -> Γ ⊢ A -> f ↷-Ctx Γ ⊢ f ↷-Type A

infixl 60 _↷-Ctx_ _↷-Comm_ _↷-Type_


f ↷-Ctx [] = []
f ↷-Ctx (Γ ,[ A ]) = f ↷-Ctx Γ ,[ f ↷-Type A ]

f ↷-Type located ϕ x = located (map-Img ϕ) (f ↷-Type x)
f ↷-Type (T ⇒ B) = (f ↷-Type T) ⇒ (f ↷-Type B)
f ↷-Type Unit = Unit
f ↷-Type Base x = Base x
f ↷-Type Val ϕ A x = Val (map-Img ϕ) (f ↷-Type A) (f ↷-Term x)

f ↷-Comm (⟮ a ↝ b ⟯[ A ] x) = ⟮ ⟨ f ⟩ a ↝ ⟨ f ⟩ b ⟯[ {!!} ] ({! f ↷-Comm x !})
f ↷-Comm (⩒⟮ a ⟯[ A ] x) = {!!}
f ↷-Comm (⩑⟮ a ⟯[ A ] x) = {!!}
f ↷-Comm End = End

{-
reduce-Ctx : Ctx (Global (𝟙 + R)) -> Ctx R
reduce-Comm : Γ ⊢Comm (𝟙 + R) Type -> reduce-Ctx Γ ⊢Comm R Type
reduce-Global : Γ ⊢ (𝟙 + R) Type -> reduce-Ctx Γ ⊢ R Type

reduce-Ctx [] = []
reduce-Ctx (Γ ,[ A ]) = reduce-Ctx Γ ,[ reduce-Global A ]

reduce-Comm (⟮ just a ↝ just b ⟯[ A ] x) = ⟮ a ↝ b ⟯[ {!reduce-Global A!} ] {!!}
reduce-Comm (⟮ just a ↝ left b ⟯[ A ] x) = {!!}
reduce-Comm (⟮ left a ↝ just b ⟯[ A ] x) = {!!}
reduce-Comm (⟮ left a ↝ left b ⟯[ A ] x) = {!!}
reduce-Comm (⩒⟮ a ⟯[ A ] x) = {!!}
reduce-Comm (⩑⟮ a ⟯[ A ] x) = {!!}
reduce-Comm End = {!!}

reduce-Global T = {!!}


infixl 60 _↷-Ctx_ _↷-Comm_ _↷-Type_


-- End Projection
--------------------------------------------------------------





------------------------------------------------------------------------
-- Weakening


{-# TERMINATING #-}
wk-Ctx₊ : (E : Γ ⊢Ctx₊) -> Γ ,[ A ] ⊢Ctx₊

wk-Type,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Type) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Type

wk-Ctx₊ [] = []
wk-Ctx₊ (E ,[ x ]) = wk-Ctx₊ E ,[ wk-Type,ind E x ]

-- σ-filter-wk-Ctx₊ : ∀{E : Γ ⊢Ctx₊} {U x} -> filter-Type,Ctx₊ (wk-Ctx₊ E) (wk-Type,ind E x) U ≣ wk-Type,ind (E ⇂-Ctx₊ U) (filter-Type,Ctx₊ E x U)
-- σ-filter-wk-Ctx₊ = ?
      -- filter-Type,Ctx₊ (wk-Ctx₊ E) (wk-Type,ind E x) U ]

σ-wk-⇂-Ctx₊ : (E : Γ ⊢Ctx₊) (A : Γ ⊢Type) -> ∀{U} -> wk-Ctx₊ {A = A} E ⇂-Ctx₊ U ≣ wk-Ctx₊ (E ⇂-Ctx₊ U)

σ-filter-wk-Ctx₊ : ∀(E : Γ ⊢Ctx₊) {A : Γ ⊢Type} {U x} ->

                     filter-Type,Ctx₊ (wk-Ctx₊ {A = A} E) (wk-Type,ind E x) U

                            ≣⟨ cong-≣ (λ ξ -> _ ⋆-Ctx₊ ξ ⊢Type) (σ-wk-⇂-Ctx₊ E A) ⟩≣

                     wk-Type,ind {A = A ⇂-Type U} (E ⇂-Ctx₊ U) (filter-Type,Ctx₊ E x U)

σ-wk-⇂-Ctx₊ [] A = refl-≣
σ-wk-⇂-Ctx₊ (E ,[ x ]) A = {!!}

σ-filter-wk-Ctx₊ [] = {!refl-≣!}
σ-filter-wk-Ctx₊ (E ,[ x ]) = {!!}


-- {-# REWRITE σ-wk-⇂-Ctx₊ #-} -- we need this for `wk-Type,ind`

wk-Type,ind E (located U A) = let A' = (wk-Type,ind (E ⇂-Ctx₊ U) A) in located U {!!} -- located U (wk-Type,ind (E ⇂-Ctx₊ U) A) -- (wk-Type,ind (E ⇂-Ctx₊ U) ?)
wk-Type,ind E (Base x) = Base x
wk-Type,ind E (T ⇒ B) = wk-Type,ind E T ⇒ wk-Type,ind (E ,[ T ]) B
wk-Type,ind E Unit = Unit

wk-Type : ∀{A} -> Γ ⊢Type -> Γ ,[ A ] ⊢Type
wk-Type X = wk-Type,ind [] X -- [ wk-⇛♮ id-⇛♮ ]-Type

wk-Term-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢Type} -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ wk-Type,ind E X
wk-Term-ind = {!!}

wk-Term : {X : Γ ⊢Type} -> Γ ⊢ X -> Γ ,[ A ] ⊢ wk-Type X
wk-Term t = wk-Term-ind [] t


-- wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

-- weakening over a whole context
wks-Type : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Type) -> Γ ⋆-Ctx₊ E ⊢Type
wks-Type [] A = A
wks-Type (E ,[ x ]) A = wk-Type (wks-Type E A)

β-wks-Type-Base : ∀{X} {E : Γ ⊢Ctx₊} -> wks-Type E (Base X) ≣ Base X
β-wks-Type-Base {E = []} = refl-≣
β-wks-Type-Base {E = E ,[ x ]} = cong-≣ (wk-Type,ind []) (β-wks-Type-Base {E = E})

wks-Type₂ : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Type) -> (B : Γ ,[ A ] ⊢Type) -> (Γ ⋆-Ctx₊ E ,[ wks-Type E A ]) ⊢Type
wks-Type₂ E A B = {!!}

-- β-wks-Type-⨉ : {E : Γ ⊢Ctx₊} -> ∀{x A B} -> wks-Type E (⨉ x A B) ≣ ⨉ x (wks-Type E A) (wks-Type₂ E A B)
-- β-wks-Type-⨉ = {!!}

-- σ-wk-wks : ∀{A B : Γ ⊢Type} {E : Γ ⊢Ctx₊} -> wk-Type,ind {A = A} E (wks-Type E B) ≣ wks-Type (wk-Ctx₊ E) ((wk-Type B))
-- σ-wk-wks = {!!}

σ-wks-wk : ∀{A B : Γ ⊢Type} {E : Γ ⊢Ctx₊} -> wks-Type (wk-Ctx₊ E) (wk-Type B) ≣ wk-Type,ind {A = A} E (wks-Type E B)
σ-wks-wk = {!!}

σ-wks-wk-, : ∀{A : Γ ⊢Type} -> ∀{E2 x B E} -> wks-Type (wk-Ctx₊ E) (wk-Type,ind (E2 ,[ x ]) (wk-Type B)) ≣ wk-Type,ind E (wks-Type E (wk-Type,ind {A = A} E2 B))
σ-wks-wk-, = {!!}

-- {-# REWRITE β-wks-Type-Base β-wks-Type-⨉ σ-wks-wk σ-wks-wk-, #-}

wks-Term : (E : Γ ⊢Ctx₊) -> {A : Γ ⊢Type} -> Γ ⊢ A -> Γ ⋆-Ctx₊ E ⊢ wks-Type E A
wks-Term = {!!}


-- End weakening
------------------------------------------------------------------------









data _⊢Var_ where
  zero : {Γ : Ctx L} -> ∀{A} -> Γ ,[ A ] ⊢Var (wk-Type A)
  suc : {Γ : Ctx L} -> ∀{A B} -> Γ ⊢Var A -> Γ ,[ B ] ⊢Var (wk-Type A)

-- data _⊢Var : Ctx L -> 𝒰₀ where
--   zero : Γ ,[ A ] ⊢Var
--   suc : Γ ⊢Var -> Γ ,[ A ] ⊢Var






data _⊢_ where
  var : Γ ⊢Var A -> Γ ⊢ A
  loc : (U : UniqueSortedList R) -> Γ ⇂ U ⊢ {!!} -> Γ ⊢ located U {!!}

  -- _↝_ : {i j : n ⊢Role} {A : Γ ⇂ ⦗ i ⦘ ∪ ⦗ j ⦘ ⊢ Local Type } -> (aᵢ : Γ ⇂ ⦗ i ⦘ ⊢ A) -> (aⱼ : Γ ⇂ ⦗ j ⦘ ⊢ (ᶜᵒ A)) -> Γ ⊢ ⟮ i ↝ j ⟯[ A ]
  -- _,_ : {A B : Γ ⊢Type} -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (A ⊗ B)














module Examples where
  emp : Ctx L
  emp = []

  T₀ : [] ⊢Comm (𝔽 3) Type
  T₀ = ⟮ # 0 ↝ # 1 ⟯[ Base NN ] ⟮ # 1 ↝ # 2 ⟯[ Base NN ] End

  T₁ : [] ,[ Base NN ＠ ⦗ # 0 ⦘ ] ⊢Comm (𝔽 2) Type
  T₁ = {!!} -- ⟮ # 0 ↝ # 1 ⟯[ Val {U = ⦗ # 0 ⦘} {V = ⦗ # 1 ⦘} (Base NN) (loc ⦗ # 0 ⦘ (var {!zero!})) ] {!!}




  -- F1 : emp ⊢ (D⁻ BN) ⊗ (D⁺ BN)
  -- F1 = η BN {!? , ?!}

  -- F1 : ε ⊢ (⨇ ((D⁺ (NN))) (⨇ ((D⁻ (NN))) (D⁺ (End))))
  -- F1 = Λ (Λ ([ zero ≔ var (suc zero) ] end) )

{-
  -- T1 : (ε ,[ (D⁻ (NN)) ]) [ zero ≔ inv (d⁺ n0) ] ≣ ε
  -- T1 = {!refl-≣!}

-}

  -- F2 : ε ⊢ (⨇ ((D⁻ (NN))) (⨇ ((D⁺ ((Fam (var zero))))) (D⁺ ((Fam (n0))))))
  -- F2 = Λ (Λ ([ suc zero ≔ d⁺ n0 ] {!var zero!}) )

  -- Λ (Λ ([ zero ≔ var (suc zero) ] end))





-- id-⇛♮ : Γ ⇛♮ Γ

-- {-# REWRITE β-id-Type #-}



------------------------------------------------------------------------
-- Weakening


{-
{-# TERMINATING #-}
wk-Ctx₊ : ∀{Γ : Ctx L} {A : Γ ⊢Type} -> (E : Γ ⊢Ctx₊) -> Γ ,[ A ] ⊢Ctx₊

σ-wk-𝕠 : ∀{A : Γ ⊢Type} {E : Γ ⊢Ctx₊} -> wk-Ctx₊ (𝕠-Ctx₊ E) ≣ 𝕠-Ctx₊ (wk-Ctx₊ {A = A} E)
σ-wk-𝕠 = {!!}

{-# REWRITE σ-wk-𝕠 #-} -- TODO: Should come after definition!!

wk-Type,ind : ∀{Γ : Ctx (◌ , τ)} -> ∀{A} -> ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Type) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Type

-- σ-wk-𝕠-Type-ind : {E : Γ ⊢Ctx₊} -> ∀{A} -> wk-Type,ind (𝕠-Ctx₊ E) (𝕠-Type A) ≣ 𝕠-Type (wk-Type,ind E ?)
-- σ-wk-𝕠-Type-ind = ?

-- {-# REWRITE σ-wk-𝕠-Type-ind #-} -- TODO: Should come after definition!!

wk-Ctx₊ [] = []
wk-Ctx₊ (E ,[ x ]) = wk-Ctx₊ E ,[ wk-Type,ind (𝕠-Ctx₊ E) x ]


wk-Type,ind E (Base x) = Base x
wk-Type,ind E (⨉ c A B) = ⨉ c (wk-Type,ind E A ) (wk-Type,ind (E ,[ 𝕠-Type A ]) B)
wk-Type,ind E (D x X) = {!!}
wk-Type,ind E (Fam x) = {!!}
-}

{-
wk-Type X = let XX = wk-Type,ind [] X in {!!} -- [ wk-⇛♮ id-⇛♮ ]-Type

wk-Term-ind : ∀ E -> {X : Γ ⋆-Ctx₊ E ⊢Type} -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ wk-Type,ind E X
wk-Term-ind = {!!}

wk-Term : {X : Γ ⊢Type} -> Γ ⊢ X -> Γ ,[ A ] ⊢ wk-Type X
wk-Term t = wk-Term-ind [] t


wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

-- weakening over a whole context
wks-Type : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Type) -> Γ ⋆-Ctx₊ E ⊢Type
wks-Type [] A = A
wks-Type (E ,[ x ]) A = wk-Type (wks-Type E A)

β-wks-Type-Base : ∀{X} {E : Γ ⊢Ctx₊} -> wks-Type E (Base X) ≣ Base X
β-wks-Type-Base {E = []} = refl-≣
β-wks-Type-Base {E = E ,[ x ]} = cong-≣ (wk-Type,ind []) (β-wks-Type-Base {E = E})

wks-Type₂ : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Type) -> (B : Γ ,[ A ] ⊢Type) -> (Γ ⋆-Ctx₊ E ,[ wks-Type E A ]) ⊢Type
wks-Type₂ E A B = {!!}

β-wks-Type-⨉ : {E : Γ ⊢Ctx₊} -> ∀{x A B} -> wks-Type E (⨉ x A B) ≣ ⨉ x (wks-Type E A) (wks-Type₂ E A B)
β-wks-Type-⨉ = {!!}

-- σ-wk-wks : ∀{A B : Γ ⊢Type} {E : Γ ⊢Ctx₊} -> wk-Type,ind {A = A} E (wks-Type E B) ≣ wks-Type (wk-Ctx₊ E) ((wk-Type B))
-- σ-wk-wks = {!!}

σ-wks-wk : ∀{A B : Γ ⊢Type} {E : Γ ⊢Ctx₊} -> wks-Type (wk-Ctx₊ E) (wk-Type B) ≣ wk-Type,ind {A = A} E (wks-Type E B)
σ-wks-wk = {!!}

σ-wks-wk-, : ∀{A : Γ ⊢Type} -> ∀{E2 x B E} -> wks-Type (wk-Ctx₊ E) (wk-Type,ind (E2 ,[ x ]) (wk-Type B)) ≣ wk-Type,ind E (wks-Type E (wk-Type,ind {A = A} E2 B))
σ-wks-wk-, = {!!}

-- {-# REWRITE β-wks-Type-Base β-wks-Type-⨉ σ-wks-wk σ-wks-wk-, #-}

wks-Term : (E : Γ ⊢Ctx₊) -> {A : Γ ⊢Type} -> Γ ⊢ A -> Γ ⋆-Ctx₊ E ⊢ wks-Type E A
wks-Term = {!!}
-}

{-
{-

-- End weakening
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Un-Weakening

-- unwk-Term : Γ ,

-- End Un-Weakening
------------------------------------------------------------------------




------------------------------------------------------------------------
-- Splitting

[_]⊢Type : (E : Γ ⊢Ctx₊) -> 𝒰₀
[_]⊢Type E = _ ⋆-Ctx₊ E ⊢Type

[_]⊢_ : (E : Γ ⊢Ctx₊) -> [ E ]⊢Type -> 𝒰₀
[_]⊢_ E T = _ ⋆-Ctx₊ E ⊢ T

data Access : 𝒰₀ where
  acc noacc : Access

data ⟨_⟩⊢Ctx : (E : Γ ,[ A ] ⊢Ctx₊) -> 𝒰₀
data ⟨_⟩⊢Type_ : {E : Γ ,[ A ] ⊢Ctx₊} -> ⟨ E ⟩⊢Ctx -> Access -> 𝒰₀
data ⟨_⟩⊢_,_ : {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> {a : Access} -> ⟨ γ ⟩⊢Type a -> Access -> 𝒰₀
data ⟨_⟩⊢Var_,_ : {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> {a : Access} -> ⟨ γ ⟩⊢Type a -> Access -> 𝒰₀

private variable
  E : Γ ⊢Ctx₊
  γ : ⟨ E ⟩⊢Ctx
  α : Access
  T S : ⟨ γ ⟩⊢Type α

⟪_⟫ : ∀{E : Γ ,[ A ] ⊢Ctx₊} -> ⟨ E ⟩⊢Ctx -> Ctx _
⟪_⟫ {Γ = Γ} {E = E} γ = Γ ,[ _ ] ⋆-Ctx₊ E

restore-Type : ⟨ γ ⟩⊢Type α -> ⟪ γ ⟫ ⊢Type

restore-Term : ⟨ γ ⟩⊢ T , α -> ⟪ γ ⟫ ⊢ restore-Type T

data ⟨_⟩⊢Ctx where
  [] : ⟨_⟩⊢Ctx {Γ = Γ} {A = A} []
  _,[_] : ∀{E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> {a : Access} -> (T : ⟨ γ ⟩⊢Type a) -> ⟨ E ,[ restore-Type T ] ⟩⊢Ctx

data ⟨_⟩⊢Type_ where
  -- Base : ∀{Γ : Ctx (◌ , τ)} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> BaseType -> ⟨ γ ⟩⊢Type noacc
  Base : {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> Γ ⊢Type -> ⟨ γ ⟩⊢Type noacc

  ⨉nn : Charge -> (X : ⟨ γ ⟩⊢Type noacc) -> (⟨ γ ,[ X ] ⟩⊢Type noacc) -> ⟨ γ ⟩⊢Type noacc
  ⨉na : Charge -> (X : ⟨ γ ⟩⊢Type noacc) -> (⟨ γ ,[ X ] ⟩⊢Type acc) -> ⟨ γ ⟩⊢Type acc
  -- D : Charge -> ∀{Γ : Ctx (+- , τ)} -> 𝕠 Γ ⊢Type -> Γ ⊢Type
  Fam : ⟨ γ ⟩⊢ Base (Base NN) , α -> ⟨ γ ⟩⊢Type α

  wk-⟨⟩⊢Type : ∀{β} -> {T : ⟨ γ ⟩⊢Type β} -> ⟨ γ ⟩⊢Type α -> ⟨ γ ,[ T ] ⟩⊢Type α

data ⟨_⟩⊢Var_,_ where
  hidden : {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> ⟨ γ ⟩⊢Var Base A , acc
  zero : ⟨ γ ,[ T ] ⟩⊢Var wk-⟨⟩⊢Type T , noacc
  suc : ∀{β} -> {S : ⟨ γ ⟩⊢Type β} -> ⟨ γ ⟩⊢Var T , α -> ⟨ γ ,[ S ] ⟩⊢Var wk-⟨⟩⊢Type T , α

data ⟨_⟩⊢_,_ where
  var : ⟨ γ ⟩⊢Var T , α -> ⟨ γ ⟩⊢ T , α
  Λnn_ : ∀{T A} -> ⟨ γ ,[ T ] ⟩⊢ A , α -> ⟨ γ ⟩⊢ (⨉nn (+) T A) , α
  -- _,_ : ∀{A B} -> Γ ⊢ A -> Γ ,[ A ] ⊢ B -> Γ ⊢ ⨈ A B
  -- inv : ∀{X} -> Γ ⊢ (D⁺ X) -> Γ ⊢ (D⁻ X)
  -- [_≔_]_ : ∀{E} -> (X : 𝕠 Γ ⊢Type) -> (v : Γ ⋆-Ctx₊ E ⊢ D⁻ )

  -- [_≔_]_ : ∀{τ Γ} {X : 𝕠 {τ = τ} Γ ⊢Type} -> (v : Γ ⊢Var (D⁻ X)) -> (x : Γ ⊢ (D⁺ X)) -> ∀{Y}
  --   -> (Γ [ v ≔ inv x ]) ⊢ Y
  --   -> Γ ⊢ (Y [ ι-subst-Ctx ])
  -- end : Γ ⊢ (D⁺ (Base End))
  -- n0 : ⟨ γ ⟩⊢ Base NN , noacc
  base : {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> Γ ⊢ B -> ⟨ γ ⟩⊢ Base B , noacc

  -- WARNING: this is probably wrong because
  -- this means that we can use all negative
  -- things in Γ
  -- d⁺ : ∀{Γ : Ctx (+- , τ)} -> ∀{A} -> 𝕠 Γ ⊢ A -> Γ ⊢ (D⁺ A)

restore-Type (Base x) = wks-Type _ (wk-Type x)
restore-Type (⨉nn x X Y) = ⨉ x (restore-Type X) (restore-Type Y)
restore-Type (⨉na x X Y) = ⨉ x (restore-Type X) (restore-Type Y)
restore-Type (Fam x) = Fam (restore-Term x)
restore-Type (wk-⟨⟩⊢Type x) = wk-Type (restore-Type x)

restore-Term (Λnn t) = Λ (restore-Term t)
restore-Term (base t) = {!!}
restore-Term (var v) = {!!}

𝓕-Ctx : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> Γ ⊢Ctx₊

𝓕-Type : ⟨ γ ⟩⊢Type noacc -> [ 𝓕-Ctx γ ]⊢Type
𝓕-Term : ⟨ γ ⟩⊢ T , noacc -> [ 𝓕-Ctx γ ]⊢ 𝓕-Type T
𝓕-Var : ⟨ γ ⟩⊢Var T , noacc -> [ 𝓕-Ctx γ ]⊢ 𝓕-Type T

𝓕-Ctx {Γ = Γ} [] = [] -- when we arrive at the bottom, we skip the A, but take the Γ
𝓕-Ctx (_,[_] γ {acc} T) = 𝓕-Ctx γ
𝓕-Ctx (_,[_] γ {noacc} T) = 𝓕-Ctx γ ,[ 𝓕-Type T ]

𝓕-Type {γ = γ} (Base x) = wks-Type (𝓕-Ctx γ) x
𝓕-Type (⨉nn x T T₁) = ⨉ x (𝓕-Type T) (𝓕-Type T₁)
𝓕-Type (Fam x) = Fam (𝓕-Term x)
𝓕-Type (wk-⟨⟩⊢Type {β = acc} x) = 𝓕-Type x
𝓕-Type (wk-⟨⟩⊢Type {β = noacc} x) = wk-Type (𝓕-Type x)

𝓕-Term (Λnn t) = Λ 𝓕-Term t
𝓕-Term (base t) = {!!}
𝓕-Term (var v) = 𝓕-Var v

𝓕-Var zero = var zero
𝓕-Var (suc {β = acc} x) = 𝓕-Var x
𝓕-Var (suc {β = noacc} x) = wk-Term (𝓕-Var x)

𝓖-Ctx : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> Γ ,[ A ] ⋆-Ctx₊ (wk-Ctx₊ (𝓕-Ctx γ)) ⊢Ctx₊
𝓖-Type : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> (T : ⟨ γ ⟩⊢Type acc) -> [ 𝓖-Ctx γ ]⊢Type

_,𝓕[_] : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> [ 𝓕-Ctx γ ]⊢Type -> Γ ,[ A ] ⊢Ctx₊
_,𝓕[_] γ A' = wk-Ctx₊ (𝓕-Ctx γ) ,[ wk-Type,ind (𝓕-Ctx γ) A' ] ⋆-Ctx₊₂ (wk-Ctx₊ (𝓖-Ctx γ))


real : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> [ 𝓕-Ctx γ ]⊢Type -> [ 𝓖-Ctx γ ]⊢Type
real γ A = wks-Type (𝓖-Ctx γ) (wk-Type,ind (𝓕-Ctx γ) A)

real₂ : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> (γ : ⟨ E ⟩⊢Ctx) -> (A : [ 𝓕-Ctx γ ]⊢Type) -> [ γ ,𝓕[ A ] ]⊢Type -> [ 𝓖-Ctx γ ,[ real γ A ] ]⊢Type
real₂ = {!!}

𝓖-Term-aa : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> {T : ⟨ γ ⟩⊢Type acc} -> ⟨ γ ⟩⊢ T , acc -> [ 𝓖-Ctx γ ]⊢ 𝓖-Type T
𝓖-Term-na : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> {T : ⟨ γ ⟩⊢Type noacc} -> ⟨ γ ⟩⊢ T , acc -> [ 𝓖-Ctx γ ]⊢ real γ (𝓕-Type T)

𝓖-Var-na : {Γ : Ctx L} -> ∀{A} -> {E : Γ ,[ A ] ⊢Ctx₊} -> {γ : ⟨ E ⟩⊢Ctx} -> {T : ⟨ γ ⟩⊢Type noacc} -> ⟨ γ ⟩⊢Var T , acc -> [ 𝓖-Ctx γ ]⊢ real γ (𝓕-Type T)

𝓖-Ctx [] = []
𝓖-Ctx (_,[_] γ {acc} T) = 𝓖-Ctx γ ,[ 𝓖-Type T ]
𝓖-Ctx (_,[_] γ {noacc} T) = wk-Ctx₊ (𝓖-Ctx γ)

𝓖-Type {γ = γ} (⨉na x A B) =
  let A' = (real γ (𝓕-Type A))
      B' = real₂ γ (𝓕-Type A) (𝓖-Type B)
  in ⨉ x A' B'
𝓖-Type {γ = γ} (Fam x) = Fam (𝓖-Term-na {γ = γ} x)
𝓖-Type (wk-⟨⟩⊢Type {β = acc} T) = let T' = 𝓖-Type T in wk-Type T'
𝓖-Type {γ = γ ,[ _ ]} (wk-⟨⟩⊢Type {β = noacc} T) = let T' = 𝓖-Type T in wk-Type,ind (𝓖-Ctx γ) T'

𝓖-Term-na {γ = γ} (var x) = 𝓖-Var-na x
𝓖-Term-na {γ = γ} (Λnn t) = let t' = 𝓖-Term-na t in Λ {!!} -- NOTE: TODO: Here we probably have to reorder the variables (we need ... ⋆ 𝓖-Ctx γ ,[ wks-Type (𝓖-Ctx γ) ZZ] -- and we have ... ,[ ZZ ] ⋆ wk-Ctx₊ (𝓖-Ctx γ))

𝓖-Var-na {γ = γ} hidden = wks-Term (𝓖-Ctx γ) (wks-Term (wk-Ctx₊ (𝓕-Ctx γ)) (var zero))
𝓖-Var-na {γ = (γ ,[ _ ])} (suc {β = acc} x) = let t = 𝓖-Var-na {γ = γ} x in wk-Term t
𝓖-Var-na {γ = (γ ,[ _ ])} (suc {β = noacc} x) = let t = 𝓖-Var-na {γ = γ} x in let t' = wk-Term-ind (𝓖-Ctx γ) t in t'


-- Filtering for splitting
{-
filter-Ctx₊ : (E : Γ ,[ A ] ⊢Ctx₊) -> ⟨ E ⟩⊢Ctx
filter-Type : ∀ E -> (Γ ,[ A ] ⋆-Ctx₊ E ⊢Type) -> ∑ λ α -> (⟨ filter-Ctx₊ E ⟩⊢Type α)
filter-Term : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢ A) -> ∑ λ β -> (⟨ filter-Ctx₊ E ⟩⊢ snd (filter-Type E A) , β)

filter-Ctx₊ [] = []
filter-Ctx₊ (E ,[ x ]) = filter-Ctx₊ E ,[ {!snd (filter-Type E x)!} ]



filter-Var : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢Var A) -> ∑ λ β -> (⟨ filter-Ctx₊ E ⟩⊢Var snd (filter-Type E A) , β)
filter-Var [] zero = acc , {!hidden!}
filter-Var [] (suc x) = {!!}
filter-Var (E ,[ x₁ ]) zero = {!!}
filter-Var (E ,[ x₁ ]) (suc x) = {!!}
-}




-- Splitting end
------------------------------------------------------------------------


{-
split-Ctx₊ : Γ ,[ A ] ⊢Ctx₊ -> ∑ λ (E₀ : Γ ⊢Ctx₊) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E₀ ⊢Ctx₊

[_]⊢Type : (E : Γ ⊢Ctx₊) -> 𝒰₀
[_]⊢Type E = _ ⋆-Ctx₊ E ⊢Type

-- Same principle as in weakening
{-# TERMINATING #-}
𝓕 : (E : Γ ,[ A ] ⊢Ctx₊) -> Γ ⊢Ctx₊
𝓕 E = fst (split-Ctx₊ E)

∥_∥ : Γ ,[ A ] ⊢Ctx₊ -> Γ ,[ A ] ⊢Ctx₊
∥_∥ E =  wk-Ctx₊ (𝓕 E) ⋆-Ctx₊₂ snd (split-Ctx₊ E)

_,𝓕[_] : (E : Γ ,[ A ] ⊢Ctx₊) -> [ 𝓕 E ]⊢Type -> Γ ,[ A ] ⊢Ctx₊
_,𝓕[_] E A' = wk-Ctx₊ (𝓕 E) ,[ wk-Type,ind (𝓕 E) A' ] ⋆-Ctx₊₂ (wk-Ctx₊ (snd (split-Ctx₊ E)))

-}

{-
-- split-Type : ∀ E -> Γ ,[ A ] ⋆-Ctx₊ E ⊢Type -> (_ ⋆-Ctx₊ snd (split-Ctx₊ E) ⊢Type) +-𝒰 (Γ ⋆-Ctx₊ fst (split-Ctx₊ E) ⊢Type)
split-Type : ∀ (E : Γ ,[ A ] ⊢Ctx₊) -> [ E ]⊢Type -> [ ∥ E ∥ ]⊢Type +-𝒰 [ 𝓕 E ]⊢Type

real : ∀ (E : Γ ,[ A ] ⊢Ctx₊) -> [ 𝓕 E ]⊢Type -> [ ∥ E ∥ ]⊢Type
real E X = {!!}

real₂ : (E : Γ ,[ A ] ⊢Ctx₊) -> (A : [ 𝓕 E ]⊢Type) -> [ E ,𝓕[ A ] ]⊢Type -> [ ∥ E ∥ ,[ real E A ] ]⊢Type
real₂ = {!!}

[_]⊢_ : ∀ (E : Γ ,[ A ] ⊢Ctx₊) -> [ E ]⊢Type -> 𝒰₀
[ E ]⊢ X = case split-Type E X of (λ X -> _ ⊢ X) (λ Y -> (_ ⊢ real E Y) +-𝒰 (_ ⊢ Y))




split-Ctx₊ [] = [] , []
split-Ctx₊ (E ,[ x ]) = let (E₀ , E₁) = split-Ctx₊ E in case (split-Type E x) of
                                                        (λ Z -> E₀        , (E₁ ,[ Z ])) -- not successful (contains A)
                                                        (λ Y -> E₀ ,[ Y ] , wk-Ctx₊ E₁)  -- successfull (does not contain A)

split-Type E (Base x) = just (Base x)
split-Type E (⨉ x A B) with split-Type E A | split-Type (E ,[ A ]) B
... | just (A') | just (B') = just (⨉ x A' B')
... | just (A') | left B' = left (⨉ x (real E A') (real₂ E A' B'))
... | left A | just B = left (⨉ x A (wk-Type (real E B)))
... | left A | left B = left (⨉ x A B)

-- case split-Type E A of
--                                 (λ A' -> case split-Type (E ,[ A ]) B of (λ B' -> left (⨉ x A' {!!})) {!!})
--                                 (λ A' -> {!!})
split-Type E (D x X) = {!!}
split-Type E (Fam x) = {!!}
split-Type E ℍ = {!!}

split-Term : ∀ (E : Γ ,[ A ] ⊢Ctx₊) -> {X : [ E ]⊢Type} -> (x : _ ⊢ X) -> [ E ]⊢ X
split-Term E (var x) = {!!}
split-Term E {X = ⨉ c A B} (Λ x) with split-Type E A | split-Type (E ,[ _ ]) B -- | split-Term (E ,[ _ ]) x
... | left A' | B' = {!!}
... | just A' | left B' = {!!}
... | just A' | just B' with split-Term (E ,[ _ ]) x
... | t = {!!}
split-Term E (inv x) = {!!}
split-Term E end = {!!}
split-Term E n0 = {!!}
split-Term E (d⁺ x) = {!!}

-}

-- filter-Type : ∀ E -> Γ ,[ A ] ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ filter-Ctx₊ E ⊢Type)
-- filter-Term : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢ A) -> Maybe (_ ⊢ filter-Type E A)
-- filter-Var : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢Var A) -> Maybe (_ ⊢ filter-Type E A)

-- End Splitting
------------------------------------------------------------------------


{-

------------------------------------------------------------------------
-- Filtering






filter-Ctx₊ : Γ ,[ A ] ⊢Ctx₊ -> Γ ⊢Ctx₊
filter-Type : ∀ E -> Γ ,[ A ] ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ filter-Ctx₊ E ⊢Type)
filter-Term : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢ A) -> Maybe (_ ⊢ filter-Type E A)
filter-Var : ∀ E -> {A : Γ ,[ A ] ⋆-Ctx₊ E ⊢Type} -> (_ ⊢Var A) -> Maybe (_ ⊢ filter-Type E A)

filter-Ctx₊ [] = []
filter-Ctx₊ (E ,[ x ]) = filter-Ctx₊ E ,[ filter-Type E x ]

β-𝕠-filter-Ctx₊ : ∀{E : Γ ,[ A ] ⊢Ctx₊} -> 𝕠-Ctx₊ (filter-Ctx₊ E) ≣ filter-Ctx₊ (𝕠-Ctx₊ E)
β-𝕠-filter-Ctx₊ = {!!}

{-# REWRITE β-𝕠-filter-Ctx₊ #-}

β-filter-wk-Type : filter-Type {A = A} [] (wk-Type B) ≣ B
β-filter-wk-Type = {!!}

σ-filter-wk-Type : ∀{E : Γ ,[ A ] ⊢Ctx₊} -> ∀{B C} -> filter-Type (E ,[ C ]) (wk-Type B) ≣ wk-Type (filter-Type E B)
σ-filter-wk-Type = {!!}

{-# REWRITE β-filter-wk-Type σ-filter-wk-Type #-}

filter-Var [] zero = nothing -- if the zero'th var is used, we have to delete this term
filter-Var [] (suc v) = just (var v)
filter-Var (E ,[ x ]) zero = just (var zero)
filter-Var (E ,[ x ]) (suc v) = map-Maybe (wk-Term _) (filter-Var E v)

filter-Type E (Base x) = (Base x)
filter-Type E (⨉ x A B) = ⨉ x (filter-Type E A) (filter-Type (E ,[ A ]) B)
filter-Type E (D x X) = D x (filter-Type (𝕠-Ctx₊ E) X)
filter-Type E (Fam x) with (filter-Term E x)
... | left x' = ℍ
... | just x' = Fam x'
filter-Type E ℍ = ℍ

filter-Term E (var x) = filter-Var E x
filter-Term E (Λ t) = map-Maybe Λ_ (filter-Term (E ,[ _ ]) t) -- Λ filter-Term (E ,[ _ ]) t
filter-Term E (inv t) = map-Maybe inv (filter-Term E t) -- inv (filter-Term E t)
filter-Term E end = just end
filter-Term E n0 = just n0
filter-Term E (d⁺ t) = {!map-Maybe d⁺ (filter-Term (𝕠-Ctx₊ E) t)!}


-- End Filtering
------------------------------------------------------------------------



_[_]-Ctx₊ [] σ = []
_[_]-Ctx₊ (E ,[ x ]) σ = (E [ σ ]-Ctx₊) ,[ under E by x [ σ ]-Type ]



_[_]-Type X σ = under [] by X [ σ ]-Type


β-wk-σ : ∀{Γ Δ : Ctx L} -> {A : Δ ⊢Type} -> (E : Γ ⊢Ctx₊) -> {B : Γ ⊢Type} -> {σ : Γ ⋆-Ctx₊ E ⇛♮ Δ} -> under [] by A [ wk-⇛♮-ind {A = B} E σ ]-Type  ≣ wk-Type,ind E (A [ σ ]-Type)
β-wk-σ = {!!}

β-wk-σ-[] : {B : Γ ⊢Type} -> {σ : Γ ⇛♮ Δ} -> under [] by A [ wk-⇛♮-ind {A = B} [] σ ]-Type ≣ wk-Type,ind [] (A [ σ ]-Type)
β-wk-σ-[] = β-wk-σ []

{-# REWRITE β-wk-σ β-wk-σ-[] #-}




wk-⇛♮-ind E ε = ε
wk-⇛♮-ind E (σ , x) = wk-⇛♮-ind E σ ,
  let XX = wk-Term-ind E _ x
  in ⟨ _ ⊢⇂ (sym-≣ (β-wk-σ E {σ = σ})) ⇃⟩ XX

wk-⇛♮ : ∀{A} -> Γ ⇛♮ Δ -> Γ ,[ A ] ⇛♮ Δ
wk-⇛♮ σ = wk-⇛♮-ind [] σ






β-id-Type : under [] by A [ id-⇛♮ ]-Type ≣ A
β-id-Type = {!!}

{-# REWRITE β-id-Type #-}

β⁻¹-id-Type : A ≣ A [ id-⇛♮ ]-Type
β⁻¹-id-Type = sym-≣ β-id-Type

id-⇛♮ {Γ = []} = ε
id-⇛♮ {Γ = Γ ,[ x ]} = wk-⇛♮ id-⇛♮ , var zero

-- This one comes from β-id-Type (and others?)
β-wk : ∀{B} -> A [ wk-⇛♮ {A = B} id-⇛♮ ]-Type ≣ wk-Type,ind [] A
β-wk = refl-≣




lift-sub : (σ : Γ ⇛♮ Δ) -> Γ ,[ A [ σ ]-Type ] ⇛♮ Δ ,[ A ]
lift-sub {Γ = Γ} {A = A} σ = wk-⇛♮ σ ,
  let X : (Γ ,[ A [ σ ]-Type ]) ⊢ (wk-Type (A [ σ ]-Type))
      X = var zero
  in X



-- {-# TERMINATING #-}
β-comp-Ctx₊ : {E : Δ ,[ A ] ⊢Ctx₊} -> {σ : Γ ⇛♮ Δ} {x : Γ ⊢ (A [ σ ]-Type)} -> ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊) ≣ E [ σ , x ]-Ctx₊
β-comp-Ctx₊ = {!!}


{-# REWRITE β-comp-Ctx₊ #-}


-- sub : ∀ i -> Γ ⇂ i ⊢ Γ ＠ i -> Γ ⇂ i ⇛♮ Γ ⇂ i ,[ Γ ＠ i ]
-- sub zero x = ♮-⇛ id , {!!}
-- sub (suc i) x = sub i x

{-
_↾_ : (Γ : Ctx L) -> (i : Γ ⊢Var) -> Γ ⇂ i ,[ Γ ＠ i ] ⊢Ctx₊

η-⇂↾ : ∀{i} -> (Γ ⇂ i ,[ Γ ＠ i ]) ⋆-Ctx₊ (Γ ↾ i) ≣ Γ

(Γ ,[ A ]) ↾ zero = []
(Γ ,[ A ]) ↾ suc i = (Γ ↾ i) ,[ transp-≣ (cong-≣ (λ ξ -> ξ ⊢Type) (sym-≣ η-⇂↾)) A  ]

η-⇂↾ {Γ = Γ ,[ A ]} {i = zero} = refl-≣
η-⇂↾ {Γ = Γ ,[ A ]} {i = suc i} with ((Γ ⇂ i ,[ Γ ＠ i ]) ⋆-Ctx₊ (Γ ↾ i)) | η-⇂↾ {Γ = Γ} {i = i}
... | .Γ | refl-≣ = refl-≣

{-# REWRITE η-⇂↾ #-}

PP1 : {A : 𝒰 𝑖} {a : A} -> (p : a ≣ a) -> p ≣ refl-≣
PP1 refl-≣ = refl-≣

Test : ∀{Γ : Ctx L} {i} -> η-⇂↾ {Γ = Γ} {i = i} ≣ refl-≣
Test = PP1 η-⇂↾

{-# REWRITE Test #-}

-}


split-front-Ctx₊ : {A : Γ ⊢Type} -> ∀{E} {σ : Δ ⇛♮ Γ} -> ([ A ]Ctx₊∷ E) [ σ ]-Ctx₊ ≣ [ A [ σ ]-Type ]Ctx₊∷ (E [ lift-sub σ ]-Ctx₊)
split-front-Ctx₊ = {!!}

{-# REWRITE split-front-Ctx₊ #-}




-- su-Type : ∀ i -> (x : Γ ⇂ i ⊢ Γ ＠ i) -> Γ ⊢Type -> ((Γ ⇂ i) ⋆-Ctx₊ ((Γ ↾ i) [ sub i x ]-Ctx₊)) ⊢Type
-- su-Type i x (Base x₁) = Base x₁
-- su-Type i x (⨉ c A B) = ⨉ c (su-Type i x A) let B' = su-Type (suc i) x B in {!!}
-- su-Type i x (D x₁ X) = {!!}
-- su-Type i x (Fam x₁) = {!!}

-- 2Type⦅_∣_⦆_ : ∀ E -> (x : Γ ⋆-Ctx₊ wk-Ctx₊ A E ⊢ ?) -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ (Ctx⦅ x ⦆ E)) ⊢Type


------------------------------------------------------------------------
-- Substitution

-- Ctx⦅_∣_⦆ : {Γ : Ctx L} -> ∀{A} -> (E : (Γ ,[ A ]) ⊢Ctx₊) -> (x : Γ ⋆-Ctx₊ filter-Ctx₊ E ⊢ wks-Type _ A) -> Γ ⊢Ctx₊

-- β-comp-Ctx₊₂ : {E : Δ ,[ A ] ⊢Ctx₊} -> {σ : Γ ⇛♮ Δ} {x : Γ ⊢ (A [ σ ]-Type)} -> Ctx⦅ x ⦆ (E [ lift-sub σ ]-Ctx₊) ≣ E [ σ , x ]-Ctx₊

-- Type⦅_∣_⦆_ : ∀ E x -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ (Ctx⦅ E ∣ x ⦆)) ⊢Type

-- su-Type₂ : ∀{E} -> (x : Γ ⊢ A) -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ Ctx⦅ x ⦆ E) ⊢Type
-- su-Type₂ {E = E} x T = Type⦅_∣_⦆_ x E T


-- infixr 90 Type⦅_∣_⦆_ Term⦅_∣_⦆_ Ctx⦅_∣_⦆

-- Term⦅_∣_⦆_ : ∀ E x -> {A : (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type} -> (t : _ ⊢ A) -> _ ⊢ Type⦅ E ∣ x ⦆ A

-- Ctx⦅ [] ∣ x ⦆ = []
-- Ctx⦅ E ,[ A ] ∣ x ⦆ = Ctx⦅ E ∣ {!!} ⦆ ,[ {!!} ]

-- Ctx⦅ x ⦆ [] = []
-- Ctx⦅ x ⦆ (E ,[ A ]) = Ctx⦅ x ⦆ E ,[ Type⦅ x ∣ E ⦆ A ]

{-
β-𝕠-Ctx₊ : ∀{x : Γ ⊢ A} {E} -> 𝕠-Ctx₊ (Ctx⦅ x ⦆ E) ≣ Ctx⦅ 𝕠-Term x ⦆ (𝕠-Ctx₊ E)
β-𝕠-Ctx₊ {E = []} = refl-≣
β-𝕠-Ctx₊ {E = E ,[ x ]} = {!!}

{-# REWRITE β-𝕠-Ctx₊ #-}


Type⦅_∣_⦆_ x E (Base x₁) = Base x₁
Type⦅_∣_⦆_ x E (⨉ c A B) = ⨉ c (su-Type₂ {E = E} x A) let B' = su-Type₂ {E = E ,[ A ]} x B in B'
Type⦅_∣_⦆_ x E (D c A) = D c (Type⦅ 𝕠-Term x ∣ 𝕠-Ctx₊ E ⦆ A)
Type⦅_∣_⦆_ x E (Fam n) = Fam (Term⦅ x ∣ E ⦆ n)
Type⦅_∣_⦆_ x E (ℍ) = ℍ


β-comp-Ctx₊₂ = {!!}

-- σ-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{E B} -> Type⦅ x ∣ E ,[ B ] ⦆ (wk-Type B) ≣ wk-Type (Type⦅ x ∣ E ⦆ B)
σ-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{E X B} -> Type⦅ x ∣ E ,[ X ] ⦆ (wk-Type B) ≣ wk-Type (Type⦅ x ∣ E ⦆ B)
σ-su-wk-Type = {!!}

β-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{B} -> Type⦅ x ∣ [] ⦆ (wk-Type B) ≣ B
β-su-wk-Type = {!!}

{-# REWRITE β-comp-Ctx₊₂ σ-su-wk-Type β-su-wk-Type #-}

Var⦅_∣_⦆_ : (x : Γ ⊢ A) -> ∀ E -> {A : (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type} -> (v : _ ⊢Var A) -> _ ⊢ Type⦅ x ∣ E ⦆ A
Var⦅ x ∣ [] ⦆ zero = x
Var⦅ x ∣ [] ⦆ suc v = var v
Var⦅_∣_⦆_ {Γ = Γ} x (E ,[ B ]) zero = var zero
Var⦅ x ∣ E ,[ B ] ⦆ suc v = wk-Term _ (Var⦅ x ∣ E ⦆ v)

Term⦅ x ∣ E ⦆ var v = Var⦅ x ∣ E ⦆ v
Term⦅ x ∣ E ⦆ (Λ t) = Λ (Term⦅ x ∣ E ,[ _ ] ⦆ t)
Term⦅ x ∣ E ⦆ inv t = let tt = Term⦅ x ∣ E ⦆ t in inv tt
Term⦅ x ∣ E ⦆ end = end
Term⦅ x ∣ E ⦆ n0 = n0
Term⦅ x ∣ E ⦆ d⁺ t = {!!}



under_by_[_]-Type E X ε = {!!}
under_by_[_]-Type {Γ = Γ} E X (_,_ {A = A} σ x) =
  let Y = under_by_[_]-Type ([ A ]Ctx₊∷ E) X σ

      -- X2 : (Γ ⋆-Ctx₊ ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊)) ⊢Type
      -- X2 = {!!} -- su-Type₂ {E = (E [ lift-sub σ ]-Ctx₊)} x Y

      X3 = su-Type₂ {E = (E [ lift-sub σ ]-Ctx₊)} x Y

      -- p : (Γ ⋆-Ctx₊ ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊)) ⊢Type ≣ (Γ ⋆-Ctx₊ (E [ σ , x ]-Ctx₊)) ⊢Type
      -- p = cong-≣ (λ ξ -> Γ ⋆-Ctx₊ ξ ⊢Type) (β-comp-Ctx₊ {E = E} {σ = σ} {x = x})

      -- Res : (Γ ⋆-Ctx₊ (E [ σ , x ]-Ctx₊)) ⊢Type
      -- Res = transp-≣ p X2
  in X3






-}
-}
-}
-}
-}
