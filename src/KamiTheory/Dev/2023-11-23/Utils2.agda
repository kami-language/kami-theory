
{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module KamiD.Dev.2023-11-23.Utils2 where

open import Agda.Builtin.Equality.Rewrite
open import Agora.Conventions hiding (Σ ; toℕ)
open import Agora.Data.Power.Definition
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_!)
open import Data.List using (List ; [] ; _∷_)
open import Data.String hiding (_≈_)
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Reflects

open import KamiD.Dev.2023-11-23.Core
open import KamiD.Dev.2023-11-23.Rules
-- open import KamiD.Dev.2023-11-23.Utils.Context

{-# REWRITE +-suc +-zero #-}


findVar : (Γ : Ctx) -> (x : Name) -> Maybe (Fin ∣ Γ ∣)
findVar [] x = nothing
findVar (Γ ,[ y ∶ x₂ ]) x with (Data.Nat._≟_ x y).does
... | false = map-Maybe suc (findVar Γ x)
... | true = just zero

--------------------------------------------------------------------
-- Kinds

-- wk-Kind : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ⊢Kind -> Γ ,[ x ∶ A ] ⊢Kind
-- wk-Shapes : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ⊢Shapes -> Γ ,[ x ∶ A ] ⊢Shapes
-- wk-Type : ∀{Γ x k j} -> {A : Γ ⊢Type k} -> Γ ⊢Type j -> Γ ,[ x ∶ A ] ⊢Type wk-Kind j

-- wk-Kind 𝑆 = 𝑆
-- wk-Kind (𝑇 x) = 𝑇 (wk-Shapes x)
-- wk-Kind (⩝ x ∶ A , t) = ⩝ x ∶ wk-Type A , {!wk-Kind t!}

-- wk-Shapes [] = []
-- wk-Shapes (S & x) = wk-Shapes S & suc x

-- wk-Type = {!!}


_＠-Kind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Γ ⊢Kind
(_,[_∶_] Γ x {k = k} A) ＠-Kind zero = weak k
(Γ ,[ x ∶ x₁ ]) ＠-Kind suc i = weak (Γ ＠-Kind i)


-- _＠-Kind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Kind
-- Γ ＠-Kind i = head-Kind (Γ ©ᵣ i)

instance
  hasNotation-＠:Kind : hasNotation-＠ Ctx (λ Γ -> Fin ∣ Γ ∣) (λ Γ _ -> Γ ⊢Kind)
  hasNotation-＠:Kind = record { _＠_ = λ Γ i -> Γ ＠-Kind i }

instance
  isKind:＠-Kind : ∀{Γ i} -> Γ ⊢ i isKind (Γ ＠ i)
  isKind:＠-Kind {Γ ,[ x ∶ x₁ ]} {zero} = zero
  isKind:＠-Kind {Γ ,[ x₂ ∶ x₃ ]} {suc i} = suc isKind:＠-Kind

-- instance
--   hasNotation-refine:isKind : ∀{Γ} -> hasNotation-refine (Fin ∣ Γ ∣) (λ i -> Γ ⊢ i isKind (Γ ＠ i))
--   hasNotation-refine:isKind = record { refine = λ i -> it }

{-
--------------------------------------------------------------------
-- Helpers

-- ‵ : ∀{Γ k} -> (x : Name)
--      -> {{_ : findVar Γ x ≣ just k }}
--      -> Fin ∣ Γ ∣
-- ‵ {Γ = Γ} x {{P}} with findVar Γ x | P
-- ... | just k | refl-≣ = k


-- get : ∀{Γ} -> (i : Fin ∣ Γ ∣) -> Γ ⊢ i isKind (Γ ＠ i)
-- get i = it

-}

‵ : ∀{Γ k} -> (x : Name) -> {{_ : findVar Γ x ≣ just k}} -> Γ ⊢ k isKind (Γ ＠ k)
‵ {Γ} {k} x {{P}} with findVar Γ x | P
... | just x₁ | refl-≣ = it


-- getIsShape : ∀ Γ k -> Maybe (Γ ⊢ k isKind 𝑆)
-- getIsShape (Γ ,[ x ∶ x₁ ]) (suc k) = map-Maybe suc (getIsShape Γ k)
-- getIsShape (_,[_∶_] Γ x {𝑆} x₁) zero = just zero
-- getIsShape (_,[_∶_] Γ x {⩝ x₂ ∶ A , k} x₁) zero = nothing

-- ‵ : ∀{Γ k p} -> (x : Name) -> {{_ : findVar Γ x ≣ just k}}
--         -> {{_ : getIsShape Γ k ≣ just p}}
--         -> Γ ⊢ k isKind 𝑆
-- ‵ {Γ} {k} x {{P}} {{Q}} with findVar Γ x | P
-- ... | just x₁ | refl-≣ with getIsShape Γ k | Q
-- ... | just x₂ | refl-≣ = x₂


