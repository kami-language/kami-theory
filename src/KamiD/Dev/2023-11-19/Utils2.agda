
{-# OPTIONS --rewriting #-}

module KamiD.Dev.2023-11-19.Utils2 where

open import Agda.Builtin.Equality.Rewrite
open import Agora.Conventions hiding (Σ ; toℕ)
open import Agora.Data.Power.Definition
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_!)
open import Data.List using (List ; [] ; _∷_)
open import Data.String hiding (_≈_)
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Reflects

open import KamiD.Dev.2023-11-19.Core
open import KamiD.Dev.2023-11-19.Rules
-- open import KamiD.Dev.2023-11-19.Utils.Context

{-# REWRITE +-suc +-zero #-}


findVar : (Γ : Ctx) -> (x : Name) -> Maybe (Fin ∣ Γ ∣)
findVar [] x = nothing
findVar (Γ ,[ y ∶ x₂ ]) x with (Data.Nat._≟_ x y).does
... | false = map-Maybe suc (findVar Γ x)
... | true = just zero

--------------------------------------------------------------------
-- Kinds

_＠-Kind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Kind
(_,[_∶_] Γ x {k = k} A) ＠-Kind zero = k
(Γ ,[ x ∶ x₁ ]) ＠-Kind suc i = Γ ＠-Kind i

-- _＠-Kind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Kind
-- Γ ＠-Kind i = head-Kind (Γ ©ᵣ i)

instance
  hasNotation-＠:Kind : hasNotation-＠ Ctx (λ Γ -> Fin ∣ Γ ∣) (λ _ _ -> Kind)
  hasNotation-＠:Kind = record { _＠_ = λ Γ i -> Γ ＠-Kind i }


instance
  isKind:＠-Kind : ∀{Γ i} -> Γ ⊢ i isKind (Γ ＠ i)
  isKind:＠-Kind {Γ ,[ x ∶ x₁ ]} {zero} = zero
  isKind:＠-Kind {Γ ,[ x₂ ∶ x₃ ]} {suc i} = suc isKind:＠-Kind

instance
  hasNotation-refine:isKind : ∀{Γ} -> hasNotation-refine (Fin ∣ Γ ∣) (λ i -> Γ ⊢ i isKind (Γ ＠ i))
  hasNotation-refine:isKind = record { refine = λ i -> it }

--------------------------------------------------------------------
-- Helpers

-- ‵ : ∀{Γ k} -> (x : Name)
--      -> {{_ : findVar Γ x ≣ just k }}
--      -> Fin ∣ Γ ∣
-- ‵ {Γ = Γ} x {{P}} with findVar Γ x | P
-- ... | just k | refl-≣ = k


-- get : ∀{Γ} -> (i : Fin ∣ Γ ∣) -> Γ ⊢ i isKind (Γ ＠ i)
-- get i = it

‵ : ∀{Γ k} -> (x : Name) -> {{_ : findVar Γ x ≣ just k}} -> Γ ⊢ k isKind (Γ ＠ k)
‵ {Γ} {k} x {{P}} with findVar Γ x | P
... | just x₁ | refl-≣ = it


