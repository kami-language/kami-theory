
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.Modality where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition

open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition



---------------------------------------------
-- A modality is a mode morphism with arbitrary
-- domain and codomain

record Modality (M : ModeSystem 𝑖) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
  constructor _↝_∋_
  field dom : Mode M
  field cod : Mode M
  field hom : ModeHom M dom cod

infixl 40 _↝_∋_

open Modality public



------------------------------------------------------------------------
-- Decidability

module _ {M : ModeSystem 𝑖} where


  ---------------------------------------------
  -- Modalities have decidable equality


  _≟-Modality_ : (μ η : Modality M) -> isDecidable (μ ≡ η)
  (m₁ ↝ n₁ ∋ μ) ≟-Modality (m₂ ↝ n₂ ∋ η) with m₁ ≟ m₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with n₁ ≟ n₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with μ ≟ η
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Modality : hasDecidableEquality (Modality M)
    hasDecidableEquality:Modality = record { _≟_ = _≟-Modality_ }




