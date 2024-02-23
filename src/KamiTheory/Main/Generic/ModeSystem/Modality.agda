
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.Modality where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition

open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition



---------------------------------------------
-- A modality is a mode morphism with arbitrary
-- domain and codomain

record SomeModeHom (M : ModeSystem 𝑖) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
  constructor _↝_∋_
  field dom : Mode M
  field cod : Mode M
  field hom : ModeHom M dom cod

infixl 40 _↝_∋_

open SomeModeHom public

data Modality (M : ModeSystem 𝑖) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
  id : Modality M
  fail : Modality M
  incl : SomeModeHom M -> Modality M



module _ {M : ModeSystem 𝑖} where

  _◆-Modality_ : Modality M -> Modality M -> Modality M
  id ◆-Modality η = η
  fail ◆-Modality η = fail
  incl x ◆-Modality id = incl x
  incl x ◆-Modality fail = fail
  incl (a ↝ b ∋ μ) ◆-Modality incl (c ↝ d ∋ η) with b ≟ c
  ... | no _ = fail
  ... | yes refl = incl (_ ↝ _ ∋ (μ ◆ η))

  ------------------------------------------------------------------------
  -- Decidability

  ---------------------------------------------
  -- Modalities have decidable equality


  _≟-SomeModeHom_ : (μ η : SomeModeHom M) -> isDecidable (μ ≡ η)
  (m₁ ↝ n₁ ∋ μ) ≟-SomeModeHom (m₂ ↝ n₂ ∋ η) with m₁ ≟ m₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with n₁ ≟ n₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with μ ≟ η
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:SomeModeHom : hasDecidableEquality (SomeModeHom M)
    hasDecidableEquality:SomeModeHom = record { _≟_ = _≟-SomeModeHom_ }

  decide-≡-Modality : (μ η : Modality M) -> isDecidable (μ ≡ η)
  decide-≡-Modality id id = yes refl
  decide-≡-Modality id fail = no λ {()}
  decide-≡-Modality id (incl x) = no λ {()}
  decide-≡-Modality fail id = no λ {()}
  decide-≡-Modality fail fail = yes refl
  decide-≡-Modality fail (incl x) = no λ {()}
  decide-≡-Modality (incl x) id = no λ {()}
  decide-≡-Modality (incl x) fail = no λ {()}
  decide-≡-Modality (incl x) (incl y) with x ≟ y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Modality : hasDecidableEquality (Modality M)
    hasDecidableEquality:Modality = record { _≟_ = decide-≡-Modality }



