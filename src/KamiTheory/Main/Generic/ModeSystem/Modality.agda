
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Generic.ModeSystem.Modality where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.Definition




---------------------------------------------
-- A modality is a mode morphism with arbitrary
-- domain and codomain

record Modality (G : 2Graph 𝑖) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
  constructor _↝_∋_
  field dom : Mode G
  field cod : Mode G
  field hom : ModeHom G dom cod

infixl 40 _↝_∋_

open Modality public



------------------------------------------------------------------------
-- Decidability

module _ {G : 2Graph 𝑖} where

  ---------------------------------------------
  -- ModeHoms have decidable equality

  _≟-ModeHom_ : ∀{m n} -> (k l : ModeHom G m n) -> isDecidable (k ≡ l)
  _≟-ModeHom_ id id = yes refl-≡
  _≟-ModeHom_ id (x ⨾ l) = no (λ ())
  _≟-ModeHom_ (x ⨾ k) id = no (λ ())
  _≟-ModeHom_ (_⨾_ {n = n} x k) (_⨾_ {n = n₁} y l) with n ≟ n₁
  -- _≟-ModeHom_ (_⨾_ {n = n} x k) (_⨾_ {n = n₁} y l) with decide-≡-Point n n₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with x ≟ y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with k ≟-ModeHom l
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:ModeHom : ∀{m n} -> hasDecidableEquality (ModeHom G m n)
    hasDecidableEquality:ModeHom = record { _≟_ = _≟-ModeHom_ }


  ---------------------------------------------
  -- Modalities have decidable equality


  _≟-Modality_ : (μ η : Modality G) -> isDecidable (μ ≡ η)
  (m₁ ↝ n₁ ∋ μ) ≟-Modality (m₂ ↝ n₂ ∋ η) with m₁ ≟ m₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with n₁ ≟ n₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with μ ≟ η
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Modality : hasDecidableEquality (Modality G)
    hasDecidableEquality:Modality = record { _≟_ = _≟-Modality_ }




