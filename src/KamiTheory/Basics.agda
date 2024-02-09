
module KamiTheory.Basics where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base
open import Agda.Builtin.Nat using (Nat; zero; suc)

_↯_ : ∀ {𝒶 ℓ} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

record isProp {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field force-≡ : ∀(a b : A) -> a ≡ b

open isProp {{...}} public

length : ∀ {A : Set} → List A → Nat
length []        =  zero
length (x ∷ xs)  =  suc (length xs)


--------------------------------------------------
-- decidable equality

open import Agora.Conventions using (isDecidable)

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → isDecidable (x ≡ y)

open hasDecidableEquality {{...}} public
