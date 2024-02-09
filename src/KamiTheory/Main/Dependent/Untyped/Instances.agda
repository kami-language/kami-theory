
module KamiTheory.Main.Dependent.Untyped.Instances where

open import KamiTheory.Main.Dependent.Untyped
open import Agora.Conventions



module _ {P : 𝒰₀} {{_ : isDiscrete P}} where
  _≟-MLMod_ : (a b : MLMod P) -> isDecidable (a ≣ b)
  Global ≟-MLMod Global = just refl-≣
  Global ≟-MLMod Local U = left (λ ())
  Local U ≟-MLMod Global = left (λ ())
  Local U ≟-MLMod Local V with U ≟-Str V
  ... | left x = left λ {refl-≣ -> x refl-≣}
  ... | just refl-≣ = just refl-≣



instance
  isDiscrete:MLMod : ∀{P} -> {{_ : isDiscrete P}} -> isDiscrete (MLMod P)
  isDiscrete:MLMod = record { _≟-Str_ = _≟-MLMod_ }



