
module KamiTheory.Main.Dependent.Untyped.Instances where

open import Agora.Conventions

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped



module _ {P : 𝒰₀} {{_ : hasDecidableEquality P}} where
  _≟-MLMod_ : (a b : MLMod P) -> isDecidable (a ≣ b)
  Global ≟-MLMod Global = just refl-≣
  Global ≟-MLMod Local U = left (λ ())
  Local U ≟-MLMod Global = left (λ ())
  Local U ≟-MLMod Local V with U ≟ V
  ... | left x = left λ {refl-≣ -> x refl-≣}
  ... | just refl-≣ = just refl-≣


instance
  hasDecidableEquality:MLMod : ∀{P} -> {{_ : hasDecidableEquality P}} -> hasDecidableEquality (MLMod P)
  hasDecidableEquality:MLMod = record { _≟_ = _≟-MLMod_ }

_≟-Kind_ : ∀{ns} -> (k l : Kind ns) -> isDecidable (k ≣ l)
_≟-Kind_ = {!!}

instance
  hasDecidableEquality:Kind : ∀{ns} -> hasDecidableEquality (Kind ns)
  hasDecidableEquality:Kind = record { _≟_ = _≟-Kind_ }

_≟-Term_ : ∀{P n} -> (k l : Term P n) -> isDecidable (k ≣ l)
_≟-Term_ = {!!}

instance
  hasDecidableEquality:Term : ∀{P n} -> hasDecidableEquality (Term P n)
  hasDecidableEquality:Term = record { _≟_ = _≟-Term_ }



