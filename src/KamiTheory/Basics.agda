
module KamiTheory.Basics where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base
open import Agda.Builtin.Nat using (Nat; zero; suc)

--------------------------------------------------
-- equality

open import Agora.Conventions using (_≡_ ; refl-≡)

-- we say refl instead of refl-≡
pattern refl = refl-≡

--------------------------------------------------
-- decidable equality

open import Agora.Conventions using (isDecidable)

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → isDecidable (x ≡ y)

open hasDecidableEquality {{...}} public



--------------------------------------------------
-- derivability syntax sugar


open import Agora.Conventions using (Maybe ; just)

record isDerivable {𝑖} (A : Set 𝑖) : Set 𝑖 where
  field derive : Maybe A

open isDerivable {{...}} public

record isTrue {𝑖} (A : Set 𝑖) : Set 𝑖 where
  constructor because
  field proof : A

open isTrue {{...}} public

instance
  isTrue:isDerivable : ∀{𝑖} {A : Set 𝑖} -> {{der : isDerivable A}} {a : A} -> {{_ :  derive {{der}} ≡ just a}} -> isTrue A
  isTrue:isDerivable {a = a} = record { proof = a }


--------------------------------------------------
-- others

_↯_ : ∀ {𝒶 ℓ} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

record isProp {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field force-≡ : ∀(a b : A) -> a ≡ b

open isProp {{...}} public

length : ∀ {A : Set} → List A → Nat
length []        =  zero
length (x ∷ xs)  =  suc (length xs)


