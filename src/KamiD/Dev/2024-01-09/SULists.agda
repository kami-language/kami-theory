module KamiD.Dev.2024-01-09.SULists where

open import Agora.Conventions using (¬_)

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (lsuc)
open import Data.Sum.Base using (_⊎_)
open import Data.List.Base using (List; []; _∷_)


record isStrictOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _<_ : A → A → Set 𝑖
    <irrefl : ∀ {a : A} → ¬ (a < a)
    -- <asym : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    <trans : ∀ {a b c : A} → a < b → b < c → a < c
    <conn : ∀ {a b : A} → ¬ (a ≡ b) → (a < b) ⊎ (b < a)

open isStrictOrder {{...}}


data SUList {𝑖} {A : Set 𝑖} {{_ :  isStrictOrder A}} : List A → Set (lsuc 𝑖) where
  [] : SUList []
  [-] : ∀ {a} → SUList (a ∷ [])
  _∷_ :  ∀ {a b as} → (a < b) → SUList (b ∷ as) → SUList (a ∷ b ∷ as)
