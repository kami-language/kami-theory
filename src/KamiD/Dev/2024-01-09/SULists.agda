module KamiD.Dev.2024-01-09.SULists where

open import Agora.Conventions using (¬_)

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (lsuc)
open import Data.Sum.Base using (_⊎_)
open import Data.List.Base using (List; []; _∷_)


record isLinearOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _≤_ : A → A → Set 𝑖
    ≤refl : ∀ {a : A} → a ≤ a -- follows from scon
    ≤trans : ∀ {a b c : A} → a ≤ b → b ≤ c → a ≤ c
    ≤asym : ∀ {a b : A} → a ≤ b → b ≤ a → a ≡ b
    ≤scon : ∀ {a b : A} → (a ≤ b) ⊎ (b ≤ a)

open isLinearOrder {{...}}


infix 4 _∈_
data _∈_ {𝑖} {A : Set 𝑖} : A → List A → Set 𝑖 where
  here : ∀ {a as} → a ∈ (a ∷ as)
  there : ∀ {a b as} → a ∈ as → a ∈ (b ∷ as)


infix 4 _∉_
_∉_ : ∀ {𝑖} {A : Set 𝑖} → A → List A → Set 𝑖
a ∉ as = ¬ (a ∈ as)


data SUList {𝑖} {A : Set 𝑖} {{_ :  isLinearOrder A}} : List A → Set (lsuc 𝑖) where
  [] : SUList []
  [_] : ∀ (a : A) → SUList (a ∷ [])
  _,_∷_ :  ∀ {a b as} → (a ∉ as) → (a ≤ b) → SUList (b ∷ as) → SUList (a ∷ b ∷ as)

