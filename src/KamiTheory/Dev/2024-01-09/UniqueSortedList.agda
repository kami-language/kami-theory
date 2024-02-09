module KamiTheory.Dev.2024-01-09.UniqueSortedList where

open import Agora.Conventions -- using (¬_)

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (lsuc)
open import Data.Sum.Base using (_⊎_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Fin.Base using (Fin)


record isStrictOrder {𝑖} (𝑗 : 𝔏) (A : Set 𝑖) : Set (𝑖 ､ 𝑗 ⁺) where
  field
    _<_ : A → A → Set 𝑗
    <irrefl : ∀ {a : A} → ¬ (a < a)
    -- <asym : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    <trans : ∀ {a b c : A} → a < b → b < c → a < c
    <conn : ∀ {a b : A} → ¬ (a ≡ b) → (a < b) ⊎ (b < a)

open isStrictOrder {{...}}

StrictOrder : ∀ (𝑖 : 𝔏 ^ 2) -> _
StrictOrder 𝑖 = Set (𝑖 ⌄ 0) :& isStrictOrder (𝑖 ⌄ 1)

data isUniqueSortedList {A : Set 𝑖} {{_ : isStrictOrder 𝑗 A}} : List A → Set (𝑖 ､ 𝑗 ⁺) where
  [] : isUniqueSortedList []
  [-] : ∀ {a} → isUniqueSortedList (a ∷ [])
  _∷_ :  ∀ {a b as} → (a < b) → isUniqueSortedList (b ∷ as) → isUniqueSortedList (a ∷ b ∷ as)


--------------------------------------------------
-- TODO move into appropriate folder(s)
instance
  _isUniverseOf[_]_:List : ∀{A : 𝒰 𝑖} -> (List A) isUniverseOf[ _ ] (List A)
  _isUniverseOf[_]_:List = _isUniverseOf[_]_:byBase

macro 𝟙 = #structureOn 𝟙-𝒰
macro
  𝔽 : ℕ -> _
  𝔽 n = #structureOn (Fin n)

--------------------------------------------------

UniqueSortedList : (A : StrictOrder 𝑖) -> _
UniqueSortedList A = List ⟨ A ⟩ :& isUniqueSortedList

module _ {A : StrictOrder 𝑖} where
  ⦗_⦘ : ⟨ A ⟩ -> UniqueSortedList A
  ⦗_⦘ a = (a ∷ []) since [-]

module _ {A : StrictOrder 𝑖} where
  postulate
    _⊆_ : (U V : UniqueSortedList A) -> 𝒰 𝑖
    decide-⊆ : ∀{U V} -> ¬(U ⊆ V) ⊎ U ⊆ V
    _∪_ : (U V : UniqueSortedList A) -> UniqueSortedList A

  infixl 50 _∪_

postulate
  -- TODO: Naming unclear
  instance isStrictOrder:⋆ : ∀{A B} -> {{_ : StrictOrder 𝑖 on A}} -> {{_ : StrictOrder 𝑗 on B}} -> isStrictOrder (𝑖 ⌄ 1 ⊔ 𝑗 ⌄ 1) (A +-𝒰 B)
  instance isStrictOrder:𝟙 : isStrictOrder ℓ₀ 𝟙

  instance isStrictOrder:𝔽 : isStrictOrder ℓ₀ (𝔽 n)


_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ +-𝒰 ⟨ B ⟩ ′

𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ 𝟙-𝒰 ′


