{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-14.UniqueSortedList where

open import Agora.Conventions -- using (¬_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

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

-- TODO: This name is very cumbersome. Rename?!
UniqueSortedList : (A : StrictOrder 𝑖) -> _
UniqueSortedList A = List ⟨ A ⟩ :& isUniqueSortedList

-- The fancy name for UniqueSortedList
macro
  𝒫ᶠⁱⁿ : StrictOrder 𝑖 -> _
  𝒫ᶠⁱⁿ A = #structureOn (UniqueSortedList A)

module _ {A : 𝒰 𝑖} {{_ : isStrictOrder 𝑗 A}} where
  ⦗_⦘ : A -> UniqueSortedList ′ A ′
  ⦗_⦘ a = (a ∷ []) since [-]

module _ {A : StrictOrder 𝑖} where

  -- data _≤-𝒫ᶠⁱⁿ_ : (U V : UniqueSortedList A) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1 ⁺) where
  -- -- data _≤-𝒫ᶠⁱⁿ_ : (U V : UniqueSortedList A) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1 ⁺) where
  --   [] : {V : UniqueSortedList A} → ([] since []) ≤-𝒫ᶠⁱⁿ V

  data _≤-𝒫ᶠⁱⁿ_ : (U V : UniqueSortedList A) -> 𝒰 (fst 𝑖 ⊔ snd 𝑖 ⁺) where
      empty : {vs : UniqueSortedList A} → ([] since []) ≤-𝒫ᶠⁱⁿ vs
      top : {v : ⟨ A ⟩} → {us vs : UniqueSortedList A} → us ≤-𝒫ᶠⁱⁿ vs → {pu : isUniqueSortedList (v ∷ ⟨ us ⟩)} → {pv : isUniqueSortedList (v ∷ ⟨ vs ⟩)} → ((v ∷ ⟨ us ⟩) since pu) ≤-𝒫ᶠⁱⁿ ((v ∷ ⟨ vs ⟩) since pv)
      pop : {v : ⟨ A ⟩} → {us vs : UniqueSortedList A} → us ≤-𝒫ᶠⁱⁿ vs → {p : isUniqueSortedList (v ∷ ⟨ vs ⟩)} → vs ≤-𝒫ᶠⁱⁿ ((v ∷ ⟨ vs ⟩) since p)

  decide-≤-𝒫ᶠⁱⁿ : ∀{U V} -> (¬(U ≤-𝒫ᶠⁱⁿ V)) +-𝒰 (U ≤-𝒫ᶠⁱⁿ V)
  decide-≤-𝒫ᶠⁱⁿ {[] since []} {V} = right empty
  decide-≤-𝒫ᶠⁱⁿ {′ x ∷ ⟨_⟩ ′} {V} = {!!}



  postulate
    -- _≤-𝒫ᶠⁱⁿ_ : (U V : UniqueSortedList A) -> 𝒰 𝑖
    -- decide-≤-𝒫ᶠⁱⁿ : ∀{U V} -> ¬(U ≤-𝒫ᶠⁱⁿ V) ⊎ U ≤-𝒫ᶠⁱⁿ V
    _∨-𝒫ᶠⁱⁿ_ : (U V : UniqueSortedList A) -> UniqueSortedList A

  infixl 50 _∨-𝒫ᶠⁱⁿ_

  instance
    isSetoid:𝒫ᶠⁱⁿ : isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = isSetoid:byId

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : isPreorderData (𝒫ᶠⁱⁿ A) (_≤-𝒫ᶠⁱⁿ_)
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { reflexive = {!!}
      ; _⟡_ = {!!}
      ; transp-≤ = {!!}
      }

  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = isPreorder:byDef _≤-𝒫ᶠⁱⁿ_

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = {!!}
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = {!!}
                           ; ι₁-∨ = {!!}
                           ; [_,_]-∨ = {!!}
                           }



postulate
  -- TODO: Naming unclear
  instance isStrictOrder:⋆ : ∀{A B} -> {{_ : StrictOrder 𝑖 on A}} -> {{_ : StrictOrder 𝑗 on B}} -> isStrictOrder (𝑖 ⌄ 1 ⊔ 𝑗 ⌄ 1) (A +-𝒰 B)
  instance isStrictOrder:𝟙 : isStrictOrder ℓ₀ 𝟙

  instance isStrictOrder:𝔽 : isStrictOrder ℓ₀ (𝔽 n)


_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ +-𝒰 ⟨ B ⟩ ′

𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ 𝟙-𝒰 ′



module _ (A : StrictOrder 𝑖) (B : StrictOrder 𝑗) where
  postulate
    isStrictOrderHom : (f : ⟨ A ⟩ -> ⟨ B ⟩) -> 𝒰 (𝑖 ､ 𝑗)

  StrictOrderHom = _ :& isStrictOrderHom


-- TODO Naming
module _ {A B : StrictOrder 𝑖} where
  postulate
    Img-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
    map-Img-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V

  postulate
    PreImg-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ B -> 𝒫ᶠⁱⁿ A
    map-PreImg-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> PreImg-𝒫ᶠⁱⁿ f U ≤ PreImg-𝒫ᶠⁱⁿ f V


postulate
  instance isStrictOrderHom:right : {A B : StrictOrder 𝑖} -> isStrictOrderHom B (A ⋆-StrictOrder B) right






