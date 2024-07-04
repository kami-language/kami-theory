
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.UniqueSortedList.NonEmpty where

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Conventions
open import KamiTheory.Data.UniqueSortedList.Definition

-- nonempty finite power sets over A
module _ (A : StrictOrder 𝑖) where
  NonEmptyUniqueSortedList : Set 𝑖
  NonEmptyUniqueSortedList = ∑ λ (x : 𝒫ᶠⁱⁿ A) -> ¬ x ≡ ⊥

  macro 𝒫₊ᶠⁱⁿ = #structureOn NonEmptyUniqueSortedList

module _ {A : StrictOrder 𝑖} where
  ⦗_⦘₊ : ⟨ A ⟩ -> 𝒫₊ᶠⁱⁿ A
  ⦗_⦘₊ a = ((a ∷ []) since [-]) , λ ()

module _ {A : StrictOrder 𝑖} where

  record _∼-𝒫₊ᶠⁱⁿ_ (a b : 𝒫₊ᶠⁱⁿ A) : Set 𝑖 where
    constructor incl
    field ⟨_⟩ : fst a ∼ fst b
  open _∼-𝒫₊ᶠⁱⁿ_ public

  instance
    isEquivRel:∼-𝒫₊ᶠⁱⁿ : isEquivRel (_∼-𝒫₊ᶠⁱⁿ_)
    isEquivRel:∼-𝒫₊ᶠⁱⁿ = record { refl-∼ = {!!} ; sym = {!!} ; _∙_ = {!!} }

  -- `𝒫₊ᶠⁱⁿ A` forms a setoid with strict equality
  instance
    isSetoid:𝒫₊ᶠⁱⁿ : isSetoid (𝒫₊ᶠⁱⁿ A)
    isSetoid:𝒫₊ᶠⁱⁿ = record { _∼_ = _∼-𝒫₊ᶠⁱⁿ_ }

  -- `𝒫₊ᶠⁱⁿ A` forms a preorder with _⊆_ as relation
  record _≤-𝒫₊ᶠⁱⁿ_ (U V : 𝒫₊ᶠⁱⁿ A) : Set 𝑖 where
    constructor incl
    field ⟨_⟩ : fst U ≤ fst V
  open _≤-𝒫₊ᶠⁱⁿ_ {{...}} public

  refl-≤-𝒫₊ᶠⁱⁿ : ∀{U} -> U ≤-𝒫₊ᶠⁱⁿ U
  refl-≤-𝒫₊ᶠⁱⁿ = incl refl-≤

  _⟡-𝒫₊ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫₊ᶠⁱⁿ V -> V ≤-𝒫₊ᶠⁱⁿ W -> U ≤-𝒫₊ᶠⁱⁿ W
  incl p ⟡-𝒫₊ᶠⁱⁿ incl q = incl (p ⟡ q)

  instance
    isPreorderData:≤-𝒫₊ᶠⁱⁿ : isPreorderData (𝒫₊ᶠⁱⁿ A) _≤-𝒫₊ᶠⁱⁿ_
    isPreorderData:≤-𝒫₊ᶠⁱⁿ = record
      { refl-≤ = refl-≤-𝒫₊ᶠⁱⁿ
      ; _⟡_ = _⟡-𝒫₊ᶠⁱⁿ_
      ; transp-≤ = {!!} -- λ {refl refl x₂ → x₂}
      }

  -- `𝒫₊ᶠⁱⁿ A` has finite joins (least upper bounds / maximum / or)
  instance
    isPreorder:𝒫₊ᶠⁱⁿ : isPreorder _ (𝒫₊ᶠⁱⁿ A)
    isPreorder:𝒫₊ᶠⁱⁿ = record { _≤_ = _≤-𝒫₊ᶠⁱⁿ_ }


module _ {A : StrictOrder 𝑖} where
  open Agora.Order.Preorder
  open Structure -- funnily this is needed for `of_` to work

  private instance _ = hasDecidableEquality:byStrictOrder {{of A}}


  decide-≤-𝒫₊ᶠⁱⁿ : ∀(u v : 𝒫₊ᶠⁱⁿ A) -> (¬ (u ≤ v)) +-𝒰 (u ≤ v)
  decide-≤-𝒫₊ᶠⁱⁿ u v with decide-≤ (fst u) (fst v)
  ... | yes p = right (incl p)
  ... | no ¬p = left (λ p -> ¬p ⟨ p ⟩)


  instance
    isDecidablePreorder:≤-𝒫₊ᶠⁱⁿ : isDecidablePreorder (𝒫₊ᶠⁱⁿ A)
    isDecidablePreorder:≤-𝒫₊ᶠⁱⁿ =
      record { decide-≤ = decide-≤-𝒫₊ᶠⁱⁿ }
