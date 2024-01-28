
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Upclosed where

open import Agora.Conventions hiding (Σ ; Lift ; k)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.UniqueSortedList

-- A preorder where we have a notion of "direct" parent

record hasStep (X : Preorder 𝑖) : 𝒰 (𝑖 ⁺) where
  field _⩿_ : ⟨ X ⟩ -> ⟨ X ⟩ -> 𝒰 (𝑖 ⌄ 2)

open hasStep {{...}} public

record isExhaustable (X : StrictOrder 𝑖) : 𝒰 (𝑖 ⁺) where
  field everything : 𝒫ᶠⁱⁿ X
  field inEverything : ∀(x : ⟨ X ⟩) -> x ∈ ⟨ everything ⟩


-- data Open (L : Lattice 𝑖) : 𝒰 𝑖 where

-- macro
--   𝒪 : ∀ L -> _
--   𝒪 L = #structureOn (Open L)

-- instance
--   isSetoid:Open : isSetoid {ℓ₀} (Open L)
--   isSetoid:Open = isSetoid:byId

-- postulate
--   _≤-𝒪_ : Open L -> Open L -> Set ℓ₀

-- instance
--   isPreorderData:≤-Open : isPreorderData (𝒪 L) _≤-𝒪_
--   isPreorderData:≤-Open = record { reflexive = {!!} ; _⟡_ = {!!} ; transp-≤ = {!!} }

-- instance
--   isPreorder:Open : isPreorder ℓ₀ (𝒪 L)
--   isPreorder:Open = isPreorder:byDef _≤-𝒪_



