-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2024-01-20.Space where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Dev.2024-01-20.Core hiding (_＠_)
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base
open import KamiTheory.Dev.2024-01-20.UniqueSortedList
open import KamiTheory.Dev.2024-01-20.StrictOrder.Instances.List
open import KamiTheory.Dev.2024-01-20.Basics
open import KamiTheory.Dev.2024-01-20.Open

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition

open import Data.List using (_++_ ; concatMap)


Space = Lattice (ℓ₀ , ℓ₀ , ℓ₀)


----------------------------------------------------------
-- Instances for products


-- module _ {A : 𝒰 𝑖}
--          {{_ : isSetoid {𝑗} A}}
--          {{_ : isPreorder 𝑘 ′ A ′}}
--          {{_ : hasFiniteJoins ′ A ′}} where
--   instance
--     hasFiniteJoins:Family : ∀{I : 𝒰 𝑗} -> hasFiniteJoins (′ (I -> A) ′)
--     hasFiniteJoins.⊥         hasFiniteJoins:Family = λ _ -> ⊥
--     hasFiniteJoins.initial-⊥ hasFiniteJoins:Family = λ _ -> initial-⊥
--     hasFiniteJoins._∨_       hasFiniteJoins:Family = λ a b i -> a i ∨ b i
--     hasFiniteJoins.ι₀-∨      hasFiniteJoins:Family = λ a -> ι₀-∨
--     hasFiniteJoins.ι₁-∨      hasFiniteJoins:Family = λ a -> ι₁-∨
--     hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Family = λ f g a -> [ f a , g a ]-∨

-- module _ {A : 𝒰 _} {B : 𝒰 _} {{_ : StrictOrder 𝑖 on A}} {{_ : StrictOrder 𝑗 on B}} where
module _ {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} where

  bind-𝒫ᶠⁱⁿ : (⟨ A ⟩ -> 𝒫ᶠⁱⁿ B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
  bind-𝒫ᶠⁱⁿ f x = concatMap (λ x -> ⟨ f x ⟩) ⟨ x ⟩ since {!!}

  bind-Space : (⟨ A ⟩ -> 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ B)) -> (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ A) -> 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ B))
  bind-Space = {!!}

_×-Space_ : Space -> Space -> Space
_×-Space_ A B = ⟨ A ⟩ × ⟨ B ⟩



