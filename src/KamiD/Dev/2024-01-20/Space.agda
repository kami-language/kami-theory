
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Space where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.StrictOrder.Base
open import KamiD.Dev.2024-01-20.UniqueSortedList
open import KamiD.Dev.2024-01-20.StrictOrder.Instances.List
open import KamiD.Dev.2024-01-20.Basics
open import KamiD.Dev.2024-01-20.Open

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition

open import Data.List using (_++_)


Space = Lattice (ℓ₁ , ℓ₁ , ℓ₁)

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


_×-Space_ : Space -> Space -> Space
_×-Space_ A B = ⟨ A ⟩ × ⟨ B ⟩



