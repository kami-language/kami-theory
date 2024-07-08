

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.UniqueSortedList.Properties where

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Conventions
open import Agora.Data.Fin.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics


record isFiniteStrictOrder (A : StrictOrder 𝑖): 𝒰 𝑖 where
  field All : 𝒫ᶠⁱⁿ A
  field intoAll : ∀{U : 𝒫ᶠⁱⁿ A} -> U ≤ All

open isFiniteStrictOrder {{...}} public

module _ {A : StrictOrder 𝑖} {{_ : isFiniteStrictOrder A}} where
  ⊤-𝒫ᶠⁱⁿ : 𝒫ᶠⁱⁿ A
  ⊤-𝒫ᶠⁱⁿ = All

  terminal-⊤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤ ⊤-𝒫ᶠⁱⁿ
  terminal-⊤-𝒫ᶠⁱⁿ = intoAll

  instance
    hasFiniteMeets:𝒫ᶠⁱⁿ : hasFiniteMeets (𝒫ᶠⁱⁿ A)
    hasFiniteMeets:𝒫ᶠⁱⁿ = record
      { ⊤ = {!!}
      ; terminal-⊤ = {!!}
      ; _∧_ = {!!}
      ; π₀-∧ = {!!}
      ; π₁-∧ = {!!}
      ; ⟨_,_⟩-∧ = {!!}
      }


instance
  isFiniteStrictOrder:𝔽 : ∀{n} -> isFiniteStrictOrder (𝔽 n)
  isFiniteStrictOrder:𝔽 = {!!}

