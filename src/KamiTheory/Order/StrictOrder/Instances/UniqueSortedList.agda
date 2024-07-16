-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.StrictOrder.Instances.UniqueSortedList where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Order.StrictOrder.Instances.List
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder

-- we show that 𝒫ᶠⁱⁿ has a strict order (inherited from list)


module _ {X : StrictOrder 𝑖}  where
  -- {{_ : ∀{x y : ⟨ X ⟩} -> isProp (x < y)}}

  record _<-𝒫ᶠⁱⁿ_ (u v : 𝒫ᶠⁱⁿ X) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ u ⟩ < ⟨ v ⟩

  open _<-𝒫ᶠⁱⁿ_ public

  private
    lift-≡ : ∀{u v : 𝒫ᶠⁱⁿ X} -> ⟨ u ⟩ ≡ ⟨ v ⟩ -> u ≡ v
    lift-≡ {u since up} {.u since vp} refl-≡ with force-≡ up vp
    ... | refl-≡ = refl-≡

    ψ : ∀(u v : 𝒫ᶠⁱⁿ X) -> Tri< _<-List_ ⟨ u ⟩ ⟨ v ⟩ -> Tri< _<-𝒫ᶠⁱⁿ_ u v
    ψ u v (tri< a<b a≢b a≯b) = tri< (incl a<b) (λ {refl-≡ -> a≢b refl-≡}) (λ p -> a≯b ⟨ p ⟩)
    ψ u v (tri≡ a≮b a≡b a≯b) = tri≡ (λ p -> a≮b ⟨ p ⟩) (lift-≡ a≡b) (λ p -> a≯b ⟨ p ⟩)
    ψ u v (tri> a≮b a≢b a>b) = tri> (λ p -> a≮b ⟨ p ⟩) (λ {refl-≡ -> a≢b refl-≡}) (incl a>b)

  force-≡-<-𝒫ᶠⁱⁿ : ∀{u v} -> (a b : u <-𝒫ᶠⁱⁿ v) → a ≡ b
  force-≡-<-𝒫ᶠⁱⁿ (incl a) (incl b) = cong-≡ incl (force-≡ a b)

  instance
    isProp:<-𝒫ᶠⁱⁿ : ∀{u v : 𝒫ᶠⁱⁿ X} -> isProp (u <-𝒫ᶠⁱⁿ v)
    isProp:<-𝒫ᶠⁱⁿ = record { force-≡ = force-≡-<-𝒫ᶠⁱⁿ }

  instance
    isStrictOrder:<-𝒫ᶠⁱⁿ : isStrictOrder _<-𝒫ᶠⁱⁿ_
    isStrictOrder:<-𝒫ᶠⁱⁿ = record
      { irrefl-< = λ p -> irrefl-< ⟨ p ⟩
      ; trans-< = λ p q -> incl (trans-< ⟨ p ⟩ ⟨ q ⟩)
      ; conn-< = λ a b -> ψ a b (conn-< ⟨ a ⟩ ⟨ b ⟩)
      }

  instance
    hasStrictOrder:𝒫ᶠⁱⁿ : hasStrictOrder (𝒫ᶠⁱⁿ X)
    hasStrictOrder:𝒫ᶠⁱⁿ = record { _<_ = _<-𝒫ᶠⁱⁿ_ }

  instance
    hasDecidableEquality:𝒫ᶠⁱⁿ : hasDecidableEquality (𝒫ᶠⁱⁿ X)
    hasDecidableEquality:𝒫ᶠⁱⁿ = hasDecidableEquality:byStrictOrder



