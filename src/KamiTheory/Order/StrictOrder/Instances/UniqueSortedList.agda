
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.StrictOrder.Instances.UniqueSortedList where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Order.StrictOrder.Instances.List
open import KamiTheory.Data.UniqueSortedList.Definition

-- we show that 𝒫ᶠⁱⁿ has a strict order (inherited from list)

module _ {X : StrictOrder 𝑖} {{_ : ∀{x y : ⟨ X ⟩} -> isProp (x < y)}} where
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


