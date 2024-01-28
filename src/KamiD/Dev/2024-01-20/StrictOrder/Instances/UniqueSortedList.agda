
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.StrictOrder.Instances.UniqueSortedList where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.StrictOrder.Base
open import KamiD.Dev.2024-01-20.UniqueSortedList
open import KamiD.Dev.2024-01-20.StrictOrder.Instances.List

-- we show that 𝒫ᶠⁱⁿ has a strict order (inherited from list)

module _ {X : StrictOrder 𝑖} where
  record _<-𝒫ᶠⁱⁿ_ (u v : 𝒫ᶠⁱⁿ X) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ u ⟩ < ⟨ v ⟩

  open _<-𝒫ᶠⁱⁿ_ public

  private
    ψ : ∀(u v : 𝒫ᶠⁱⁿ X) -> Tri< _<-List_ ⟨ u ⟩ ⟨ v ⟩ -> Tri< _<-𝒫ᶠⁱⁿ_ u v
    ψ u v (tri< a<b a≢b a≯b) = tri< (incl a<b) (λ {refl-≣ -> a≢b refl-≣}) (λ p -> a≯b ⟨ p ⟩)
    ψ u v (tri≡ a≮b a≡b a≯b) = tri≡ {!!} {!!} {!!}
    ψ u v (tri> a≮b a≢b a>b) = {!!}

  instance
    isStrictOrder:<-𝒫ᶠⁱⁿ : isStrictOrder _<-𝒫ᶠⁱⁿ_
    isStrictOrder:<-𝒫ᶠⁱⁿ = record
      { irrefl-< = λ p -> irrefl-< ⟨ p ⟩
      ; trans-< = λ p q -> incl (trans-< ⟨ p ⟩ ⟨ q ⟩)
      ; conn-< = λ a b -> ψ a b (conn-< ⟨ a ⟩ ⟨ b ⟩)
      }



