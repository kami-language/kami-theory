
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.Vec.Definition where

open import Agora.Conventions hiding (Σ ; Lift ; k)
open import KamiTheory.Basics

open import Data.Fin using (Fin ; suc ; zero)
-- open import Data.Vec using () renaming (_[_]=_ to _∈_at_ ; here to take ; there to skip) public
open import Data.Vec using (Vec ; [] ; _∷_) public

module _ {X : 𝒰 𝑖} where

  data _∈_at_ : (x : X) -> (xs : Vec X n) -> Fin n -> 𝒰 𝑖 where
    take : ∀{x} {xs : Vec X n} -> x ∈ (x ∷ xs) at zero
    skip : ∀{x y n i} {xs : Vec X n} -> y ∈ xs at i -> y ∈ x ∷ xs at suc i

  data _≤ⁱⁿᵈ-Vec_ : (xs : Vec X n) (ys : Vec X m) -> 𝒰 𝑖 where
    [] : ∀{vs : Vec X n} -> [] ≤ⁱⁿᵈ-Vec vs
    _∷_ : ∀{u i} {us : Vec X n} {vs : Vec X m} -> u ∈ vs at i -> us ≤ⁱⁿᵈ-Vec vs -> (u ∷ us) ≤ⁱⁿᵈ-Vec vs

  _≤-Vec_ : ∀(xs ys : Vec X n) -> 𝒰 _
  _≤-Vec_ xs ys = {!∀{x i} -> x ∈ xs at i -> x ∈ ys at j!}




