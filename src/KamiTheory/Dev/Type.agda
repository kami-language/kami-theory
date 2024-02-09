
module KamiTheory.Dev.Type where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Universe.Power.Definition
open import Data.Fin
open import Data.Nat


module _ {A B : 𝒰 𝑖} where
  record isRestriction (f : A -> B) : 𝒰 𝑖 where
    field decide : ∀(b : B) -> Maybe (∑ λ a -> f a ≣ b)

-- data RTel : 𝒰₁ where
--   El : 𝒰₀


module _ {R : 𝒰₀} where

  data Prot (R : ℕ) : (Tel : 𝒫 R -> 𝒰₀) -> 𝒰₁ where
    Σ : ∀{Tel} -> Fin R -> (A : Tel -> 𝒰₀) -> Prot R (∑ A) -> Prot R Tel
    Π : ∀{Tel} -> Fin R -> (A : Tel -> 𝒰₀) -> Prot R (∑ A) -> Prot R Tel
    End : ∀{Tel} -> Prot R Tel

watashi wa maxim desu.




fp : Prot 1 𝟙-𝒰
fp = Π zero (const ℕ) (Π zero (const ℕ) (Σ zero (const ℕ) End))





