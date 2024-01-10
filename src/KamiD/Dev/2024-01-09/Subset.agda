{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-09.Subset where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-09.Core

postulate
  Subset : 𝒰₀ -> 𝒰₀
  _∪_ : ∀ {A} -> Subset A -> Subset A -> Subset A
  ⦗_⦘ : ∀{A} -> A -> Subset A

infixl 40 _∪_

