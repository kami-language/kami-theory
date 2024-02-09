
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2024-02-08.ML.Rules where

open import Agora.Conventions hiding (Σ ; Lift ; k ; m ; n ; Structure)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_ ; _≰_ ; _/_)
-- open import Relation.Nullary.Decidable.Core

open import KamiTheory.Dev.2024-02-08.Core hiding (_＠_)


Index = ⊤

  data Ctx (Ix : Index) : 𝒰₀

  private variable
    Γ : Ctx W
    Γ₀ Γ₁ : Ctx W



