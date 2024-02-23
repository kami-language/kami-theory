
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.Transition where

open import Agora.Conventions hiding (m ; n)
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation as 2CellCommutation

open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition

private variable
  M : ModeSystem 𝑖
  v : Visibility
  m n : Mode M

------------------------------------------------------------------------
-- ModalityTrans
--
-- An intermediate datatype which is like a ModeTrans but has modalities
-- for domain and codomain


data ModalityTrans (M : ModeSystem 𝑖) (v : Visibility) : (μ η : Modality M) -> 𝒰 𝑖 where
  _⇒_∋_ : ∀{m n : Mode M} -> (μ η : ModeHom M m n) -> (ξ : ModeTrans M v μ η) -> ModalityTrans M v (m ↝ n ∋ μ) (m ↝ n ∋ η)

---------------------------------------------
-- Category structure on modality trans

_◆-ModalityTrans_ : {μ η ω : Modality M}
                    -> ModalityTrans M v μ η
                    -> ModalityTrans M v η ω
                    -> ModalityTrans M v μ ω
(μ ⇒ η ∋ ξ) ◆-ModalityTrans (.η ⇒ ω ∋ ζ) = μ ⇒ ω ∋ (ξ ◆₂ₘ ζ)



------------------------------------------------------------------------
-- Transitions

---------------------------------------------
-- A transition is a mode transformation with arbitrary
-- modalities as domain and codomain. We define them as
-- a monoid with explicit identity element.

data Transition (M : ModeSystem 𝑖) : (v : Visibility) -> 𝒰 𝑖 where
  id : Transition M invis
  fail : Transition M v
  _⇒_∋_ : (μ η : Modality M) -> ModalityTrans M v μ η -> Transition M v



-- Monoid structure on transitions

module _ {M : ModeSystem 𝑖} where

  _◆-Transition_ : Transition M v -> Transition M v -> Transition M v
  id ◆-Transition s = s
  fail ◆-Transition s = fail
  _◆-Transition_ t@(μ ⇒ η ∋ x) id = t
  _◆-Transition_ t@(μ ⇒ η ∋ x) fail = fail
  _◆-Transition_ t@(μ ⇒ η₀ ∋ x) (η₁ ⇒ ω ∋ y) with η₀ ≟ η₁
  ... | no p = fail
  ... | yes refl = μ ⇒ ω ∋ (x ◆-ModalityTrans y)



