
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Generic.ModeSystem.Transition where

open import Agora.Conventions hiding (m ; n)
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

private variable
  G : 2Graph 𝑖
  v w : Visibility
  m n : Mode G

------------------------------------------------------------------------
-- ModalityTrans
--
-- An intermediate datatype which is like a ModeTrans but has modalities
-- for domain and codomain


data ModalityTrans (G : 2Graph 𝑖) : (μ η : Modality G) (v : Visibility) -> 𝒰 𝑖 where
  _⇒_∋_ : ∀{m n : Mode G} -> (μ η : ModeHom G m n) -> (ξ : ModeTrans G μ η v) -> ModalityTrans G (m ↝ n ∋ μ) (m ↝ n ∋ η) v

---------------------------------------------
-- Category structure on modality trans

_◆-ModalityTrans_ : {μ η ω : Modality G}
                    -> ModalityTrans G μ η v
                    -> ModalityTrans G η ω w
                    -> ModalityTrans G μ ω (v ⋆ w)
(μ ⇒ η ∋ ξ) ◆-ModalityTrans (.η ⇒ ω ∋ ζ) = μ ⇒ ω ∋ (ξ ◇ ζ)



------------------------------------------------------------------------
-- Transitions

---------------------------------------------
-- A transition is a mode transformation with arbitrary
-- modalities as domain and codomain. We define them as
-- a monoid with explicit identity element.

data Transition (G : 2Graph 𝑖) : (v : Visibility) -> 𝒰 𝑖 where
  id : Transition G invis
  fail : Transition G v
  _⇒_∋_ : (μ η : Modality G) -> ModalityTrans G μ η v -> Transition G v



-- Monoid structure on transitions

module _ {G : 2Graph 𝑖} where

  _⋆-Transition_ : Transition G v -> Transition G w -> Transition G (v ⋆ w)
  id ⋆-Transition s = s
  fail ⋆-Transition s = fail
  _⋆-Transition_ {vis}   t@(μ ⇒ η ∋ x) id = t
  _⋆-Transition_ {vis}   t@(μ ⇒ η ∋ x) fail = fail
  _⋆-Transition_ {vis}   t@(μ ⇒ η₀ ∋ x) (η₁ ⇒ ω ∋ y) with η₀ ≟ η₁
  ... | no p = fail
  ... | yes refl = μ ⇒ ω ∋ (x ◆-ModalityTrans y)
  _⋆-Transition_ {invis} t@(μ ⇒ η ∋ x) id = t
  _⋆-Transition_ {invis} t@(μ ⇒ η ∋ x) fail = fail
  _⋆-Transition_ {invis} t@(μ ⇒ η₀ ∋ x) (η₁ ⇒ ω ∋ y) with η₀ ≟ η₁
  ... | no p = fail
  ... | yes refl = μ ⇒ ω ∋ (x ◆-ModalityTrans y)



