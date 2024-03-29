-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.Transition where

open import Agora.Conventions hiding (m ; n ; _∣_)
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
  r : Range
  m n : Mode M

------------------------------------------------------------------------
-- ModalityTrans
--
-- An intermediate datatype which is like a ModeTrans but has modalities
-- for domain and codomain


data ModalityTrans (M : ModeSystem 𝑖) (r : Range) : (μ η : SomeModeHom M) -> 𝒰 𝑖 where
  _⇒_∋_ : ∀{m n : Mode M} -> (μ η : ModeHom M m n) -> (ξ : ModeTrans* M r μ η) -> ModalityTrans M r (m ↝ n ∋ μ) (m ↝ n ∋ η)

open 2CellDefinition.2CellDefinition

pattern idTⱼ = [ incl [] ∣ incl [] ]
pattern idT = _ ⇒ _ ∋ [ incl [] ∣ incl [] ]
pattern idT[_] μ = μ ⇒ _ ∋ [ incl [] ∣ incl [] ]

-- idT : ∀{M : ModeSystem 𝑖} -> ∀{μ : SomeModeHom M } -> ModalityTrans M all μ μ
-- idT = (_ ⇒ _ ∋ [ incl [] ∣ incl [] ])



---------------------------------------------
-- Category structure on modality trans

_◆-ModalityTrans_ : {μ η ω : SomeModeHom M}
                    -> ModalityTrans M r μ η
                    -> ModalityTrans M r η ω
                    -> ModalityTrans M r μ ω
(μ ⇒ η ∋ ξ) ◆-ModalityTrans (.η ⇒ ω ∋ ζ) = μ ⇒ ω ∋ (ξ ◆*₂ₘ ζ)



------------------------------------------------------------------------
-- Transitions

---------------------------------------------
-- A transition is a mode transformation with arbitrary
-- modalities as domain and codomain. We define them as
-- a monoid with explicit identity element.

data Transition (M : ModeSystem 𝑖) : (r : Range) -> 𝒰 𝑖 where
  id : Transition M r
  fail : String -> Transition M r
  incl : {μ η : SomeModeHom M} -> ModalityTrans M r μ η -> Transition M r




module _ {M : ModeSystem 𝑖} where
  private variable
    a b c : Mode m


  -- We want to allow transition composition where the domain of the second morphism is a
  -- prefix of the codomain of the first.

  -- Monoid structure on transitions
  _◆-Transition_ : Transition M r -> Transition M r -> Transition M r
  id ◆-Transition s = s
  (fail msg) ◆-Transition s = (fail msg)
  _◆-Transition_ t@(incl x) id = t
  _◆-Transition_ t@(incl x) (fail msg) = (fail msg)
  _◆-Transition_ t@(incl {η = η₀} x@(_ ⇒ _ ∋ xx)) (incl {μ = η₁} y@(_ ⇒ _ ∋ yy))
    with dom η₁ ≟ dom η₀
  ... | no p = (fail ("◆ at codomain point " <> show η₀ <> " ↔ " <> show η₁))
  ... | yes refl
    with checkSplit (graph M) (hom η₁) (hom η₀)
  ... | yes (incl (η₁' , refl)) = incl (x ◆-ModalityTrans (_ ⇒ _ ∋ (yy ↶-ModeTrans* η₁')))
  ... | no p
    with checkSplit (graph M) (hom η₀) (hom η₁)
  ... | no p = (fail ("◆ at boundary " <> show η₀ <> " ↔ " <> show η₁))
  ... | yes (incl (η₁' , refl)) = incl ((_ ⇒ _ ∋ (xx ↶-ModeTrans* η₁')) ◆-ModalityTrans y)

-- with η₀ ≟ η₁
--   ... | no p = (fail ("◆ at boundary " <> show η₀ <> " ↔ " <> show η₁))
--   ... | yes refl = incl (x ◆-ModalityTrans y)



  -- whiskering of transitions with modalities
  _↷-Transition_ : Modality M -> Transition M r -> Transition M r
  id ↷-Transition ξ = ξ
  fail ↷-Transition ξ = fail "↷ of fail"
  incl ϕ ↷-Transition id = id
  incl ϕ ↷-Transition (fail msg) = (fail msg)
  incl (a ↝ b ∋ ϕ) ↷-Transition incl (_⇒_∋_ {m = c} μ η ξ) with b ≟ c
  ... | no p = fail ("↷ of " <> show ϕ <> " failed (dom/cod)")
  ... | yes refl = incl ((ϕ ◆ μ) ⇒ (ϕ ◆ η) ∋ (ϕ ↷-ModeTrans* ξ))

  _↶-Transition_ : Transition M r -> Modality M -> Transition M r
  ξ ↶-Transition id = ξ
  ξ ↶-Transition fail = fail "↶ of fail"
  id ↶-Transition incl ϕ = id
  (fail msg) ↶-Transition incl ϕ = (fail msg)
  incl (_⇒_∋_ {m = a} {n = b} μ η ξ) ↶-Transition incl (c ↝ d ∋ ϕ) with b ≟ c
  ... | no p = fail ("↷ of " <> show ϕ <> " failed (dom/cod)")
  ... | yes refl = incl ((μ ◆ ϕ) ⇒ (η ◆ ϕ) ∋ (ξ ↶-ModeTrans* ϕ))

  into-all-Transition : Transition M vis -> Transition M all
  into-all-Transition id = id
  into-all-Transition (fail msg) = fail msg
  into-all-Transition (incl (μ ⇒ η ∋ ξ)) = incl (_ ⇒ _ ∋ into-all-ModeTrans* ξ)

  split-all-Transition : Transition M all -> Transition M all ×-𝒰 Transition M vis
  split-all-Transition id = id , id
  split-all-Transition (fail msg) = (fail msg) , (fail msg)
  split-all-Transition (incl (_ ⇒ _ ∋ ξ)) = let (_ , iξ , vξ) = split-all-ModeTrans* ξ in incl (_ ⇒ _ ∋ iξ) , incl (_ ⇒ _ ∋ vξ)


  -- commuting a visible transition with an all transition
  commute-Transition-vis : Transition M vis -> Transition M all -> (Transition M all ×-𝒰 Transition M vis)
  commute-Transition-vis ξ ζ =
    let ξ' = into-all-Transition ξ
    in split-all-Transition (ξ' ◆-Transition ζ)

  ----------------------------------------------------------
  -- Decidability



  decide-≡-Transition : (x y : Transition M r) → isDecidable (x ≡ y)
  decide-≡-Transition id id = yes refl
  decide-≡-Transition id (fail s) = no λ ()
  decide-≡-Transition id (incl x) = no λ ()
  decide-≡-Transition (fail s) id = no λ ()
  decide-≡-Transition (fail s) (fail t) = yes {!!}
  decide-≡-Transition (fail s) (incl x) = no λ ()
  decide-≡-Transition (incl x) id = no λ ()
  decide-≡-Transition (incl x) (fail s) = no λ ()
  decide-≡-Transition (incl (_⇒_∋_ {m} {n} μ η ξ)) (incl (_⇒_∋_ {m₁} {n₁} μ₁ η₁ ξ₁)) with m ≟ m₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with n ≟ n₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with μ ≟ μ₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with η ≟ η₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with ξ ≟ ξ₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Transition : ∀{r} -> hasDecidableEquality (Transition M r)
    hasDecidableEquality:Transition = record { _≟_ = decide-≡-Transition }

