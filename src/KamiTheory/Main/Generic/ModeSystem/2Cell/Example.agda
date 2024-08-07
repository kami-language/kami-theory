-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

----------------------------------------------------------
--
-- In this file we give examples of the 2cells of the
-- (＠ ⊣ ◻) adjuction, and in particular state the rewrite
-- rule for both triangle identities.
--
----------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Example where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open 2CellDefinition

open import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting
open 2CellRewriting

import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as Ex


--
-- We state some 2cells as examples.
--

module SendReceiveNarrow-2Cells (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  open Ex.SendReceiveNarrow-2Graph P

  module RewriteCells where
    ---------------------------------------------
    -- evaluating send/recv pairs
    --
    -- There are two evaluation rules for the adjunction,
    -- dependending on whether send or recv comes first.
    --
    -- We state both.

    -------------------
    -- send comes first
    SR-eval-dom : (U : ⟨ P ⟩) -> 2Cell SRN vis (`＠` U ⨾ id) (`＠` U ⨾ id)
    SR-eval-dom U = incl (id ⌟[ send U ]⌞ (`＠` U ⨾ id) ⌟)
                  ∷ incl ((`＠` U ⨾ id) ⌟[ recv U ]⌞ id ⌟)
                  ∷ []

    SR-eval-cod : (U : ⟨ P ⟩) -> 2Cell SRN vis (`＠` U ⨾ id) (`＠` U ⨾ id)
    SR-eval-cod U = []


    -------------------
    -- recv comes first
    RS-eval-dom : (U : ⟨ P ⟩) -> 2Cell SRN vis (`[]` ⨾ id) (`[]` ⨾ id)
    RS-eval-dom U = incl ((`[]` ⨾ id) ⌟[ send U ]⌞ id ⌟)
                  ∷ incl (id ⌟[ recv U ]⌞ (`[]` ⨾ id) ⌟)
                  ∷ []

    RS-eval-cod : 2Cell SRN vis (`[]` ⨾ id) (`[]` ⨾ id)
    RS-eval-cod = []

    ---------------------------------------------
    -- evaluating narrow/narrow pairs
    --
    -- narrow pairs can be composed
    NN-eval-dom : {U V W : ⟨ P ⟩}
                  -> (ϕ : U ≤ V) (ψ : V ≤ W)
                  -> 2Cell SRN invis (`＠` U ⨾ id) (`＠` W ⨾ id)
    NN-eval-dom ϕ ψ = incl (id ⌟[ narrow ϕ ]⌞ id ⌟)
                    ∷ incl (id ⌟[ narrow ψ ]⌞ id ⌟)
                    ∷ []

    NN-eval-cod : {U V W : ⟨ P ⟩}
                  -> (ϕ : U ≤ V) (ψ : V ≤ W)
                  -> 2Cell SRN invis (`＠` U ⨾ id) (`＠` W ⨾ id)
    NN-eval-cod ϕ ψ = incl (id ⌟[ narrow (ϕ ⟡ ψ) ]⌞ id ⌟)
                    ∷ []


    ------------------------------------------------------------------------
    -- We state the rewriting law
    --
    -- Interestingly enough, our rewriting algorithm is formulated in such
    -- a way that a single rewrite rule is applicable for both triangle identities.
    --
    -- It is given as a simple finite state machine which matches on faces
    -- and returns their transformation if applicable, while also carrying
    -- state to remember the location-annotations of our modalities.
    --
    Pat-SR : 2CellLinePattern SRN vis _ 2
    Pat-SR = record { State = S ; start = lift tt ; step = s }
      where
        S : ℕ -> 𝒰 _
        S zero = Lift 𝟙-𝒰
        S (suc zero) = ⟨ P ⟩
        S (suc (suc i)) = Lift 𝟙-𝒰

        s : (i : ℕ) → S i → {a b : 0Cell SRN} (ξ : SingleFace SRN vis a b) → Maybe (Some2CellGenOnPoints SRN vis a b ×-𝒰 S (suc i))
        -- STEP 0: We are searching for a send
        s zero _ (ϕ ⌟[ send U ]⌞ ψ) = yes ( record { get = incl ((ϕ ◆ ψ) ⌟) } , U )
        s zero _ (ϕ ⌟[ recv U ]⌞ ψ)   = nothing

        -- STEP 1: We are searching for a (matching!) recv
        s (suc zero) U (ϕ ⌟[ send _ ]⌞ ψ)  = nothing
        s (suc zero) U (ϕ ⌟[ recv V ]⌞ ψ) with U ≟ V
        ... | no _ = nothing
        ... | yes refl = yes ( record { get = incl ((ϕ ◆ ψ) ⌟)} , lift tt)

        -- STEP other: we are already done
        s (suc (suc i)) s ξ = nothing




------------------------------------------------------------------------
-- Here are some examples to test that the rewriting algorithm works
-- correctly.
------------------------------------------------------------------------

module Examples where

  open import Data.Fin.Base using (zero ; suc)
  open import Data.Fin using (#_)
  open import Data.List using (_∷_ ; [])

  open import Agora.Order.Preorder
  open import Agora.Order.Lattice
  open import Agora.Data.Normal.Definition
  open import Agora.Data.Normal.Instance.Setoid
  open import Agora.Data.Normal.Instance.Preorder
  open import Agora.Data.Normal.Instance.Lattice
  open import Agora.Data.Normal.Instance.DecidableEquality

  open import KamiTheory.Data.Open.Definition
  open import KamiTheory.Data.UniqueSortedList.Definition
  open import KamiTheory.Data.UniqueSortedList.Instance.Preorder
  open import KamiTheory.Order.StrictOrder.Base
  open import KamiTheory.Order.StrictOrder.Instances.UniqueSortedList

  PP : Preorder _
  PP = -- QQ
    ′_′ (𝒫ᶠⁱⁿ (𝔽 3)) {_} {{isPreorder:𝒫ᶠⁱⁿ}}

  MyInst : hasDecidableEquality ⟨ PP ⟩
  MyInst = hasDecidableEquality:𝒫ᶠⁱⁿ

  instance
    isProp:≤ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)
    isProp:≤ = {!!}

  open Ex.SendReceiveNarrow-2Graph PP {{MyInst}} {{isProp:≤}}


  uu : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘
  -- (((⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])
  vv : ⟨ PP ⟩
  vv = ⦗ # 1 ⦘


  G : 2Graph _
  G = (SRN )

  pat : 2CellLinePattern G vis _ 1
  pat = record { State = S ; start = tt ; step = s }
    where
      S : ℕ -> 𝒰₀
      S zero = 𝟙-𝒰
      S (suc i) = 𝟙-𝒰

      s : (i : ℕ) → S i → {a b : 0Cell G} (ξ : SingleFace G vis a b) →
          Maybe (Some2CellGenOnPoints G vis a b ×-𝒰 𝟙-𝒰)
      s _ st (ϕ ⌟[ send U ]⌞ ψ) with U ≟ uu
      ... | no p = nothing
      ... | yes p = yes ( record { top = _ ; bottom = _ ; get = incl (ϕ ⌟[ send U ]⌞ ψ ⌟) }
                          , tt)
      s _ st (idₗ₁ ⌟[ recv U ]⌞ idᵣ₁) = nothing


  ξ₀ : Some2CellGen G vis id _
  ξ₀ = incl ((id) ⌟[ send uu ]⌞ (id) ⌟[ send vv ]⌞ (id) ⌟)


  -- We try to find the send vv face
  result = findNext G pat _ (get ξ₀)

  ξ : 2Cell G vis (`＠` vv ⨾ id) (`＠` vv ⨾ id)
  ξ = SendReceiveNarrow-2Cells.RewriteCells.SR-eval-dom PP {{{!!}}} vv

  ξ₁ : 2Cell G vis _ _ -- (`＠` vv ⨾ id) (`＠` vv ⨾ id)
  ξ₁ = SendReceiveNarrow-2Cells.RewriteCells.RS-eval-dom PP {{{!!}}} vv

  ξ' : 2Cell G vis _ _ -- (`＠` vv ⨾ id) (`＠` vv ⨾ `[]` ⨾ `＠` uu ⨾ id)
  ξ' = incl (id ⌟[ send vv ]⌞ (`＠` vv ⨾ `[]` ⨾ `＠` uu ⨾ id) ⌟)
      ∷ incl ((`＠` vv ⨾ id) ⌟[ recv vv ]⌞ `[]` ⨾ `＠` uu ⨾ id ⌟)
      ∷ incl ((`＠` vv ⨾ `[]` ⨾ id) ⌟[ send uu ]⌞ (`＠` uu ⨾ id) ⌟)
      ∷ []


  -- now lets try to find sth in a 2cell
  result2 = findAllAndReduce G (SendReceiveNarrow-2Cells.RewriteCells.Pat-SR PP {{MyInst}} {{isProp:≤}}) ξ'




