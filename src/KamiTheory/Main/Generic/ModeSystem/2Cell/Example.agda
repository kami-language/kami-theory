
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Example where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition


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






