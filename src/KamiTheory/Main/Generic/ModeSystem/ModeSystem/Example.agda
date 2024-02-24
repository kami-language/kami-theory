
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
-- open import KamiTheory.Main.Generic.ModeSystem.Modality

open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open 2CellDefinition

open import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting
open 2CellRewriting

open import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation
open 2CellCommutation


import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as 2GraphExample
import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample



module SendReceiveNarrow-ModeSystem (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  open 2GraphExample.SendReceiveNarrow-2Graph P
  open 2CellExample.SendReceiveNarrow-2Cells P {{it}} {{it}}

  commute-intersecting-SRN : ∀{a b : 0Cell SRN} -> ∀{μ η : 1Cell SRN a b}
                             -> Intersecting SRN μ η
                             -> ∑ λ ω -> MaybeSparse2CellGen SRN invis μ ω ×-𝒰 MaybeSparse2CellGen SRN vis ω η
  commute-intersecting-SRN (situation1 id (`＠` U ⨾ id) id δ≠id () iξ)
  commute-intersecting-SRN (situation1 id (`＠` U ⨾ id) (x ⨾ vεₗvξ₁') δ≠id () iξ)
  commute-intersecting-SRN (situation1 (`＠` U₁ ⨾ vεₗ') (`＠` U ⨾ id) vεₗvξ₁' δ≠id () iξ)
  commute-intersecting-SRN (situation1 (`[]` ⨾ vεₗ') (`＠` U ⨾ id) vεₗvξ₁' δ≠id () iξ)


  commute-intersecting-SRN (situation2 id (`＠` U ⨾ .id) .(`[]` ⨾ id) (send .U) (narrow x)) = _ , id , incl (id ⌟[ _ ⇒ _ ∋ (send _) ]⌞ id [ refl , refl ])
  commute-intersecting-SRN (situation2 (`＠` U₁ ⨾ `[]` ⨾ id) (`＠` U ⨾ .id) iεₗiξ₀' () (narrow x))
  commute-intersecting-SRN (situation2 (`＠` U₁ ⨾ `[]` ⨾ x₁ ⨾ vεₗ') (`＠` U ⨾ .id) iεₗiξ₀' () (narrow x))


  commute-intersecting-SRN (situation3 .(`＠` _ ⨾ id) id id (recv U) (narrow x)) = _ , incl (id ⌟[ _ ⇒ _ ∋ (narrow x) ]⌞ _ [ refl , refl ]) , incl ((`＠` _ ⨾ id) ⌟[ _ ⇒ _ ∋ (recv _) ]⌞ id [ refl , refl ])
  commute-intersecting-SRN (situation3 (x₁ ⨾ id) id (x ⨾ vεₗvξ₁') (recv U) ())
  commute-intersecting-SRN (situation3 (x₁ ⨾ x₂ ⨾ iεₗ') id (x ⨾ vεₗvξ₁') (recv U) ())
  commute-intersecting-SRN (situation3 (x₂ ⨾ id) (.(`＠` U) ⨾ .`[]` ⨾ .id) vεₗvξ₁' (send U) ())
  commute-intersecting-SRN (situation3 (x₂ ⨾ x ⨾ iεₗ') (.(`＠` U) ⨾ .`[]` ⨾ .id) vεₗvξ₁' (send U) ())


  commute-intersecting-SRN (situation4 id (.(`＠` _) ⨾ .id) id δ≠id () (narrow x))
  commute-intersecting-SRN (situation4 id (`＠` U ⨾ .id) (.`[]` ⨾ .id) δ≠id (send .U) (narrow x)) = _ , id , incl (id ⌟[ _ ⇒ _ ∋ (send _) ]⌞ id [ refl , refl ])
  commute-intersecting-SRN (situation4 (2GraphExample.SendReceiveNarrow-2Graph.`＠` U₁ ⨾ x ⨾ iεₗ') (.(2GraphExample.SendReceiveNarrow-2Graph.`＠` U) ⨾ id) .(2GraphExample.SendReceiveNarrow-2Graph.`[]` ⨾ id) δ≠id (2GraphExample.SendReceiveNarrow-2Graph.send U) ())
  commute-intersecting-SRN (situation4 (x₁ ⨾ id) (x ⨾ x₂ ⨾ δ) id δ≠id vξ ())
  commute-intersecting-SRN (situation4 (x₁ ⨾ id) (x ⨾ x₂ ⨾ δ) (x₃ ⨾ iεₗiξ₀') δ≠id vξ ())
  commute-intersecting-SRN (situation4 (x₁ ⨾ x₃ ⨾ iεₗ') (x ⨾ x₂ ⨾ δ) iεₗiξ₀' δ≠id vξ ())

  SRN-ModeSystem : ModeSystem _
  SRN-ModeSystem = record
      { graph = SRN
      ; commute-intersecting = commute-intersecting-SRN
      ; patterns-vis = 1 , RewriteCells.Pat-SR ∷ []
      ; patterns-invis = []
      }



