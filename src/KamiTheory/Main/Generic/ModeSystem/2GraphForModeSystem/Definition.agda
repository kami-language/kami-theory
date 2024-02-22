
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2GraphForModeSystem.Definition where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
-- open import KamiTheory.Main.Generic.ModeSystem.LinearFSM.Definition
open import KamiTheory.Order.StrictOrder.Base

open import Data.Fin using (Fin ; zero ; suc)


import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation as 2CellCommutation


open 2CellDefinition.2CellDefinition


record 2GraphForModeSystem (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  field graph : 2Graph (𝑖 ⌄ 0 ⋯ 2)

  open 2CellCommutation.2CellCommutation graph
  field commute-intersecting : ∀{a b : 0Cell graph} -> ∀{μ η : 1Cell graph a b} -> Intersecting μ η -> ∑ λ ω -> MaybeSparse2CellGen invis μ ω ×-𝒰 MaybeSparse2CellGen vis ω η

  open 2CellRewriting.2CellRewriting graph
  field patterns-vis : List (∑ 2CellLinePattern vis (𝑖 ⌄ 3))
  field patterns-invis : List (∑ 2CellLinePattern invis (𝑖 ⌄ 3))

  -- open WithCommute commute-intersecting

open 2GraphForModeSystem public


record ModeTrans (G : 2GraphForModeSystem 𝑖) v {a b : 0Cell (graph G)} (μ η : 1Cell (graph G) a b) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : 2Cell (graph G) v μ η




