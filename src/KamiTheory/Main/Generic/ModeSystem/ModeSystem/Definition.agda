
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition

import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation as 2CellCommutation




record ModeSystem (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  field graph : 2Graph (𝑖 ⌄ 0 ⋯ 2)

  open 2CellCommutation.2CellCommutation graph
  field commute-intersecting : ∀{a b : 0Cell graph} -> ∀{μ η : 1Cell graph a b} -> Intersecting μ η -> ∑ λ ω -> MaybeSparse2CellGen invis μ ω ×-𝒰 MaybeSparse2CellGen vis ω η

  open 2CellRewriting.2CellRewriting graph
  field patterns-vis : List (∑ λ n -> 2CellLinePattern vis (𝑖 ⌄ 3) (suc n))
  field patterns-invis : List (∑ λ n -> 2CellLinePattern invis (𝑖 ⌄ 3) (suc n))

  -- open WithCommute commute-intersecting

open ModeSystem public

---------------------------------------------
-- Convenience definitions for accessing
-- the mode data

Mode : ModeSystem 𝑖 -> 𝒰 _
Mode M = Point (graph M)

ModeHom : (M : ModeSystem 𝑖) -> (m n : Mode M) -> 𝒰 _
ModeHom M = Path (Edge (graph M))


record ModeTrans (M : ModeSystem 𝑖) v {a b : Mode M} (μ η : ModeHom M a b) : 𝒰 𝑖 where
  constructor incl
  open 2CellDefinition.2CellDefinition
  field ⟨_⟩ : 2Cell (graph M) v μ η

open ModeTrans public


module _ {G : ModeSystem 𝑖} where

  private variable
    a b c d e f : 0Cell (graph G)
    μ : 1Cell (graph G) a b
    η : 1Cell (graph G) b c
    ω : 1Cell (graph G) c d
    v : Visibility

  open 2CellDefinition.2CellDefinition (graph G)
  open 2CellRewriting.2CellRewriting (graph G)

  normalizeₘ : ∀{v} -> ModeTrans G v μ η -> ModeTrans G v μ η
  normalizeₘ {v = vis} ξ    = incl (rewriteComplete (patterns-vis G) ⟨ ξ ⟩)
  normalizeₘ {v = invis} ξ  = incl (rewriteComplete (patterns-invis G) ⟨ ξ ⟩)

  _◆₂ₘ_ : ModeTrans G v μ η -> ModeTrans G v η ω -> ModeTrans G v μ ω
  _◆₂ₘ_ ξ ζ = normalizeₘ (incl (⟨ ξ ⟩ ◆₂ ⟨ ζ ⟩))


