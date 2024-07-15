-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition where

open import Agora.Conventions hiding (_∣_)
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition

import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation as 2CellCommutation
import KamiTheory.Main.Generic.ModeSystem.2Cell.Decidability as 2CellDecidability




record ModeSystem (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  field graph : 2Graph (𝑖 ⌄ 0 ⋯ 2)
  open 2CellDefinition.2CellDefinition graph

  open 2CellCommutation.2CellCommutation graph
  field commute-intersecting : ∀{a b : 0Cell graph} -> ∀{μ η : 1Cell graph a b} -> Intersecting μ η -> ∑ λ ω -> MaybeSparse2CellGen invis μ ω ×-𝒰 MaybeSparse2CellGen vis ω η

  open 2CellRewriting.2CellRewriting graph
  field patterns-vis : List (∑ λ n -> 2CellLinePattern vis (𝑖 ⌄ 3) (suc n))
  field patterns-invis : List (∑ λ n -> 2CellLinePattern invis (𝑖 ⌄ 3) (suc n))

  open WithCommute commute-intersecting
  commute : ∀{a b : 0Cell graph} -> ∀{μ η ω : 1Cell graph a b}
          -> 2Cell vis μ η -> 2Cell invis η ω
                    -> ∑ λ η' -> (2Cell invis μ η' ×-𝒰 2Cell vis η' ω)
  commute = commute-2Cell

open ModeSystem public

---------------------------------------------
-- Convenience definitions for accessing
-- the mode data

Mode : ModeSystem 𝑖 -> 𝒰 _
Mode M = Point (graph M)

ModeHom : (M : ModeSystem 𝑖) -> (m n : Mode M) -> 𝒰 _
ModeHom M = Path (Edge (of graph M))


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


data Range : 𝒰₀ where
  vis : Range
  all : Range

private variable
  r : Range

data ModeTrans* (M : ModeSystem 𝑖) {a b : Mode M} : (r : Range) -> (μ η : ModeHom M a b) -> 𝒰 𝑖 where
  [_] : ∀{μ η} -> ModeTrans M vis μ η -> ModeTrans* M vis μ η
  [_∣_] : ∀{μ η ω} -> ModeTrans M invis μ η -> ModeTrans M vis η ω -> ModeTrans* M all μ ω

pattern idT = [ incl [] ∣ incl [] ]

-- private variable
--   M : ModeSystem 𝑖
--   a b c d e f : Mode M
--   μ : ModeHom M a b
--   η : ModeHom M b c
--   ω : ModeHom M c d

module _ {M : ModeSystem 𝑖} where

  open 2CellDefinition.2CellDefinition (graph M)
  open 2CellDecidability.2CellDecidability (graph M)

  _◆*₂ₘ_ : {a b : Mode M} -> {μ η ω : ModeHom M a b} -> ModeTrans* M r μ η -> ModeTrans* M r η ω -> ModeTrans* M r μ ω
  [ ξ ] ◆*₂ₘ [ ζ ] = [ ξ ◆₂ₘ ζ ]
  [ iξ ∣ vξ ] ◆*₂ₘ [ iζ ∣ vζ ] = let _ , iζ' , vξ' = commute M ⟨ vξ ⟩ ⟨ iζ ⟩ in [ iξ ◆₂ₘ incl iζ' ∣ incl vξ' ◆₂ₘ vζ ]


  _↷-ModeTrans*_ : {a b c : Mode M} -> (ϕ : ModeHom M a b)
                  -> {μ η : ModeHom M b c} -> ModeTrans* M r μ η
                  -> ModeTrans* M r (ϕ ◆ μ) (ϕ ◆ η)
  ϕ ↷-ModeTrans* [ ξ ] = [ incl (ϕ ⧕ ⟨ ξ ⟩) ]
  ϕ ↷-ModeTrans* [ iξ ∣ vξ ] = [ incl (ϕ ⧕ ⟨ iξ ⟩) ∣ incl (ϕ ⧕ ⟨ vξ ⟩) ]

  _↶-ModeTrans*_ : {a b c : Mode M}
                  -> {μ η : ModeHom M a b} -> ModeTrans* M r μ η
                  -> (ϕ : ModeHom M b c)
                  -> ModeTrans* M r (μ ◆ ϕ) (η ◆ ϕ)
  [ ξ ] ↶-ModeTrans* ϕ = [ incl (⟨ ξ ⟩ ⧔ ϕ) ]
  [ iξ ∣ vξ ] ↶-ModeTrans* ϕ = [ incl (⟨ iξ ⟩ ⧔ ϕ) ∣ incl (⟨ vξ ⟩ ⧔ ϕ) ]


  into-all-ModeTrans* : {a b : Mode M}
                  -> {μ η : ModeHom M a b} -> ModeTrans* M vis μ η
                  -> ModeTrans* M all (μ) (η)
  into-all-ModeTrans* [ ξ ] = [ incl [] ∣ ξ ]


  split-all-ModeTrans* : {a b : Mode M}
                  -> {μ ω : ModeHom M a b} -> ModeTrans* M all μ ω
                  ->  ∑ λ η -> ModeTrans* M all (μ) (η) ×-𝒰 ModeTrans* M vis η ω
  split-all-ModeTrans* [ iξ ∣ vξ ] = _ , [ iξ ∣ incl [] ] , [ vξ ]


  decide-≡-ModeTrans* : {a b : Mode M} -> {μ η : ModeHom M a b} -> (x y : ModeTrans* M r μ η) → isDecidable (x ≡ y)
  decide-≡-ModeTrans* [ incl x ] [ incl x₁ ] with x ≟ x₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  decide-≡-ModeTrans* ([_∣_] {η = η} (incl iξ) (incl vξ)) ([_∣_] {η = η₁} (incl iζ) (incl vζ)) with η ≟ η₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with iξ ≟ iζ
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with vξ ≟ vζ
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl


  instance
    hasDecidableEquality:ModeTrans* : {a b : Mode M} -> {μ η : ModeHom M a b} -> hasDecidableEquality (ModeTrans* M r μ η)
    hasDecidableEquality:ModeTrans* = record { _≟_ = decide-≡-ModeTrans* }

  -- _◆ₘ_ : ∀{r} -> {a b c : Mode M} -> ∀{μ₀ η₀ : ModeHom M a b} {μ₁ η₁ : ModeHom M b c}
  --     -> ModeTrans M r μ₀ η₀ -> ModeTrans M r μ₁ η₁ -> ModeTrans M r (μ₀ ◆ μ₁) (η₀ ◆ η₁)
  -- _◆ₘ_ = {!!}

  _◆ₘ*_ : ∀{r} ->  {a b c : Mode M} -> ∀{μ₀ η₀ : ModeHom M a b} {μ₁ η₁ : ModeHom M b c}
      -> ModeTrans* M r μ₀ η₀ -> ModeTrans* M r μ₁ η₁ -> ModeTrans* M r (μ₀ ◆ μ₁) (η₀ ◆ η₁)
  _◆ₘ*_ [ incl f ] [ incl g ]  = [ incl (f ⧓ g)]
  _◆ₘ*_ [ incl f0 ∣ incl f1 ] [ incl g0 ∣ incl g1 ]  = [ incl (f0 ⧓ g0) ∣ incl (f1 ⧓ g1)]

