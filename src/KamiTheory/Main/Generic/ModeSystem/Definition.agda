
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Generic.ModeSystem.Definition where

open import Agora.Conventions


------------------------------------------------------------------------
-- We define the free strict 2-category
-- on a 2-graph. Thus, we need to talk about
-- the free 1-category on a graph already
-- in the input data. Thus we define it first.
--


---------------------------------------------
-- Free category on a graph

data Path {X : 𝒰 𝑖} (R : X -> X -> 𝒰 𝑗) : X -> X -> 𝒰 (𝑖 ､ 𝑗) where
  id : ∀{m} -> Path R m m
  _⨾_ : ∀{m n o} -> R m n  -> Path R n o -> Path R m o

infixr 80 _⨾_

_◆_ : ∀{X : 𝒰 𝑖} -> ∀{R : X -> X -> 𝒰 𝑗} -> ∀{m n k} -> Path R m n -> Path R n k -> Path R m k
id ◆ q = q
(x ⨾ p) ◆ q = x ⨾ (p ◆ q)

---------------------------------------------
-- Visibility parametrization
--
-- Each face has a visibility parameter, marking whether
-- this face should be tracked in the type system. This
-- means that the category of 2-cells is actually enriched
-- in the `Visibility` monoid.


data Visibility : Set where
  vis : Visibility
  invis : Visibility

_⋆_ : (v w : Visibility) -> Visibility
vis ⋆ w = vis
invis ⋆ w = w

---------------------------------------------
-- Input data for a free strict 2-category,
-- thus a 2-graph

record 2Graph (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field Point : 𝒰 (𝑖 ⌄ 0)
  field Edge : Point -> Point -> 𝒰 (𝑖 ⌄ 1)
  field Face : ∀{p q : Point} -> (a b : Path Edge p q) -> Visibility -> 𝒰 (𝑖 ⌄ 2)

open 2Graph public


------------------------------------------------------------------------
-- Working with a generated 2 category
--

---------------------------------------------
-- We describe the 0-cells

0Cell : 2Graph 𝑖 -> 𝒰 _
0Cell G = Point G

---------------------------------------------
-- We describe the 1-cells

1Cell : (G : 2Graph 𝑖) -> (p q : 0Cell G) -> 𝒰 _
1Cell G = Path (Edge G)

---------------------------------------------
-- We describe the 2-cells


module _ (G : 2Graph 𝑖) where

  data 2Cell : {m n : Point G} (μs ηs : Path (Edge G) m n) -> Visibility -> 𝒰 𝑖 where
    id : ∀{m n} -> {μs : 1Cell G m n} -> 2Cell μs μs invis

    gen : ∀{m n v} -> {α β : 1Cell G m n}
          -> Face G α β v
          -> 2Cell α β v

    _⨾_ : ∀{m n k v w} -> {α₀ α₁ : 1Cell G m n} -> {β₀ β₁ : 1Cell G n k}
          -> 2Cell α₀ α₁ v
          -> 2Cell β₀ β₁ w
          -> 2Cell (α₀ ◆ β₀) (α₁ ◆ β₁) (v ⋆ w)

    _◇_ : ∀{m n v w} -> {α β γ : 1Cell G m n}
          -> 2Cell α β v
          -> 2Cell β γ w
          -> 2Cell α γ (v ⋆ w)


------------------------------------------------------------------------
-- A mode system is given by

record ModeSystem 𝑖 : 𝒰 (𝑖 ⁺) where
  field Generators : 2Graph 𝑖


---------------------------------------------
-- Convenience definitions for accessing
-- the mode data

Mode : 2Graph 𝑖 -> 𝒰 _
Mode G = Point G

ModeHom : (G : 2Graph 𝑖) -> (m n : Mode G) -> 𝒰 _
ModeHom G = Path (Edge G)

ModeTrans : (G : 2Graph 𝑖) -> ∀{m n} -> (μ η : ModeHom G m n) -> Visibility -> 𝒰 _
ModeTrans G = 2Cell G


---------------------------------------------
-- A modality is a mode morphism with arbitrary
-- domain and codomain

record Modality (G : 2Graph 𝑖) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
  constructor _↝_∋_
  field dom : Mode G
  field cod : Mode G
  field hom : ModeHom G dom cod

infixl 40 _↝_∋_

open Modality public


---------------------------------------------
-- A transition is a mode transformation with arbitrary
-- domain and codomain

record Transition (G : 2Graph 𝑖) (v : Visibility) : 𝒰 𝑖 where
  constructor _⇒_∋_
  field {dom-Mode} : Mode G
  field {cod-Mode} : Mode G
  field dom : ModeHom G dom-Mode cod-Mode
  field cod : ModeHom G dom-Mode cod-Mode
  field trans : ModeTrans G dom cod v

