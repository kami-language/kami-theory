
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Graph.Definition where

open import Agora.Conventions
open import KamiTheory.Basics

{-# BUILTIN REWRITE _≡_ #-}


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


module _ {X : 𝒰 𝑖} {R : X -> X -> 𝒰 𝑗} where
  _◆_ : ∀{m n k} -> Path R m n -> Path R n k -> Path R m k
  id ◆ q = q
  (x ⨾ p) ◆ q = x ⨾ (p ◆ q)

  infixr 30 _◆_

  assoc-◆ : ∀{m n k l} -> (p : Path R m n) -> (q : Path R n k) -> (r : Path R k l)
          -> (p ◆ q) ◆ r ≡ p ◆ q ◆ r
  assoc-◆ id q r = refl
  assoc-◆ (x ⨾ p) q r = cong-≡ (x ⨾_) (assoc-◆ p q r)

  {-# REWRITE assoc-◆ #-}

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

_⋆-Visibility_ : (v w : Visibility) -> Visibility
vis ⋆-Visibility w = vis
invis ⋆-Visibility w = w

instance
  hasNotation-⋆:Visibility : hasNotation-⋆ Visibility (λ _ -> Visibility) (λ _ _ -> Visibility)
  hasNotation-⋆:Visibility = record { _⋆_ = _⋆-Visibility_ }

---------------------------------------------
-- Input data for a free strict 2-category,
-- thus a 2-graph. We require the graph to be decidable.

record 2Graph (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field Point : 𝒰 (𝑖 ⌄ 0)
  field Edge : Point -> Point -> 𝒰 (𝑖 ⌄ 1)
  field Face : Visibility -> ∀{p q : Point} -> (a b : Path Edge p q) -> 𝒰 (𝑖 ⌄ 2)

  field {{decide-≡-Point}} : hasDecidableEquality Point
  field {{decide-≡-Edge}} : ∀{a b} -> hasDecidableEquality (Edge a b)
  field {{decide-≡-Face}} : ∀{a b} -> {p q : Path Edge a b} -> ∀{v} -> hasDecidableEquality (Face v p q)

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

-- ModeTrans : (G : 2Graph 𝑖) -> ∀{m n} -> (μ η : ModeHom G m n) -> Visibility -> 𝒰 _
-- ModeTrans G = 2Cell G



------------------------------------------------------------------------
-- Decidability

-- record isDecidable2Graph (G : 2Graph 𝑖) : 𝒰 𝑖 where
--   field decide-≡-Point : (a b : Point G) -> isDecidable (a ≡ b)
--   field decide-≡-Edge : ∀{a b} -> (p q : Edge G a b) -> isDecidable (p ≡ q)
--   field decide-≡-Face : ∀{a b} -> {p q : Path (Edge G) a b} -> ∀{v} -> {s t : Face G p q v} -> isDecidable (s ≡ t)

-- open isDecidable2Graph {{...}} public



