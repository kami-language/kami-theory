-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

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

  unit-r-◆ : ∀{m n} -> (p : Path R m n) -> p ◆ id ≡ p
  unit-r-◆ id = refl
  unit-r-◆ (x ⨾ p) = cong-≡ (x ⨾_) (unit-r-◆ p)

  {-# REWRITE unit-r-◆ #-}

  module _ {{_ : hasDecidableEquality X}} {{_ : ∀{m n : X} -> hasDecidableEquality (R m n)}} where

    decide-≡-Path : ∀{m n} -> (x y : Path R m n) → isDecidable (x ≡ y)
    decide-≡-Path id id = yes refl-≡
    decide-≡-Path id (x ⨾ l) = no (λ ())
    decide-≡-Path (x ⨾ k) id = no (λ ())
    decide-≡-Path (_⨾_ {n = n} x k) (_⨾_ {n = n₁} y l) with n ≟ n₁
    ... | no p = no λ {refl -> p refl}
    ... | yes refl with x ≟ y
    ... | no p = no λ {refl -> p refl}
    ... | yes refl with decide-≡-Path k l
    ... | no p = no λ {refl -> p refl}
    ... | yes refl = yes refl

    instance
      hasDecidableEquality:Path : ∀{m n} -> hasDecidableEquality (Path R m n)
      hasDecidableEquality:Path = record { _≟_ = decide-≡-Path }

    β-decide-≡-Path : ∀{m n} -> {x : Path R m n} -> decide-≡-Path x x ≡ yes refl
    β-decide-≡-Path = {!!}

    {-# REWRITE β-decide-≡-Path #-}

    module _ {{_ : ∀{a b} -> hasShow (R a b)}} where

      show-Path : ∀{a b} -> (Path R a b) -> String
      show-Path id = "id"
      show-Path (x ⨾ p) = show x <> " ; " <> show-Path p

      instance
        hasShow:Path : ∀{a b} -> hasShow (Path R a b)
        hasShow:Path = record { show = show-Path }


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

record is2Graph (𝑗 : 𝔏 ^ 2) (Point : 𝒰 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  -- field Point : 𝒰 (𝑖 ⌄ 0)
  field Edge : Point -> Point -> 𝒰 (𝑗 ⌄ 0)
  field Face : Visibility -> ∀{p q : Point} -> (a b : Path Edge p q) -> 𝒰 (𝑗 ⌄ 1)

  field {{decide-≡-Point}} : hasDecidableEquality Point
  field {{decide-≡-Edge}} : ∀{a b} -> hasDecidableEquality (Edge a b)
  field {{decide-≡-Face}} : ∀{a b} -> {p q : Path Edge a b} -> ∀{v} -> hasDecidableEquality (Face v p q)

  field {{hasShow:Edge}} : ∀{a b} -> hasShow (Edge a b)

open is2Graph public

2Graph : (𝑖 : 𝔏 ^ 3) -> 𝒰 (𝑖 ⁺)
2Graph 𝑖 = 𝒰 (𝑖 ⌄ 0) :& is2Graph (𝑖 ⌄ 1 ⋯ 2)

Point : 2Graph 𝑖 -> 𝒰 _
Point G = ⟨ G ⟩



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
1Cell G = Path (Edge (of G))



