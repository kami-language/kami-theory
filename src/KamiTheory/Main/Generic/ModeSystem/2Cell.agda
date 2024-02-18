

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

data Normal? : Set where
  normal notNormal : Normal?

module _ (G : 2Graph 𝑖) where

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    η : 1Cell G b c
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f


  -- We describe 2cells as following:
  --
  -- a --μ--> b --η--> c --ω--> d
  --
  --     ∥        ∥        ∥
  --  Id ∥      ξ ∥     Id ∥
  --     v        v        v
  --
  -- a --μ--> b --ε--> c --ω--> d

  -- Every 1cell can be partitioned into taken and untaken
  -- parts.

  FreeParts : 𝒰 _
  FreeParts = List (Modality G)

  -- n says how many taken parts we have
  data Partition : {a b : 0Cell G} (n : ℕ) (ϕs : FreeParts) (μ : 1Cell G a b) -> 𝒰 𝑖 where
    _⌟ : (μ : 1Cell G a b) -> Partition 0 ((a ↝ b ∋ μ) ∷ []) μ
    _⌟[_]⌞_ :   (μ : 1Cell G a b)
            -> (τ : 1Cell G b c)
            -> ∀{ϕs}
            -> {η : 1Cell G c d}
            -> Partition n ϕs η
            -> Partition (suc n) ((a ↝ b ∋ μ) ∷ ϕs) (μ ◆ τ ◆ η)

  infixr 40 _⌟[_]⌞_

  infixl 10 ⌞_

  ⌞_ : ∀{A : 𝒰 𝑖} -> A -> A
  ⌞_ a = a


  data SubPartition : {a b : 0Cell G} {m n : ℕ} {ϕs ψs : FreeParts}
                      {μ η : 1Cell G a b}
                      -> (μp : Partition m ϕs μ)
                      -> (ηp : Partition n ψs η)
                      -> 𝒰 𝑖
                      where





  -- A generator for the 2cells has a domain and codomain given by two partitions
  -- with the same free parts
  data 2CellGen (v : Visibility) :
                   {a b : 0Cell G} (ϕs : FreeParts) {μ η : 1Cell G a b}
                -> (μp : Partition n ϕs μ)
                -> (ηp : Partition n ϕs η)
                -> 𝒰 𝑖 where
    _⌟ : (μ : 1Cell G a b) -> 2CellGen v (a ↝ b ∋ μ ∷ []) (⌞ μ ⌟) (⌞ μ ⌟)
    _⌟[_]⌞_ : (ϕ : 1Cell G a b)
             -> (ξ : Face G v ξ₀ ξ₁)
             -> ∀{ϕs}
             -> {μp : Partition n ϕs μ}
             -> {ηp : Partition n ϕs η}
             -> 2CellGen v ϕs {μ} {η} μp ηp
             -> 2CellGen v (a ↝ b ∋ ϕ ∷ ϕs)
                         (ϕ ⌟[ ξ₀ ]⌞ μp)
                         (ϕ ⌟[ ξ₁ ]⌞ ηp)

  -- A (normal) 2cell is a sequence of matching 2CellGen(erators)
  data Normal2Cell (v : Visibility) {a b : 0Cell G} :
                {μ : 1Cell G a b} {ϕs : FreeParts}
                (μp : Partition n ϕs μ)
                (η : 1Cell G a b)
                -> 𝒰 𝑖 where

    id : Normal2Cell v (μ ⌟) μ
    [_by_]∷_ :
           {μ η ω : 1Cell G a b} {ϕs ψs : FreeParts}
           {μp  : Partition n ϕs μ}
           {η₀p : Partition n ϕs η}
           {η₁p : Partition m ψs η}
           -> 2CellGen v ϕs μp η₀p
           -> Normal2Cell v η₁p ω
           -> Normal2Cell v μp ω



{-

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

-}
