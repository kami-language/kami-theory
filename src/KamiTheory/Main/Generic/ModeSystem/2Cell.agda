

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

data Normal? : Set where
  normal notNormal : Normal?

-- data NonEmptyList (A : 𝒰 𝑖) : 𝒰 𝑖 where
--   [_] : (a : A) -> NonEmptyList A
--   _∷_ : (a : A) -> (as : NonEmptyList A) -> NonEmptyList A

-- mapFirst : ∀{A : 𝒰 𝑖} -> (f : A -> A) -> NonEmptyList A -> NonEmptyList A
-- mapFirst f [ a ] = [ f a ]
-- mapFirst f (a ∷ as) = f a ∷ as


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

  -- FreeParts : 𝒰 _
  -- FreeParts = NonEmptyList (Modality G)

  data FreeParts : (a b : 0Cell G) -> 𝒰 𝑖 where
    [_] : (ϕ : 1Cell G a b) -> FreeParts a b
    _∷_ : (ϕ : 1Cell G a b) -> (ϕs : FreeParts c d) -> FreeParts a d

  private variable
    ϕs : FreeParts a b
    ψs : FreeParts c d


  -- n says how many taken parts we have
  data Partition : {a b : 0Cell G} (n : ℕ) (ϕs : FreeParts a b) (μ : 1Cell G a b) -> 𝒰 𝑖 where
    _⌟ : (μ : 1Cell G a b) -> Partition 0 [ μ ] μ
    _⌟[_]⌞_ :   (μ : 1Cell G a b)
            -> (τ : 1Cell G b c)
            -> ∀{ϕs}
            -> {η : 1Cell G c d}
            -> Partition n ϕs η
            -> Partition (suc n) (μ ∷ ϕs) (μ ◆ τ ◆ η)

  infixr 40 _⌟[_]⌞_

  infixr 40 _⌟
  infixl 38 ⌞_

  ⌞_ : ∀{A : 𝒰 𝑖} -> A -> A
  ⌞_ a = a

  record ∃Partition {a b : 0Cell G} (μ : 1Cell G a b) : 𝒰 𝑖 where
    constructor incl
    field {size} : ℕ
    field {freeParts} : FreeParts a b
    field get : Partition size freeParts μ

  open ∃Partition public


  join-FreeParts : (ϕs : FreeParts a b) -> (ψs : FreeParts b c) -> FreeParts a c
  join-FreeParts [ ϕ ] [ ψ ] = [ ϕ ◆ ψ ]
  join-FreeParts [ ϕ ] (ψ ∷ ψs) = (ϕ ◆ ψ) ∷ ψs
  join-FreeParts (ϕ ∷ ϕs) ψs = ϕ ∷ join-FreeParts ϕs ψs

  join : {μ : 1Cell G a b} -> {η : 1Cell G b c}
         -> Partition m ϕs μ -> Partition n ψs η -> Partition (m +-ℕ n) (join-FreeParts ϕs ψs) (μ ◆ η)
  join (ϕ ⌟) (ψ ⌟) = (ϕ ◆ ψ) ⌟
  join (ϕ ⌟) (ψ ⌟[ τ ]⌞ ηs) = (ϕ ◆ ψ) ⌟[ τ ]⌞ ηs
  join (ϕ ⌟[ τ ]⌞ μs) ηs = ϕ ⌟[ τ ]⌞ join μs ηs


  -- We temporarily use ⋈ ⋊ ⋉ for concatenation on partitions
  _⋈_ : ∃Partition μ -> ∃Partition η -> ∃Partition (μ ◆ η)
  incl a ⋈ incl b = incl (join a b)

  _⋉_ : ∃Partition μ -> (η : 1Cell G a b) -> ∃Partition (μ ◆ η)
  μp ⋉ η = μp ⋈ incl (η ⌟)

  _⋊_ : (μ : 1Cell G a b) -> ∃Partition η -> ∃Partition (μ ◆ η)
  μ ⋊ ηp = incl (μ ⌟) ⋈ ηp

  infixr 30 _⋈_
  infixl 30 _⋉_
  infixr 28 _⋊_



  data _≤-∃Partition_ : ∀{a b : 0Cell G} {μ : 1Cell G a b}
                        -> (π σ : ∃Partition μ)
                        -> 𝒰 𝑖 where



  -- If we have a μ₁ part of a 1Cell μ, and a partition of it, then we can
  -- get the subpartition which belongs to the μ₁

  extract : {a b c d : 0Cell G}
            (μ₀ : 1Cell G a b)
            (μ₁ : 1Cell G b c)
            (μ₂ : 1Cell G c d)
            (π : ∃Partition (μ₀ ◆ μ₁ ◆ μ₂))
            -> ∑ λ (π₁ : ∃Partition μ₁)
              -> (μ₀ ⋊ π₁ ⋉ μ₂) ≤-∃Partition π
  extract id μ₁ μ₂ π = {!!}
  extract (x ⨾ μ₀) μ₁ μ₂ π = {!!}


{-



  -- A generator for the 2cells has a domain and codomain given by two partitions
  -- with the same free parts
  data 2CellGen (v : Visibility) :
                   {a b : 0Cell G} (ϕs : FreeParts) {μ η : 1Cell G a b}
                -> (μp : Partition n ϕs μ)
                -> (ηp : Partition n ϕs η)
                -> 𝒰 𝑖 where
    _⌟ : (μ : 1Cell G a b) -> 2CellGen v [ a ↝ b ∋ μ ] (⌞ μ ⌟) (⌞ μ ⌟)
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

-}
