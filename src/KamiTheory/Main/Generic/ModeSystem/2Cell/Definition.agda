
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Definition where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
-- open import KamiTheory.Main.Generic.ModeSystem.LinearFSM.Definition
open import KamiTheory.Order.StrictOrder.Base

open import Data.Fin using (Fin ; zero ; suc)




module 2CellDefinition (G : 2Graph 𝑖) where

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    η : 1Cell G b c
    ω : 1Cell G c d
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f
    v : Visibility


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

  infixr 42 _⌟
  infixl 38 ⌞_

  ⌞_ : ∀{A : 𝒰 𝑖} -> A -> A
  ⌞_ a = a

  ---------------------------------------------
  -- ∃Partitions

  record ∃Partition {a b : 0Cell G} (μ : 1Cell G a b) : 𝒰 𝑖 where
    constructor incl
    field {size} : ℕ
    field {freeParts} : FreeParts a b
    field get : Partition size freeParts μ

  open ∃Partition public


  data _≤-∃Partition_ : ∀{a b : 0Cell G} {μ : 1Cell G a b}
                        -> (π σ : ∃Partition μ)
                        -> 𝒰 𝑖 where


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



  ---------------------------------------------
  -- Patterns
  --
  -- Reduction rules are given by patterns.








  -- If we have a μ₁ part of a 1Cell μ, and a partition of it, then we can
  -- get the subpartition which belongs to the μ₁

  -- extract : {a b c d : 0Cell G}
  --           (μ₀ : 1Cell G a b)
  --           (μ₁ : 1Cell G b c)
  --           (μ₂ : 1Cell G c d)
  --           (π : ∃Partition (μ₀ ◆ μ₁ ◆ μ₂))
  --           -> ∑ λ (π₁ : ∃Partition μ₁)
  --             -> (μ₀ ⋊ π₁ ⋉ μ₂) ≤-∃Partition π
  -- extract id μ₁ μ₂ π = {!!}
  -- extract (x ⨾ μ₀) μ₁ μ₂ π = {!!}





  -- A generator for the 2cells has a domain and codomain given by two partitions
  -- with the same free parts
  data 2CellGen (v : Visibility) :
                   {a b : 0Cell G} (ϕs : FreeParts a b) {μ η : 1Cell G a b}
                -> (μp : Partition n ϕs μ)
                -> (ηp : Partition n ϕs η)
                -> 𝒰 𝑖 where
    _⌟ : (μ : 1Cell G a b) -> 2CellGen v [ μ ] (⌞ μ ⌟) (⌞ μ ⌟)
    _⌟[_]⌞_ : (ϕ : 1Cell G a b)
             -> (ξ : Face G v ξ₀ ξ₁)
             -> ∀{ϕs}
             -> {μp : Partition n ϕs μ}
             -> {ηp : Partition n ϕs η}
             -> 2CellGen v ϕs {μ} {η} μp ηp
             -> 2CellGen v (ϕ ∷ ϕs)
                         (ϕ ⌟[ ξ₀ ]⌞ μp)
                         (ϕ ⌟[ ξ₁ ]⌞ ηp)

  gen←base : ∀{v} -> (ξ : Face G v ξ₀ ξ₁)  -> 2CellGen v _ _ _
  gen←base ξ = ⌞ id ⌟[ ξ ]⌞ id ⌟

  record Some2CellGen (v : Visibility) {a b : 0Cell G}
                (μ : 1Cell G a b)
                (η : 1Cell G a b)
                : 𝒰 𝑖 where
    constructor incl
    field {size} : ℕ
    field {freeParts} : FreeParts a b
    field {domPartition} : Partition size freeParts μ
    field {codPartition} : Partition size freeParts η
    field get : 2CellGen v freeParts domPartition codPartition

  open Some2CellGen public



  join-2CellGen : {v : Visibility}
          {a b c : 0Cell G}

          -- The first 2cell generator
          -> {ϕs : FreeParts a b}
          -> {μ₀ μ₁ : 1Cell G a b}
          -> {μ₀p : Partition m ϕs μ₀}
          -> {μ₁p : Partition m ϕs μ₁}
          -> (ξ : 2CellGen v ϕs μ₀p μ₁p)

          -- The second 2cell generator
          -> {ψs : FreeParts b c}
          -> {η₀ η₁ : 1Cell G b c}
          -> {η₀p : Partition n ψs η₀}
          -> {η₁p : Partition n ψs η₁}
          -> (ζ : 2CellGen v ψs η₀p η₁p)

          -- The horizontal composition
          -> 2CellGen v (join-FreeParts ϕs ψs) (join μ₀p η₀p) (join μ₁p η₁p)

  join-2CellGen (ϕ ⌟) (ψ ⌟) = (ϕ ◆ ψ) ⌟
  join-2CellGen (ϕ ⌟) (ψ ⌟[ ξ ]⌞ ζ) = (ϕ ◆ ψ) ⌟[ ξ ]⌞ ζ
  join-2CellGen (ϕ ⌟[ ξ ]⌞ ξs) ζ = ϕ ⌟[ ξ ]⌞ (join-2CellGen ξs ζ)


  _⧓_ : {v : Visibility} {a b c : 0Cell G}
          -> {μ₀ μ₁ : 1Cell G a b}
          -> {η₀ η₁ : 1Cell G b c}
          -> Some2CellGen v μ₀ μ₁
          -> Some2CellGen v η₀ η₁
          -> Some2CellGen v (μ₀ ◆ η₀) (μ₁ ◆ η₁)
  (incl ξ) ⧓ (incl ζ) = incl (join-2CellGen ξ ζ)

  _⧕_ : {v : Visibility} {a b c : 0Cell G}
          -> (ϕ : 1Cell G a b)
          -> {η₀ η₁ : 1Cell G b c}
          -> Some2CellGen v η₀ η₁
          -> Some2CellGen v (ϕ ◆ η₀) (ϕ ◆ η₁)
  _⧕_ ϕ ξ = incl (ϕ ⌟) ⧓ ξ



  ----------------------------------------------------------
  -- 2Cells


  -- A (normal) 2cell is a sequence of matching 2CellGen(erators)
  data Normal2Cell (v : Visibility) {a b : 0Cell G} :
                {μ : 1Cell G a b} {ϕs : FreeParts a b}
                (μp : Partition n ϕs μ)
                (η : 1Cell G a b)
                -> 𝒰 𝑖 where

    id : Normal2Cell v (μ ⌟) μ
    [_by_]∷_ :
           {μ η ω : 1Cell G a b} {ϕs ψs : FreeParts a b}
           {μp  : Partition n ϕs μ}
           {η₀p : Partition n ϕs η}
           {η₁p : Partition m ψs η}
           -> 2CellGen v ϕs μp η₀p
           -> Normal2Cell v η₁p ω
           -> Normal2Cell v μp ω


  data 2Cell (v : Visibility) {a b : 0Cell G} :
                (μ : 1Cell G a b)
                (η : 1Cell G a b)
                -> 𝒰 𝑖 where
    [] : 2Cell v μ μ
    _∷_ : Some2CellGen v μ η -> 2Cell v η ω -> 2Cell v μ ω

  _◆₂_ : ∀{v} -> 2Cell v μ η -> 2Cell v η ω -> 2Cell v μ ω
  [] ◆₂ b = b
  (x ∷ a) ◆₂ b = x ∷ (a ◆₂ b)



  ----------------------------------------------------------
  -- Merging 2CellGen's

  data 2CellGenSubst (v : Visibility) : FreeParts a b -> 𝒰 𝑖 where


  -- Compute the freeparts of the bottom cellgen, which should be less
  -- than before
  -- bottomFreeParts : (η : 1Cell G a b) {ϕs ψs : FreeParts a b}
  --                   (η₀p : Partition n ϕs η)
  --                   (η₁p : Partition m ψs η)
  --                   -> FreeParts a b
  -- bottomFreeParts η (.η ⌟) (.η ⌟) = {!!}
  -- bottomFreeParts .(μ ◆ τ ◆ _) (.(μ ◆ τ ◆ _) ⌟) (μ ⌟[ τ ]⌞ y) = {!!}
  -- bottomFreeParts .(μ ◆ τ ◆ _) (μ ⌟[ τ ]⌞ x) y = {!!}


  -- Given a cellgen and a face with a 1cell-prefix, we
  -- try to insert it
  insertFace : {v : Visibility}
           -- the 2cellgen into which we want to insert
           {μ η : 1Cell G a d} {ϕs : FreeParts a d}
           {μp  : Partition n ϕs μ}
           {ηp : Partition n ϕs η}
           (ζ : 2CellGen v ϕs μp ηp)

           -- the prefix of the face
           (εₗ : 1Cell G a b)
           -- the top and bottom boundaries
           {top bottom : 1Cell G b c}
           -- the face itself
           (ξ : Face G v top bottom)

           -- We only return a value if we are succesfull
           -> Maybe (Some2CellGen v μ η)
  insertFace (_ ⌟) εₗ ξ = {!!}
  insertFace (ϕ ⌟[ ξ₁ ]⌞ ζ) εₗ ξ = {!!}


  -- Given two 2cellgens, we can push down all taken parts which fit into
  -- the bottom cellgen.
  pushDownTaken : {v : Visibility} ->
        -- μₗ (ηₗ) is the top (bottom) boundary of the already processed cell
        -- We iterate over a partition of ξᵣ between μᵣ and ηᵣ
        {μₗ : 1Cell G a b} {μᵣ : 1Cell G b c}
        {ηₗ : 1Cell G a b} {ηᵣ : 1Cell G b c}
        -- Our current result is in ξₗ
        (ξₗ : Some2CellGen v μₗ ηₗ)
        -- Our todo list is in ξᵣ
        {ϕs : FreeParts b c}
        {μᵣp : Partition n ϕs μᵣ}
        {ηᵣp : Partition n ϕs ηᵣ}
        (ξᵣ : 2CellGen v ϕs μᵣp ηᵣp)
        -- The bottom cell into which we insert goes from
        -- ηₗ ◆ ηᵣ to ω
        (ζ : Some2CellGen v (ηₗ ◆ ηᵣ) ω)
        -- We return two new cells
        -> (Some2CellGen v (μₗ ◆ μᵣ) (ηₗ ◆ ηᵣ)
          ×-𝒰 Some2CellGen v (ηₗ ◆ ηᵣ) ω)
  pushDownTaken ξₗ (_ ⌟) ζ = {!!}
  -- Case 2: We have a taken face ξ in ξᵣ.
  --         Thus we try to insert ξ down into ζ.
  pushDownTaken ξₗ (ϕ ⌟[ ξ ]⌞ ξᵣ) ζ = {!!}

-- {μ η ω : 1Cell G a b} {ϕs ψs : FreeParts a b}
--            {μp  : Partition n ϕs μ}
--            {η₀p : Partition n ϕs η}
--            {η₁p : Partition m ψs η}
--            {ωp  : Partition m ψs ω}
--            -> 2CellGen v ϕs μp η₀p
--            -> 2CellGen v ψs η₁p ωp
--            -> 





  ----------------------------------------------------------
  -- Commutation

  -- We can commute the visibile and invisible cells. This is required
  -- for substitution under `transform` terms in our type theory.
  -- commute-vis : (ξ : 2Cell vis μ η) -> (ζ : 2Cell invis η ω) ->
  --               ∑ λ η' -> (2Cell invis μ η' ×-𝒰 2Cell vis η' ω)
  -- commute-vis = {!!}





