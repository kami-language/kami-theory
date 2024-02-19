

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Definition where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality

open import Data.Fin using (Fin ; zero ; suc)

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
    ω : 1Cell G c d
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



  -------------------
  -- 2Cell patterns

  record SingleFace v (a d : 0Cell G) : 𝒰 𝑖 where
    constructor _⌟[_]⌞_
    field {pb pc} : 0Cell G
    field idₗ : 1Cell G a pb
    field {cξ₀ cξ₁} : 1Cell G pb pc
    field face : Face G v cξ₀ cξ₁
    field idᵣ : 1Cell G pc d

  open SingleFace public

  as2CellGen : ∀{v} -> (ξ : SingleFace v a d) -> Some2CellGen v ((ξ .idₗ) ◆ (ξ .cξ₀) ◆ (ξ .idᵣ)) ((ξ .idₗ) ◆ (ξ .cξ₁) ◆ (ξ .idᵣ))
  as2CellGen (μ ⌟[ ξ ]⌞ η) = incl (μ ⌟[ ξ ]⌞ η ⌟)

  -- ⌞_◆_◆_⌟ : 1Cell G a b -> SingleFace b c -> 1Cell G c d -> SingleFace a d
  -- ⌞_◆_◆_⌟ = {!!}

  record SubSingleFace v {a d : 0Cell G} (ξ : SingleFace v a d) : 𝒰 𝑖 where
    field {a' d'} : 0Cell G
    field extₗ : 1Cell G a a'
    field keepₗ : 1Cell G a' (ξ .pb)
    field keepᵣ : 1Cell G (ξ .pc) d'
    field extᵣ : 1Cell G d' d
    field proofₗ : extₗ ◆ keepₗ ≡ ξ .idₗ
    field proofᵣ : keepᵣ ◆ extᵣ ≡ ξ .idᵣ

  open SubSingleFace public

    -- field extᵣ : 1Cell G pc d
    -- field proofₗ :
    -- ⌞ extₗ ◆ subface ◆ extᵣ ⌟ ≡ ξ

  -- A pattern allows us to match existing 2cells with
  -- others, while having "free variables". We currently
  -- only support "line" patterns, where there is only single
  -- face in each row.
  record 2CellLinePattern v 𝑗 (n : ℕ) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
    field State : ℕ -> 𝒰 𝑗
    field start : State zero
    field step : ∀{i} -> (s : State i)
                 -> ∀{a b}
                 -> (ξ : SingleFace v a b)
                 -> Maybe (SubSingleFace v ξ ×-𝒰 State (suc i))

  open 2CellLinePattern public

  record SplitGen v {a d : 0Cell G} (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⧓⌞_⌟⧓_[_,_]
    field {pb pc} : 0Cell G
    field {left₀ left₁} : 1Cell G a pb
    field {right₀ right₁} : 1Cell G pc d
    field leftξ : Some2CellGen v left₀ left₁
    field center : SingleFace v pb pc
    field rightξ : Some2CellGen v right₀ right₁
    field proof₀ : left₀ ◆ (center .idₗ ◆ center .cξ₀ ◆ center .idᵣ) ◆ right₀ ≡ μ
    field proof₁ : left₁ ◆ (center .idₗ ◆ center .cξ₁ ◆ center .idᵣ) ◆ right₁ ≡ η

  open SplitGen


  _↷-SplitGen_ : ∀{v} -> {ω₀ ω₁ : 1Cell G a b} -> (ξ : Some2CellGen v ω₀ ω₁) -> ∀{μ η : 1Cell G b c} -> SplitGen v μ η -> SplitGen v (ω₀ ◆ μ) (ω₁ ◆ η)
  _↷-SplitGen_ {ω₀ = ω₀} {ω₁} ξ (leftξ ⧓⌞ center ⌟⧓ rightξ [ proof₀ , proof₁ ]) = (ξ ⧓ leftξ) ⧓⌞ center ⌟⧓ rightξ [ cong-≡ (ω₀ ◆_) proof₀ , cong-≡ (ω₁ ◆_) proof₁ ]



  -- Given a pattern, we try to find the next matching face in a gen-row
  findNext : ∀{n}
             -> {v : Visibility}
             -> 2CellLinePattern v 𝑗 (suc n)
             -> {a b : 0Cell G} (ϕs : FreeParts a b) {μ η : 1Cell G a b}
             -> {μp : Partition m ϕs μ}
             -> {ηp : Partition m ϕs η}
             -> 2CellGen v ϕs μp ηp
             -> Maybe (SplitGen v μ η ×-𝒰 2CellLinePattern v 𝑗 n)
  findNext pat ([ ϕ ]) (ϕ ⌟) = nothing
  findNext pat (ϕ ∷ [ ψ ]) (ϕ ⌟[ ξ ]⌞ .ψ ⌟) with (pat .step (pat .start) (ϕ ⌟[ ξ ]⌞ ψ))

  ... | no x = nothing
  ... | yes (ξ₊ , s) = yes ((incl (ξ₊ .extₗ ⌟) ⧓⌞ ξ₊ .keepₗ ⌟[ ξ ]⌞ ξ₊ .keepᵣ ⌟⧓ incl (ξ₊ .extᵣ ⌟) [ {!!} , {!!} ])
                           , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

  findNext pat (ϕ ∷ (ψ ∷ ψs)) (ϕ ⌟[ ξ ]⌞ ξs) with (pat .step (pat .start) (ϕ ⌟[ ξ ]⌞ ψ))

  findNext pat (ϕ ∷ (ψ ∷ ψs)) (ϕ ⌟[ ξ ]⌞ .ψ ⌟[ ζ ]⌞ ξs) | yes (ξ₊ , s) =

        yes ((incl (ξ₊ .extₗ ⌟) ⧓⌞ ξ₊ .keepₗ ⌟[ ξ ]⌞ ξ₊ .keepᵣ ⌟⧓ (incl ((ξ₊ .extᵣ ) ⌟[ ζ ]⌞ ξs)) [ {!!} , {!!} ])

      , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

  ... | nothing with findNext pat _ ξs
  ... | nothing = nothing
  ... | yes ((incl leftξ ⧓⌞ center ⌟⧓ rightξ [ pf₀ , pf₁ ]) , nextpat) = yes ((incl (ϕ ⌟[ ξ ]⌞ leftξ) ⧓⌞ center ⌟⧓ rightξ [ {!!} , {!!} ])
                                                                   , nextpat
                                                                   )




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



  record Split v {a d : 0Cell G} (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⧓⌞_⌟⧓_
    field {pb pc} : 0Cell G
    field {left₀ left₁} : 1Cell G a pb
    field {center₀ center₁} : 1Cell G pb pc
    field {right₀ right₁} : 1Cell G pc d
    field leftξ : 2Cell v left₀ left₁
    field centerξ : 2Cell v center₀ center₁
    field rightξ : 2Cell v right₀ right₁

  open Split

  splitFromGen : ∀{v} -> SplitGen v μ η -> (Split v μ η)
  splitFromGen (leftξ ⧓⌞ center ⌟⧓ rightξ [ proof₀ , proof₁ ]) = (leftξ ∷ []) ⧓⌞ (as2CellGen center ∷ []) ⌟⧓ (rightξ ∷ [])

  tryMergeSplit : ∀{v} -> SplitGen v μ η -> Split v η ω -> Maybe (Split v μ ω)
  tryMergeSplit g s with pb s ≟ pb g | pc s ≟ pc g
  ... | no _ | Y = nothing
  ... | yes refl | no _ = nothing
  ... | yes refl | yes refl with decide-≡-Path (g .left₁) (s .left₀)
  ... | no x = nothing
  ... | yes refl with decide-≡-Path (g .right₁) (s .right₀)
  ... | no x = nothing
  ... | yes refl with decide-≡-Path (g .center .idₗ ◆ g .center .cξ₁ ◆ g .center .idᵣ) (s .center₀)
  ... | no x = nothing
  ... | yes refl = yes ((g .leftξ ∷ s .leftξ) ⧓⌞ as2CellGen (g .center) ∷ s .centerξ ⌟⧓ (g .rightξ ∷ s .rightξ))

  -- _↷-Split_ : ∀{v} -> {ω₀ ω₁ : 1Cell G a b} -> (ξ : Some2CellGen v ω₀ ω₁) -> ∀{μ η : 1Cell G b c} -> Split v μ η -> Split v (ω₀ ◆ μ) (ω₁ ◆ η)
  -- _↷-Split_ = {!!}



  --
  -- |---- overfind --->|
  -- | l  | center | r  |   | direction of 2cells
  -- |--- underfind --->|   v
  -- |----- bottom ---->|
  --
  record Result:findAllLocked v (overfind bottom : 1Cell G a d) : 𝒰 𝑖 where
    field underfind : 1Cell G a d
    field split : Split v overfind underfind
    field bottomξ : 2Cell v underfind bottom

  open Result:findAllLocked

  record Result:findAll v (top bottom : 1Cell G a d) : 𝒰 𝑖 where
    field {overfind} : 1Cell G a d
    field topξ : 2Cell v top overfind
    field result : Result:findAllLocked v overfind bottom

  open Result:findAll



  {-# TERMINATING #-}
  -- Under the assumption that we already "locked in" the 2CellLinePattern,
  -- find the rest of it downstream
  findAllLocked : ∀ n -> ∀ {m k v}
            -- The pattern we are searching for
            -> 2CellLinePattern v 𝑗 (suc n)

            -- We have two 1cells and corresponding current 2cellgens,
            -- one is on the left, which we already checked, and one is
            -- on the right, which we are going to check now
            -> {μ₀ μ₁ : 1Cell G a b}        -> {η₀ η₁ : 1Cell G b c}

            -> {ϕs : FreeParts a b}         -> {ψs : FreeParts b c}
            -> {μ₀p : Partition m ϕs μ₀}     -> {η₀p : Partition k ψs η₀}
            -> {μ₁p : Partition m ϕs μ₁}     -> {η₁p : Partition k ψs η₁}
            -> (ξ : 2CellGen v ϕs μ₀p μ₁p)  -> (ζ : 2CellGen v ψs η₀p η₁p)

            -- Next, we have the rest of the 2cell which is still left "downwards"
            -- (ω is the target 1cell of this whole 2cell)
            -> {ω : 1Cell G a c}
            -> 2Cell v (μ₁ ◆ η₁) ω

            -- We return a split of the upsteam 2cell if we find the pattern
            -> String +-𝒰 (Result:findAllLocked v (μ₀ ◆ η₀) (ω))

  -- We recurse on ζ:
  --
  -- Case 1: if ζ is empty, this means we found nothing in the current
  --         row, so we can return
  findAllLocked n pat ξ (_ ⌟) rest = left "ζ empty case 1"
  --
  -- Case 2: if ζ is not empty, try to find the next face which satisfies the pattern
  findAllLocked n {v = v} pat {μ₁ = μ₁} {η₁ = η₁} ξ ζs@(ϕ ⌟[ ξ₁ ]⌞ ζ) rest with findNext pat _ ζs
  --
  -- Case 2.1: Nothing was found in the current row. So exit.
  ... | no x = no "end 2.1"
  --
  -- Case 2.2: We found a satisfying face.
  --           This means the following:
  --             - We have to call ourselves recursively, to try to
  --               find the rest of the pattern.
  --             - If the recursive call does not work out, we still
  --               continue to search the current line, with the right-part
  --               of the currently returned `SplitGen`, as it might be that
  --               another satisfying face is hiding behind the current one
  --
  --           But, first we need to check whether n is now zero, because if
  --           it is, this means that we finished the whole pattern!
  --
  -- Case 2.2.1: (n = 0): We finished the pattern!
  findAllLocked zero pat ξ (_ ⌟[ ξ₁ ]⌞ ζ) rest | yes (sp , pat2) =
    let x = sp
    in yes (record
      { underfind = _
      ; split = splitFromGen (incl ξ ↷-SplitGen sp)
      ; bottomξ = rest
      })
  --
  -- Case 2.2.2: (n > 0): We still have to search
  --
  -- Case 2.2.2.1: But we don't have any rest-2cell left over (rest = []), so we
  --               cannot complete the pattern. Thus return nothing.
  findAllLocked (suc n) pat ξ (_ ⌟[ ξ₁ ]⌞ ζ) [] | yes (sp , pat2) = no "end 2.2.2.1"
  --
  -- Case 2.2.2.2: We have a rest, and we can take a ζ-new with which to
  --               initialize the recursive call. We also use the new pattern `pat2`
  findAllLocked (suc n) {v = v} pat {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest) | yes (sp@(_⧓⌞_⌟⧓_[_,_] {left₁ = left₁} {right₁ = right₁} foundₗ found foundᵣ pf₀ pf₁ ) , pat2) with findAllLocked n pat2 (id ⌟) (ζ-new .get) rest
  --
  -- Case 2.2.2.2.1: The recursive call was successful!
  --                 That means that we have to merge the recursive Split with the currently gotten SplitGen
  --                 We have:
  --                  - sp     : SplitGen v (ϕ ◆ ξ₀ ◆ μ) (ϕ ◆ ξ₂ ◆ η₂)
  --                  - res     : Result:findAllLocked v (μ₁ ◆ ϕ ◆ ξ₂ ◆ η₂) ω
  --                 This means that first we can add μ₁ on the left side of sp, by doing (μ₁ ↷-SplitGen sp),
  --                 and then we try to merge with the split in res.
  ... | yes res with tryMergeSplit (incl ξ ↷-SplitGen sp) (res .split)
  --
  -- Case 2.2.2.2.1.1: The merging was successful. This means this is our new result, and we can return :)
  ... | yes newsplit = yes (record { underfind = _ ; split = newsplit ; bottomξ = res .bottomξ })
  --
  -- Case 2.2.2.2.1.2: The merging was not successful, back to the drawing board! We do the same thing as in
  --                   case 2.2.2.2.2
  findAllLocked (suc n) {v = v} pat {μ₀ = μ₀} {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest)
    | yes (sp@(_⧓⌞_⌟⧓_[_,_] {left₀ = left₀} {left₁ = left₁} {right₀ = right₀} {right₁ = right₁} foundₗ found foundᵣ pf₀ pf₁ ) , pat2)
    | yes res
    | no p with findAllLocked (suc n) pat (get (incl ξ ⧓ (foundₗ ⧓ as2CellGen found ))) (foundᵣ .get) (ζ-new' ∷ rest)

    where ζ-new' : Some2CellGen _ (μ₁ ◆ left₁ ◆ found .idₗ ◆ found .cξ₁ ◆ found .idᵣ ◆ right₁) _
          ζ-new' = transp-≡ (cong-≡ (λ ξ -> Some2CellGen v (μ₁ ◆ ξ) η) (sym-≡ pf₁)) ζ-new

  ... | no x = no "end 2.2.2.2.1.2"
  ... | yes res = yes (record { underfind = _ ; split = split-new ; bottomξ = res .bottomξ })
    where split-new = transp-≡ (cong-≡ (λ ξ -> Split v (μ₀ ◆ ξ) (underfind res)) (pf₀)) (res .split)
  --
  -- Case 2.2.2.2.2: The recursive call wasn't successful. But this is no reason
  --                 to be sad because as noted in 2.2, there is still a chance that
  --                 we are going to find another satisfying face in the current row
  --                 So we recurse into the current row with the original pattern `pat`.
  --
  --                 Note that agda doesn't see that this call terminates because it doesn't know that
  --                 the foundᵣ is going to be smaller than ζ
  findAllLocked (suc n) {v = v} pat {μ₀ = μ₀} {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest)
    | yes (sp@(_⧓⌞_⌟⧓_[_,_] {left₁ = left₁} {right₁ = right₁} foundₗ found foundᵣ pf₀ pf₁ ) , pat2)
    | no p with findAllLocked (suc n) pat (get (incl ξ ⧓ (foundₗ ⧓ as2CellGen found ))) (foundᵣ .get) (ζ-new' ∷ rest)

    where ζ-new' : Some2CellGen _ (μ₁ ◆ left₁ ◆ found .idₗ ◆ found .cξ₁ ◆ found .idᵣ ◆ right₁) _
          ζ-new' = transp-≡ (cong-≡ (λ ξ -> Some2CellGen v (μ₁ ◆ ξ) η) (sym-≡ pf₁)) ζ-new
  --
  -- Case 2.2.2.2.2.1: We are still not successful in this row. This means that we can stop trying now.
  ... | no x = no "end 2.2.2.2.2.1"
  --
  -- Case 2.2.2.2.2.2: We were actually successful! So update the result.
  ... | yes res = yes (record { underfind = _ ; split = split-new ; bottomξ = res .bottomξ })
    where split-new = transp-≡ (cong-≡ (λ ξ -> Split v (μ₀ ◆ ξ) (underfind res)) (pf₀)) (res .split)




  -- Repeatedly try to lock in a pattern, and find the rest of it downstream
  findAll : ∀{n v}
            -- The pattern we are searching for
            -> 2CellLinePattern v 𝑗 (suc n)

            -- The top(μ) and bottom(ω) 1cell
            -> {μ ω : 1Cell G a b}

            -- The 2Cell between them which we are searching
            -> 2Cell v μ ω

            -- We return a 4-way split if we find the pattern
            -> String +-𝒰 (Result:findAll v μ ω)

  -- Case 1: we don't allow for empty patterns,
  -- thus this means that we didn't find this
  -- pattern
  findAll pat [] = no "findall empty"

  -- Case 2: we have a 2CellGen ξ which we can check
  findAll pat (ξ ∷ ξs) with findAllLocked _ pat (id ⌟) (ξ .get) ξs

  -- Case 2.1: the happy case, we found our pattern! Now we have
  --           to return the result
  ... | yes res = yes (record { topξ = [] ; result = res })

  -- Case 2.2: if we could not lock-in the pattern in this row,
  --           we recursively try the next
  ... | no prev with findAll pat ξs

  -- Case 2.2.1: the recursive case found it!
  --             we simply add the current row to the top of the result
  ... | yes res = yes (record { topξ = ξ ∷ topξ res ; result = result res })

  -- Case 2.2.2: even the recursive call didn't find this pattern
  --             this means that it doesn't exist, so we return nothing
  ... | no msg = no ("exhausted: " <> msg <> ", prev: " <> prev)







  -- We can commute the visibile and invisible cells. This is required
  -- for substitution under `transform` terms in our type theory.
  commute-vis : (ξ : 2Cell vis μ η) -> (ζ : 2Cell invis η ω) ->
                ∑ λ η' -> (2Cell invis μ η' ×-𝒰 2Cell vis η' ω)
  commute-vis = {!!}





{-

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

{-
-}
-}
