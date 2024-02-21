
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
    μ₀ : 1Cell G c d
    μ₁ : 1Cell G e f
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
  -- _⋈_ : ∃Partition μ -> ∃Partition η -> ∃Partition (μ ◆ η)
  -- incl a ⋈ incl b = incl (join a b)

  -- _⋉_ : ∃Partition μ -> (η : 1Cell G a b) -> ∃Partition (μ ◆ η)
  -- μp ⋉ η = μp ⋈ incl (η ⌟)

  -- _⋊_ : (μ : 1Cell G a b) -> ∃Partition η -> ∃Partition (μ ◆ η)
  -- μ ⋊ ηp = incl (μ ⌟) ⋈ ηp

  -- infixr 30 _⋈_
  -- infixl 30 _⋉_
  -- infixr 28 _⋊_



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


  _⋈_ : {v : Visibility} {a b c : 0Cell G}
          -> {μ₀ μ₁ : 1Cell G a b}
          -> {η₀ η₁ : 1Cell G b c}
          -> Some2CellGen v μ₀ μ₁
          -> Some2CellGen v η₀ η₁
          -> Some2CellGen v (μ₀ ◆ η₀) (μ₁ ◆ η₁)
  (incl ξ) ⋈ (incl ζ) = incl (join-2CellGen ξ ζ)

  _⋊_ : {v : Visibility} {a b c : 0Cell G}
          -> (ϕ : 1Cell G a b)
          -> {η₀ η₁ : 1Cell G b c}
          -> Some2CellGen v η₀ η₁
          -> Some2CellGen v (ϕ ◆ η₀) (ϕ ◆ η₁)
  _⋊_ ϕ ξ = incl (ϕ ⌟) ⋈ ξ

  _⋉_ : {v : Visibility} {a b c : 0Cell G}
          -> {η₀ η₁ : 1Cell G a b}
          -> Some2CellGen v η₀ η₁
          -> (ϕ : 1Cell G b c)
          -> Some2CellGen v (η₀ ◆ ϕ) (η₁ ◆ ϕ)
  _⋉_ ξ ϕ = ξ ⋈ incl (ϕ ⌟)



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

  _◆'₂_ : ∀{v} -> 2Cell v μ η -> 2Cell v η ω -> 2Cell v μ ω
  [] ◆'₂ b = b
  (x ∷ a) ◆'₂ b = x ∷ (a ◆'₂ b)



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

  isLeftSub1Cell : (μ₀ : 1Cell G a b) (μ : 1Cell G a c) -> 𝒰 _
  isLeftSub1Cell μ₀ μ = ∑ λ μ₁ -> μ₀ ◆ μ₁ ≡ μ

  record _⊴_ (μ₀ : 1Cell G a b) (μ : 1Cell G a c) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : isLeftSub1Cell μ₀ μ

  open _⊴_ public

  refl-⊴ : μ ⊴ μ
  refl-⊴ = incl (id , refl)

  _⟡-⊴_ : μ ⊴ η -> η ⊴ ω -> μ ⊴ ω
  _⟡-⊴_ (incl (μ' , refl)) (incl (η' , refl)) = incl (μ' ◆ η' , refl)

  _↷-⊴_ : ∀ (μ : 1Cell G a b) -> η₀ ⊴ η₁ -> μ ◆ η₀ ⊴ μ ◆ η₁
  _↷-⊴_ μ (incl (η₀' , refl)) = incl (η₀' , refl)


  cancelₗ-⨾-head : ∀{x y : Edge G a b} -> x ⨾ μ ≡ y ⨾ η -> x ≡ y
  cancelₗ-⨾-head refl = refl

  cancelₗ-⨾-tail : ∀{x y : Edge G a b} -> x ⨾ μ ≡ y ⨾ η -> μ ≡ η
  cancelₗ-⨾-tail refl = refl

  cancelₗ-⨾-point : ∀{x : Edge G a b} {y : Edge G a c} -> x ⨾ μ ≡ y ⨾ η -> b ≡ c
  cancelₗ-⨾-point refl = refl


  cancelₗ-◆ : ∀ (μ : 1Cell G a b) -> (μ ◆ η₀ ≡ μ ◆ η₁) -> η₀ ≡ η₁
  cancelₗ-◆ id p = p
  cancelₗ-◆ (x ⨾ μ) p = cancelₗ-◆ μ (cancelₗ-⨾-tail p)


  cancelₗ-⊴ : ∀ (μ₀ : 1Cell G a b) -> (μ₀ ◆ μ₁) ⊴ (μ₀ ◆ η) -> μ₁ ⊴ η
  cancelₗ-⊴ μ₀ (incl (μ' , p)) = incl (μ' , cancelₗ-◆ μ₀ p)

  private
    decide-⊴-ind : ∀{b₀ b₁ : 0Cell G} -> (μ₀ : 1Cell G a b₀) -> (μ₁ : 1Cell G a b₁)
                   -> (μ₀' : 1Cell G b₀ c) -> (μ₁' : 1Cell G b₁ c)
                   -> (p : μ₀ ◆ μ₀' ≡ μ₁ ◆ μ₁')
                   -> ((¬(μ₀ ⊴ μ₁)) ×-𝒰 (μ₁ ⊴ μ₀)) +-𝒰 (μ₀ ⊴ μ₁)
    decide-⊴-ind id id μ₀' μ₁' p = yes refl-⊴
    decide-⊴-ind id (x ⨾ μ₁) μ₀' μ₁' p = yes (incl (_ , refl))
    decide-⊴-ind (x ⨾ μ₀) id μ₀' μ₁' p = no ((λ {(incl (_ , ()))}) , incl (_ , refl))
    decide-⊴-ind (_⨾_ {n = n} x μ₀) (_⨾_ {n = n₁} x₁ μ₁) μ₀' μ₁' p
      with refl <- cancelₗ-⨾-point p
      with refl <- cancelₗ-⨾-head p
      with p <- cancelₗ-⨾-tail p
      with decide-⊴-ind μ₀ μ₁ μ₀' μ₁' p
    ... | no (P , Q) = no ((λ xμ₀⊴xμ₁ -> P (cancelₗ-⊴ (x ⨾ id) xμ₀⊴xμ₁)) , ((x ⨾ id) ↷-⊴ Q))
    ... | yes X = yes ((x ⨾ id) ↷-⊴ X)

  decide-⊴ : μ₀ ⊴ μ -> μ₁ ⊴ μ -> ((¬(μ₀ ⊴ μ₁)) ×-𝒰 (μ₁ ⊴ μ₀)) +-𝒰 (μ₀ ⊴ μ₁)
  decide-⊴ (incl (μ₀' , μ₀'p)) (incl (μ₁' , refl)) = decide-⊴-ind _ _ μ₀' μ₁' μ₀'p


  _◆[_] : ∀ (μ : 1Cell G a b) -> ∀ (η : 1Cell G b c) -> μ ⊴ (μ ◆ η)
  _◆[_] μ η = incl (η , refl)

  infixr 30 _◆[_]






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
           -- a proof that the prefix and the bottom part of
           -- the face are a subcell of μ
           (P : (εₗ ◆ bottom) ⊴ μ)
           -- the face itself
           (ξ : Face G v top bottom)

           -- We only return a value if we are succesfull
           -> Maybe (Some2CellGen v (εₗ ◆ top ◆ ⟨ P ⟩ .fst) η)

  -- Case 1: There is only a single free part left of ζ.
  --         Then we can take our face and insert it after
  --         the prefix εₗ. We know that there exists a proper
  --         suffix εᵣ because of P.
  insertFace (ϕ ⌟) εₗ (incl (εᵣ , refl)) ξ = yes (incl (εₗ ⌟[ ξ ]⌞ εᵣ ⌟))

  -- Case 2: 
  insertFace (_⌟[_]⌞_ {ξ₀ = ξ₀} {μ = μ}  ϕ ξ' ζ) εₗ {top} {bottom} P@(incl (εᵣ , εₗ◆bottom◆εᵣ=μ)) ξ

    -- we check whether εₗ or ϕ is contained in the other
    with decide-⊴ (ϕ ◆[ ξ₀ ◆ μ ]) (εₗ ◆[ bottom ] ⟡-⊴ P)

  -- Case 2.1: we have εₗ⊴ϕ. This means that `bottom` has to fit between the
  --           end of εₗ and the end of ϕ
  ... | no (_ , εₗ⊴ϕ@(incl (εₗ' , refl)))

    -- we check whether bottom fits into εₗ'
    with decide-⊴ (cancelₗ-⊴ εₗ (P)) (εₗ' ◆[ ξ₀ ◆ μ ])

  -- Case 2.1.1: It does, this means we found our place for insertion!
  ... | yes bottom⊴εₗ'@(incl (bottom' , refl))

    -- We only need to show that we have the right boundaries...
    with refl <- cancelₗ-◆ (εₗ ◆ bottom) (εₗ◆bottom◆εᵣ=μ)

    -- ... and can return
      = yes (incl (εₗ ⌟[ ξ ]⌞ bottom' ⌟[ ξ' ]⌞ ζ ))

  -- Case 2.1.2: Bottom does not fit into εₗ'. This means that it overlaps with the top boundary
  --             ξ₀ of the face ξ', and thus we cannot insert ξ.
  ... | no p = nothing

  -- Case 2.2: We have ϕ⊴εₗ. This means that our prefix εₗ skips over the full
  --           ϕ free space before ξ'. We now need to check whether it also skips
  --           over the full top boundary ξ₀ of ξ'.
  insertFace (_⌟[_]⌞_ {ξ₀ = ξ₀} {μ = μ} ϕ ξ' ζ) εₗ {top} {bottom} P ξ | right ϕ⊴εₗ@(incl (ϕ' , refl))

    -- we compare ξ₀ ⊴ ξ₀ ⟡ μ   and   ϕ' ⊴ ξ₀ ⟡ μ
    with decide-⊴ (ξ₀ ◆[ μ ]) (ϕ' ◆[ bottom ] ⟡-⊴ (cancelₗ-⊴ ϕ P))

    -- Case 2.2.1: ¬ (ξ₀ ⊴ ϕ'). This means that our left prefix ϕ' ends before ξ₀. Thus we would
    --             have to insert our new face ξ directly into the existing face ξ' with top boundary
    --             ξ₀. Thus we say that we cannot.
  ... | no p = nothing

    -- Case 2.2.2: ξ₀ ⊴ ϕ', indeed. This means that we can skip over the ξ face, and call ourselves
    --             recursively.
  ... | yes ξ₀⊴ϕ'@(incl (ξ₀' , refl)) with insertFace ζ ξ₀' (cancelₗ-⊴ (ϕ ◆ ξ₀) P) ξ
  ... | no p = nothing
  ... | yes (incl ζ-new) = yes (incl (ϕ ⌟[ ξ' ]⌞ ζ-new))




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
        -- ω₀ to ω₁. (Originally, ω₀ ≡ ηₗ ◆ ηᵣ, but this changes when we insert succesfully)
        {ω₁ : 1Cell G a c}
        (ζ : Some2CellGen v (ηₗ ◆ ηᵣ) ω₁)
        -- We return two new cells
        -> ∑ λ ω₀ -> (Some2CellGen v (μₗ ◆ μᵣ) ω₀
                 ×-𝒰 Some2CellGen v ω₀ ω₁)

  -- Case 1: There is no face left in ξᵣ, so we reappend ϕ to ξₗ and return
  pushDownTaken ξₗ (ϕ ⌟) ζ = _ , (ξₗ ⋈ incl (ϕ ⌟)) , ζ

  -- Case 2: We have a taken face ξ in ξᵣ.
  --         Thus we try to insert ξ down into ζ.
  pushDownTaken {ηₗ = ηₗ} ξₗ (_⌟[_]⌞_ {ξ₀ = ξ₀} {ξ₁ = ξ₁} {η = η} ϕ ξ ξᵣ) ζ with insertFace (ζ .get) (ηₗ ◆ ϕ) ((ηₗ ◆ ϕ ◆ ξ₁) ◆[ η ])  ξ

  -- Case 2.1: We couldn't successfully insert, so we skip this face
  ... | no x = pushDownTaken (ξₗ ⋈ incl (ϕ ⌟[ ξ ]⌞ id ⌟)) ξᵣ ζ

  -- Case 2.2: We inserted successfully! So call ourselves with an ξₗ which is only extended by identity
  ... | yes (ζ-new) = pushDownTaken (ξₗ ⋈ incl ((ϕ ◆ ξ₀) ⌟)) ξᵣ ζ-new


  pushDown2CellGen : Some2CellGen v η μ -> Some2CellGen v μ ω -> ∑ λ μ' -> Some2CellGen v η μ' ×-𝒰 Some2CellGen v μ' ω
  pushDown2CellGen ξ ζ = pushDownTaken (incl (id ⌟)) (ξ .get) ζ


  {-# TERMINATING #-}
  pushDownAll : 2Cell v η μ -> 2Cell v η μ
  pushDownAll [] = []
  pushDownAll (x ∷ []) = x ∷ []
  pushDownAll (ξ ∷ (ζ ∷ ζs))
    with (_ , ξ' , ζ') <- pushDown2CellGen ξ ζ
    = ξ' ∷ pushDownAll (ζ' ∷ ζs)



  ------------------------------------------------------------------------
  -- The proper operations on 2Cells

  -- vertical composition of 2cells
  _◆₂_ : 2Cell v μ η -> 2Cell v η ω -> 2Cell v μ ω
  _◆₂_ ξ ζ = pushDownAll (ξ ◆'₂ ζ)

  -- whiskering 2cells
  _⧕_ : (μ : 1Cell G a b) -> 2Cell v η ω -> 2Cell v (μ ◆ η) (μ ◆ ω)
  μ ⧕ [] = []
  μ ⧕ (ξ ∷ ξs) = (μ ⋊ ξ) ∷ (μ ⧕ ξs)

  _⧔_ : 2Cell v η ω -> (μ : 1Cell G a b) -> 2Cell v (η ◆ μ) (ω ◆ μ)
  [] ⧔ μ = []
  (ξ ∷ ξs) ⧔ μ = (ξ ⋉ μ) ∷ (ξs ⧔ μ)

  -- horizontal composition of 2cells
  _⧓_ : ∀{μ₀ η₀ : 1Cell G a b} {μ₁ η₁ : 1Cell G b c}
      -> 2Cell v μ₀ η₀ -> 2Cell v μ₁ η₁ -> 2Cell v (μ₀ ◆ μ₁) (η₀ ◆ η₁)
  _⧓_ {η₀ = η₀} {μ₁ = μ₁} ξ₀ ξ₁ = (ξ₀ ⧔ μ₁)
                               ◆₂ (η₀ ⧕ ξ₁)



  {-



  ----------------------------------------------------------
  -- Commutation

  -- We can commute the visibile and invisible cells. This is required
  -- for substitution under `transform` terms in our type theory.
  -- commute-vis : (ξ : 2Cell vis μ η) -> (ζ : 2Cell invis η ω) ->
  --               ∑ λ η' -> (2Cell invis μ η' ×-𝒰 2Cell vis η' ω)
  -- commute-vis = {!!}



-}

