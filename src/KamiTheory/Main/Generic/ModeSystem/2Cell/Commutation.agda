
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
-- open import KamiTheory.Main.Generic.ModeSystem.LinearFSM.Definition
open import KamiTheory.Order.StrictOrder.Base

open import Data.Fin using (Fin ; zero ; suc)


import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as D


module 2CellCommutation (G : 2Graph 𝑖) where
  open D.2CellDefinition G

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    η : 1Cell G b c
    ω : 1Cell G c d
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f
    v : Visibility

  record Some1Cell : 𝒰 𝑖 where
    constructor incl
    field {start end} : 0Cell G
    field get : 1Cell G start end

  open Some1Cell public

  data isNonTrivial : Some1Cell -> 𝒰 𝑖 where
    incl : ∀{x : Edge G a b} -> isNonTrivial (incl (x ⨾ μ))


  record Sparse2CellGen v (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⌟[_⇒_∋_]⌞_[_,_]
    field {pb pc} : 0Cell G
    field εₗ : 1Cell G a pb
    field top bottom : 1Cell G pb pc
    field face : Face G v top bottom
    field εᵣ : 1Cell G pc d
    field pf₀ : (εₗ ◆ top ◆ εᵣ) ≡ μ
    field pf₁ : (εₗ ◆ bottom ◆ εᵣ) ≡ η

  _⟡-⊴≡_ : η ⊴ μ -> μ ≡ ω -> η ⊴ ω
  p ⟡-⊴≡ refl-≡ = p


  -- Given two 1cells, there are 4 ways in which they can intersect:
  --  Case 1:
  --    |---- ξ ----|
  --        |----- ζ -----|
  --
  --  Case 2:
  --    |---- ξ ----|
  --       |--- ζ -|
  --
  --  Case 3:
  --        |----- ξ ----|
  --    |------ ζ ---|
  --
  --  Case 4:
  --        |-- ξ --|
  --    |------- ζ -----|
  --
  --
  -- In each case, the area spanned by the two cells is given by different
  -- endpoints. This makes it difficult to formulate a gluing uniformly.
  -- We thus simply distinguish all cases.

  data Intersecting : (μ : 1Cell G a b) -> (η : 1Cell G a b) -> 𝒰 𝑖 where
    situation1 : (vεₗ' : 1Cell G a b) (δ : 1Cell G b c) (vεₗvξ₁' : 1Cell G c d)
                 (δ≠id : isNonTrivial (incl δ))

                 -- We have a face into the "vξ₁ = iεₗ' ◆ δ"
                 {vξ₀ : 1Cell G a c}
                 (vξ : Face G vis vξ₀ (vεₗ' ◆ δ))

                 -- And a face out of "iξ₀ = δ ◆ vεᵣ'"
                 {iξ₁ : 1Cell G b d}
                 (iξ : Face G invis (δ ◆ vεₗvξ₁') iξ₁)

                 -- This means we have an intersection with a boundary
                 -> Intersecting (vξ₀ ◆ vεₗvξ₁') (vεₗ' ◆ iξ₁)

  commute-intersecting : Intersecting μ η -> ∑ λ ω -> Sparse2CellGen invis μ ω ×-𝒰 Sparse2CellGen vis ω η
  commute-intersecting = {!!}








  -- commute two faces
  commuteFace : Sparse2CellGen vis μ η -> Sparse2CellGen invis η ω
              -> ∑ λ η' -> (Sparse2CellGen invis μ η' ×-𝒰 Sparse2CellGen vis η' ω)
  commuteFace {μ = μ} {η = η} {ω = ω} (vεₗ ⌟[ vξ₀ ⇒ vξ₁ ∋ vξ ]⌞ vεᵣ [ refl , refl ]) (iεₗ ⌟[ iξ₀ ⇒ iξ₁ ∋ iξ ]⌞ iεᵣ [ ipf₀ , refl ])
  --
  -- first we have to understand whether we are intersecting at all,
  -- and if we are, then in which of the four cases.
  --
  -- We have, between our two cells, the situtation:
  --
  --  |--- vεₗ ---|-- vξ₁ --|--- vεᵣ ---|
  --  |                                 |
  --  |--- iεₗ ---|-- iξ₀ --|--- iεᵣ ---|
  --
  -- So first we check how (iεₗ ◆ iξ₀) is related to vεₗ
    with decide-⊴ (((iεₗ ◆ iξ₀) ◆[ iεᵣ ]) ⟡-⊴≡ ipf₀) (vεₗ ◆[ vξ₁ ◆ vεᵣ ])
  --
  -- Case 1: If iεₗiξ₀⊴vεₗ, this means that the invisible cell fits through on the left
  --         side of the visible cell, and they don't interact. We can thus directly return
  --         their commuted result.
  ... | yes (iεₗiξ₀⊴vεₗ@(incl (iεₗiξ₀' , refl))) = _ , (iεₗ ⌟[ _ ⇒ _ ∋ iξ ]⌞ iεₗiξ₀' ◆ vξ₀ ◆ vεᵣ [ refl , refl ]) , (iεₗ ◆ iξ₁ ◆ iεₗiξ₀' ⌟[ _ ⇒ _ ∋ vξ ]⌞ vεᵣ [ refl , P ])
        where P₀ : iεₗiξ₀' ◆ vξ₁ ◆ vεᵣ ≡ iεᵣ
              P₀ = cancelₗ-◆ (iεₗ ◆ iξ₀) (sym-≡ ipf₀)

              P : iεₗ ◆ iξ₁ ◆ iεₗiξ₀' ◆ vξ₁ ◆ vεᵣ ≡ iεₗ ◆ iξ₁ ◆ iεᵣ
              P = cong-≡ ((iεₗ ◆ iξ₁) ◆_) P₀
  --
  -- Case 2: We know that the invisible cell does not fit through on the left side.
  --         So we try whether it fits through on the right.
  ... | no (¬iεₗiξ₀⊴vεₗ , vεₗ⊴iεₗiξ₀)
  --
  -- We thus check how (vεₗ ◆ vξ₁) is related to iεₗ
    with decide-⊴ (((vεₗ ◆ vξ₁) ◆[ vεᵣ ]) ⟡-⊴≡ sym-≡ ipf₀) (iεₗ ◆[ iξ₀ ◆ iεᵣ ])
  --
  -- Case 2.1: If (vεₗ◆vξ₁) ⊴ iεₗ, this means that we can fit the invisible cell through
  --           on the right side of the visible cell, and they don't interact. We can thus directly
  --           return the result.
  ... | yes (vεₗvξ₁⊴iεₗ@(incl (vεₗvξ₁' , refl))) = _ , (vεₗ ◆ vξ₀ ◆ vεₗvξ₁' ⌟[ _ ⇒ _ ∋ iξ ]⌞ iεᵣ [ P , refl ]) , (vεₗ ⌟[ _ ⇒ _ ∋ vξ ]⌞ vεₗvξ₁' ◆ iξ₁ ◆ iεᵣ [ refl , refl ])
        where P₀ : vεₗvξ₁' ◆ iξ₀ ◆ iεᵣ ≡ vεᵣ
              P₀ = cancelₗ-◆ (vεₗ ◆ vξ₁) (ipf₀)

              P : vεₗ ◆ vξ₀ ◆ vεₗvξ₁' ◆ iξ₀ ◆ iεᵣ ≡ vεₗ ◆ vξ₀ ◆ vεᵣ
              P = cong-≡ ((vεₗ ◆ vξ₀) ◆_) P₀
  --
  -- Case 2.2: We know that the invisible cell does not fit on the left, neither on the right.
  --           This means that the cells have to intersect, but we don't yet know which of them
  --           is "more left", that is whose left point is the leftmost point of their union.
  --           We thus check as next step which of {vεₗ,iεₗ} is shorter by comparing them.
  commuteFace {μ = μ} {η = η} {ω = ω} (vεₗ ⌟[ vξ₀ ⇒ vξ₁ ∋ vξ ]⌞ vεᵣ [ refl , refl ]) (iεₗ ⌟[ iξ₀ ⇒ iξ₁ ∋ iξ ]⌞ iεᵣ [ ipf₀ , refl ])
    | no (¬iεₗiξ₀⊴vεₗ , vεₗ⊴iεₗiξ₀@(incl (vδ , vδp)))
    | no (¬vεₗvξ₁⊴iεₗ , iεₗ⊴vεₗvξ₁@(incl (iδ , iδp)))
  --
  -- Check how vεₗ relates to iεₗ
    with decide-⊴ (vεₗ ◆[ vξ₁ ◆ vεᵣ ] ⟡-⊴≡ sym-≡ ipf₀) (iεₗ ◆[ iξ₀ ◆ iεᵣ ])
  --
  -- Case 2.2.1: We know that vεₗ is shorter (or equal) to iεₗ. This means we are in
  --             "situation 1" or "situation 2" from above. We have to check in which we are,
  --             by comparing the lengths of "prefix◆cell", that is (vεₗ ◆ vξ₁) and (iεₗ ◆ iξ₀).
  ... | yes (vεₗ⊴iεₗ@(incl (vεₗ' , refl))) with decide-⊴ ((vεₗ ◆ vξ₁) ◆[ vεᵣ ] ⟡-⊴≡ sym-≡ ipf₀) ((iεₗ ◆ iξ₀) ◆[ iεᵣ ])
  --
  -- Case 2.2.1.1: We know that (vεₗ ◆ vξ₁) is shorter (or equal) to (iεₗ ◆ iξ₀). This means that
  --               we are in situtation 1 from above.
  --
  --               Now we first need to show that this means that the bottom face of vξ decomposes
  --               into (vεₗ' ◆ δ), and the upper face of iξ decomposes into (δ ◆ vεₗvξ₁'), where
  --               δ is their nontrivial intersection. To show these facts, we use the equations
  --               that we already have.
  ... | yes (vεₗvξ₁⊴iεₗiξ₀@(incl (vεₗvξ₁' , vεₗvξ₁'p)))
  --
  -- We first show that we can write vξ₁ as (vεₗ' ◆ iδ)
    with refl <- (let P₀ : vεₗ ◆ vξ₁ ≡ vεₗ ◆ vεₗ' ◆ iδ
                      P₀ = sym-≡ iδp

                      P : vξ₁ ≡ vεₗ' ◆ iδ
                      P = cancelₗ-◆ vεₗ P₀
                  in P)
  --
  -- Next we show that we can write iξ₀ as (δ ◆ vεₗvξ₁')
    with refl <- (let P₀ : (vεₗ ◆ vεₗ' ◆ iξ₀) ≡ (vεₗ ◆ vεₗ' ◆ iδ ◆ vεₗvξ₁')
                      P₀ = sym-≡ vεₗvξ₁'p

                      P : iξ₀ ≡ (iδ ◆ vεₗvξ₁')
                      P = cancelₗ-◆ (vεₗ ◆ vεₗ') P₀
                  in P)

    = let s1 : Intersecting (vξ₀ ◆ vεₗvξ₁') (vεₗ' ◆ iξ₁)
          s1 = situation1 vεₗ' iδ vεₗvξ₁' {!!} vξ iξ

          res = commute-intersecting s1

      in {!!}
  --
  --
  --
  --
  -- Case 2.2.1.1: We know that (vεₗ ◆ vξ₁) is longer than (iεₗ ◆ iξ₀). This means that
  --               we are in situtation 2 from above.
  ... | no Y = {!!}
  --
  -- Case 2.2.2:
  commuteFace {μ = μ} {η = η} {ω = ω} (vεₗ ⌟[ vξ₀ ⇒ vξ₁ ∋ vξ ]⌞ vεᵣ [ refl , refl ]) (iεₗ ⌟[ iξ₀ ⇒ iξ₁ ∋ iξ ]⌞ iεᵣ [ ipf₀ , refl ])
    | no (¬iεₗiξ₀⊴vεₗ , vεₗ⊴iεₗiξ₀)
    | no (¬vεₗvξ₁⊴iεₗ , iεₗ⊴vεₗvξ₁)
    | no X = {!!}







{-

  -- We have an invisible face and a visible 2Cell below it,
  -- we commute the 2cell up. For this we first need to find
  -- the starting point where the invisible face begins to
  -- intersect with the cells' faces.
  commuteFace :
           -- the 2cellgen which we want to commute
           -- we commute from the bottom up
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

           -- We return 
           -> (Some2CellGen v (εₗ ◆ top ◆ ⟨ P ⟩ .fst) η)

-}
{-

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

-}



{-

  record Some1Cell : 𝒰 𝑖 where
    constructor incl
    field {start end} : 0Cell G
    field get : 1Cell G start end

  open Some1Cell public

  data isNonTrivial : Some1Cell -> 𝒰 𝑖 where
    incl : ∀{x : Edge G a b} -> isNonTrivial (incl (x ⨾ μ))


  -- We define sub1cells, this time they are both-sided

  isSub1Cell : (μ₀ : Some1Cell) (μ : Some1Cell) -> 𝒰 _
  isSub1Cell μ₀ μ = ∑ λ εₗ -> ∑ λ εᵣ -> εₗ ◆ μ₀ .get ◆ εᵣ ≡ μ .get

  record _⋖_ (μ₀ : Some1Cell) (μ : Some1Cell) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : isSub1Cell μ₀ μ


  -- two cells have an intersection if there is a non-trivial cell
  -- which is contained in both
  record _⟑_ (μ : Some1Cell) (η : Some1Cell) : 𝒰 𝑖 where
    field intersection : Some1Cell
    field in₀ : intersection ⋖ μ
    field in₁ : intersection ⋖ η
    field nontrivial : isNonTrivial intersection

  leftPoint : ∀{μ η : Some1Cell} -> (μ ⟑ η) -> 0Cell G
  leftPoint = {!!}

  rightPoint : ∀{μ η : Some1Cell} -> (μ ⟑ η) -> 0Cell G
  rightPoint = {!!}

  -- We say that a 2graph is commutable if every visible/invisible
  -- face pair which has a nontrivial intersection commutes against each other
  record isCommutable : 𝒰 𝑖 where
    field commuteFace : {μ : 1Cell G a b} {η₁ : 1Cell G c d} {ω : 1Cell G c d}
                  -> ∀{ξ : Face G vis μ η₀} {ζ : Face G invis η₁ ω}
                  -> (I : incl η₀ ⟑ incl η₁)
                  -> ∑ λ (η : 1Cell G (leftPoint I) (rightPoint I)) -> (Face G invis μ η) ×-𝒰 (Face G vis η ω)

-}
