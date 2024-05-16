-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


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
    incl : ∀{x : Edge (of G) a b} -> isNonTrivial (incl (x ⨾ μ))

  nonTrivialBy⊴ : (¬(η ⊴ μ)) -> (p : μ ⊴ η) -> isNonTrivial (incl (⟨ p ⟩ .fst))
  nonTrivialBy⊴ P (incl (id , refl)) = ⊥-elim (P refl-⊴)
  nonTrivialBy⊴ P (incl (x ⨾ δ , δp)) = incl


  record Sparse2CellGen v (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⌟[_⇒_∋_]⌞_[_,_]
    field {pb pc} : 0Cell G
    field εₗ : 1Cell G a pb
    field top bottom : 1Cell G pb pc
    field face : Face (of G) v top bottom
    field εᵣ : 1Cell G pc d
    field pf₀ : (εₗ ◆ top ◆ εᵣ) ≡ μ
    field pf₁ : (εₗ ◆ bottom ◆ εᵣ) ≡ η

  _⟡-⊴≡_ : η ⊴ μ -> μ ≡ ω -> η ⊴ ω
  p ⟡-⊴≡ refl-≡ = p

  data MaybeSparse2CellGen v : (μ η : 1Cell G a b) -> 𝒰 𝑖 where
    id : MaybeSparse2CellGen v μ μ
    incl : Sparse2CellGen v μ η -> MaybeSparse2CellGen v μ η

  _↷-Sparse2CellGen_ : ∀(ϕ : 1Cell G a b) -> Sparse2CellGen v μ η -> Sparse2CellGen v (ϕ ◆ μ) (ϕ ◆ η)
  _↷-Sparse2CellGen_ ϕ (εₗ ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ [ pf₀ , pf₁ ]) = (ϕ ◆ εₗ) ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ [ (cong-≡ (ϕ ◆_) pf₀) , ((cong-≡ (ϕ ◆_) pf₁)) ]

  _↷-MaybeSparse2CellGen_ : ∀(ϕ : 1Cell G a b) -> MaybeSparse2CellGen v μ η -> MaybeSparse2CellGen v (ϕ ◆ μ) (ϕ ◆ η)
  _↷-MaybeSparse2CellGen_ ϕ id = id
  _↷-MaybeSparse2CellGen_ ϕ (incl (εₗ ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ [ pf₀ , pf₁ ])) = incl ((ϕ ◆ εₗ) ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ [ (cong-≡ (ϕ ◆_) pf₀) , ((cong-≡ (ϕ ◆_) pf₁)) ])

  _↶-MaybeSparse2CellGen_ : MaybeSparse2CellGen v μ η -> (ϕ : 1Cell G a b) -> MaybeSparse2CellGen v (μ ◆ ϕ) (η ◆ ϕ)
  _↶-MaybeSparse2CellGen_ id ϕ = id
  _↶-MaybeSparse2CellGen_ (incl (εₗ ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ [ pf₀ , pf₁ ])) ϕ = incl (εₗ ⌟[ _ ⇒ _ ∋ ξ ]⌞ εᵣ ◆ ϕ [ (cong-≡ (_◆ ϕ) pf₀) , ((cong-≡ (_◆ ϕ) pf₁)) ])

  data Sparse2Cell v : (μ η : 1Cell G a d) -> 𝒰 𝑖 where
    [] : Sparse2Cell v μ μ
    _∷_ : Sparse2CellGen v μ η -> Sparse2Cell v η ω -> Sparse2Cell v μ ω

  -- Sparse2Cell : (v : Visibility) -> (μ η : 1Cell G a d) -> 𝒰 𝑖

  _↷-Sparse2Cell_ : ∀(ϕ : 1Cell G a b) -> Sparse2Cell v μ η -> Sparse2Cell v (ϕ ◆ μ) (ϕ ◆ η)
  _↷-Sparse2Cell_ ϕ [] = []
  _↷-Sparse2Cell_ ϕ (ξ ∷ ξs) = (ϕ ↷-Sparse2CellGen ξ) ∷ (ϕ ↷-Sparse2Cell ξs)

  _◆-Sparse2Cell_ : Sparse2Cell v μ η -> Sparse2Cell v η ω -> Sparse2Cell v μ ω
  _◆-Sparse2Cell_ ([]) ζs = ζs
  _◆-Sparse2Cell_ (ξ ∷ ξs) ζs = ξ ∷ (ξs ◆-Sparse2Cell ζs)



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
  --        |-- ξ --|
  --    |------- ζ -----|
  --
  --  Case 4:
  --        |----- ξ ----|
  --    |------ ζ ---|
  --
  -- In each case, the area spanned by the two cells is given by different
  -- endpoints. This makes it difficult to formulate a gluing uniformly.
  -- We thus simply distinguish all cases.

  data Intersecting : (μ : 1Cell G a b) -> (η : 1Cell G a b) -> 𝒰 𝑖 where
    situation1 : (vεₗ' : 1Cell G a b) (δ : 1Cell G b c) (vεₗvξ₁' : 1Cell G c d)
                 (δ≠id : isNonTrivial (incl δ))

                 -- We have a face into the "vξ₁ = vεₗ' ◆ δ"
                 {vξ₀ : 1Cell G a c}
                 (vξ : Face (of G) vis vξ₀ (vεₗ' ◆ δ))

                 -- And a face out of "iξ₀ = δ ◆ vεᵣ'"
                 {iξ₁ : 1Cell G b d}
                 (iξ : Face (of G) invis (δ ◆ vεₗvξ₁') iξ₁)

                 -- This means we have an intersection with a boundary
                 -> Intersecting (vξ₀ ◆ vεₗvξ₁') (vεₗ' ◆ iξ₁)

    situation2 : (vεₗ' : 1Cell G a b) (δ : 1Cell G b c) (iεₗiξ₀' : 1Cell G c d)
                 -- NOTE that it is possible that δ is trivial,
                 -- since we have to consider this possibility as well

                 -- We have a face into the "vξ₁ = vεₗ' ◆ δ ◆ iεₗiξ₀'"
                 {vξ₀ : 1Cell G a d}
                 (vξ : Face (of G) vis vξ₀ (vεₗ' ◆ δ ◆ iεₗiξ₀'))

                 -- And a face out of "iξ₀ = δ"
                 {iξ₁ : 1Cell G b c}
                 (iξ : Face (of G) invis δ iξ₁)

                 -- This means we have an intersection with a boundary
                 -> Intersecting (vξ₀) (vεₗ' ◆ iξ₁ ◆ iεₗiξ₀')

    situation3 : (iεₗ' : 1Cell G a b) (δ : 1Cell G b c) (vεₗvξ₁' : 1Cell G c d)
                 -- NOTE that it is possible that δ is trivial,
                 -- since we have to consider this possibility as well

                 -- We have a face into the "vξ₁ = δ"
                 {vξ₀ : 1Cell G b c}
                 (vξ : Face (of G) vis vξ₀ δ)

                 -- And a face out of "iξ₀ = iεₗ' ◆ δ ◆ vεₗvξ₁'"
                 {iξ₁ : 1Cell G a d}
                 (iξ : Face (of G) invis (iεₗ' ◆ δ ◆ vεₗvξ₁') iξ₁)

                 -- This means we have an intersection with a boundary
                 -> Intersecting (iεₗ' ◆ vξ₀ ◆ vεₗvξ₁') (iξ₁)

    situation4 : (iεₗ' : 1Cell G a b) (δ : 1Cell G b c) (iεₗiξ₀' : 1Cell G c d)
                 (δ≠id : isNonTrivial (incl δ))

                 -- ...
                 {vξ₀ : 1Cell G b d}
                 (vξ : Face (of G) vis vξ₀ (δ ◆ iεₗiξ₀'))

                 -- ...
                 {iξ₁ : 1Cell G a c}
                 (iξ : Face (of G) invis (iεₗ' ◆ δ) iξ₁)

                 -- This means we have an intersection with a boundary
                 -> Intersecting (iεₗ' ◆ vξ₀) (iξ₁ ◆ iεₗiξ₀')

  module WithCommute (commute-intersecting : ∀{a b : 0Cell G} -> ∀{μ η : 1Cell G a b} -> Intersecting μ η -> ∑ λ ω -> MaybeSparse2CellGen invis μ ω ×-𝒰 MaybeSparse2CellGen vis ω η) where










    -- commute two faces
    commuteFace : Sparse2CellGen vis μ η -> Sparse2CellGen invis η ω
                -> ∑ λ η' -> (MaybeSparse2CellGen invis μ η' ×-𝒰 MaybeSparse2CellGen vis η' ω)
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
    ... | yes (iεₗiξ₀⊴vεₗ@(incl (iεₗiξ₀' , refl))) = _ , (incl (iεₗ ⌟[ _ ⇒ _ ∋ iξ ]⌞ iεₗiξ₀' ◆ vξ₀ ◆ vεᵣ [ refl , refl ])) , (incl (iεₗ ◆ iξ₁ ◆ iεₗiξ₀' ⌟[ _ ⇒ _ ∋ vξ ]⌞ vεᵣ [ refl , P ]))
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
    ... | yes (vεₗvξ₁⊴iεₗ@(incl (vεₗvξ₁' , refl))) = _ , (incl (vεₗ ◆ vξ₀ ◆ vεₗvξ₁' ⌟[ _ ⇒ _ ∋ iξ ]⌞ iεᵣ [ P , refl ])) , (incl (vεₗ ⌟[ _ ⇒ _ ∋ vξ ]⌞ vεₗvξ₁' ◆ iξ₁ ◆ iεᵣ [ refl , refl ]))
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
    ... | yes (vεₗ⊴iεₗ@(incl (vεₗ' , refl)))
    --
    -- But before that, we first show that we can write vξ₁ as (vεₗ' ◆ iδ), because we are going to
    -- need this in both subcases.
      with refl <- (let P₀ : vεₗ ◆ vξ₁ ≡ vεₗ ◆ vεₗ' ◆ iδ
                        P₀ = sym-≡ iδp

                        P : vξ₁ ≡ vεₗ' ◆ iδ
                        P = cancelₗ-◆ vεₗ P₀
                    in P)
    --
    -- Now we check whether we are in situation 1 or 2.
      with decide-⊴ ((vεₗ ◆ vξ₁) ◆[ vεᵣ ] ⟡-⊴≡ sym-≡ ipf₀) ((iεₗ ◆ iξ₀) ◆[ iεᵣ ])
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
    -- Next we show that we can write iξ₀ as (δ ◆ vεₗvξ₁')
      with refl <- (let P₀ : (vεₗ ◆ vεₗ' ◆ iξ₀) ≡ (vεₗ ◆ vεₗ' ◆ iδ ◆ vεₗvξ₁')
                        P₀ = sym-≡ vεₗvξ₁'p

                        P : iξ₀ ≡ (iδ ◆ vεₗvξ₁')
                        P = cancelₗ-◆ (vεₗ ◆ vεₗ') P₀
                    in P)
    --
    -- We also already show that vεᵣ is (vεₗvξ₁' ◆ iεᵣ), because this makes returning our result easier.
      with refl <- (let P₀ : (vεₗ ◆ vξ₁ ◆ vεₗvξ₁' ◆ iεᵣ) ≡ (iεₗ ◆ iξ₀ ◆ iεᵣ)
                        P₀ = cong-≡ (_◆ iεᵣ) (vεₗvξ₁'p)

                        P₁ : (vεₗ ◆ vξ₁ ◆ vεₗvξ₁' ◆ iεᵣ) ≡ (vεₗ ◆ vξ₁ ◆ vεᵣ)
                        P₁ = P₀ ∙-≡ ipf₀

                        P : vεₗvξ₁' ◆ iεᵣ ≡ vεᵣ
                        P = cancelₗ-◆ (vεₗ ◆ vξ₁) P₁
                    in P)

      = let s1 : Intersecting (vξ₀ ◆ vεₗvξ₁') (vεₗ' ◆ iξ₁)
            s1 = situation1 vεₗ' iδ vεₗvξ₁' (nonTrivialBy⊴ ¬vεₗvξ₁⊴iεₗ iεₗ⊴vεₗvξ₁) vξ iξ

            γ , ξ₀' , ξ₁' = commute-intersecting s1

            res₀ = (vεₗ ↷-MaybeSparse2CellGen ξ₀') ↶-MaybeSparse2CellGen iεᵣ
            res₁ = (vεₗ ↷-MaybeSparse2CellGen ξ₁') ↶-MaybeSparse2CellGen iεᵣ

        in _ , res₀ , res₁
    --
    --
    --
    --
    -- Case 2.2.1.1: We know that (vεₗ ◆ vξ₁) is longer than (iεₗ ◆ iξ₀). This means that
    --               we are in situtation 2 from above.
    ... | no (¬vεₗvξ₁⊴iεₗiξ₀ , iεₗiξ₀⊴vεₗvξ₁@(incl (iεₗiξ₀' , iεₗiξ₀'p)))
    --
    -- We first show that we can write iδ as (iξ₀ ◆ iεₗiξ₀')
      with refl <- (let P₀ : vεₗ ◆ vεₗ' ◆ iξ₀ ◆ iεₗiξ₀' ≡ vεₗ ◆ vεₗ' ◆ iδ
                        P₀ = iεₗiξ₀'p

                        P : iξ₀ ◆ iεₗiξ₀' ≡ iδ
                        P = cancelₗ-◆ (vεₗ ◆ vεₗ') P₀

                    in P)
    --
    -- We also already show that iεᵣ is (iεₗiξ₀' ◆ vεᵣ), because this makes returning our result easier.
      with refl <- (let P₀ : vεₗ ◆ vεₗ' ◆ iξ₀ ◆ iεₗiξ₀' ◆ vεᵣ ≡ vεₗ ◆ vεₗ' ◆ iδ ◆ vεᵣ
                        P₀ = cong-≡ (_◆ vεᵣ) (iεₗiξ₀'p)

                        P₁ : (vεₗ ◆ vεₗ' ◆ iξ₀ ◆ iεᵣ) ≡ vεₗ ◆ vεₗ' ◆ iξ₀ ◆ iεₗiξ₀' ◆ vεᵣ
                        P₁ = ipf₀ ∙-≡ P₀

                        P : iεₗiξ₀' ◆ vεᵣ ≡ iεᵣ
                        P = cancelₗ-◆ (vεₗ ◆ vεₗ' ◆ iξ₀) (sym-≡ P₁)
                    in P)
      = let s2 : Intersecting vξ₀ (vεₗ' ◆ iξ₁ ◆ iεₗiξ₀')
            s2 = situation2 vεₗ' iξ₀ iεₗiξ₀' vξ iξ

            γ , ξ₀' , ξ₁' = commute-intersecting s2

            res₀ = (vεₗ ↷-MaybeSparse2CellGen ξ₀') ↶-MaybeSparse2CellGen vεᵣ
            res₁ = (vεₗ ↷-MaybeSparse2CellGen ξ₁') ↶-MaybeSparse2CellGen vεᵣ

        in _ , res₀ , res₁
    --
    --
    --
    -- Case 2.2.2: We know that vεₗ is (strictly) longer than iεₗ. This means that we might have situation 3 or 4. We have to check
    --             in which situation we are by comparing (vεₗ ◆ vξ₁) with (iεₗ ◆ iξ₀)
    commuteFace {μ = μ} {η = η} {ω = ω} (vεₗ ⌟[ vξ₀ ⇒ vξ₁ ∋ vξ ]⌞ vεᵣ [ refl , refl ]) (iεₗ ⌟[ iξ₀ ⇒ iξ₁ ∋ iξ ]⌞ iεᵣ [ ipf₀ , refl ])
      | no (¬iεₗiξ₀⊴vεₗ , vεₗ⊴iεₗiξ₀@(incl (vδ , vδp)))
      | no (¬vεₗvξ₁⊴iεₗ , iεₗ⊴vεₗvξ₁@(incl (iδ , iδp)))
      | no (_ , iεₗ⊴vεₗ@(incl (iεₗ' , refl)))
    --
    -- But before that, we first show that we can write iξ₀ as (iεₗ' ◆ vδ), because we are going to
    -- need this in both subcases.
      with refl <- (let P₀ : iεₗ ◆ iξ₀ ≡ iεₗ ◆ iεₗ' ◆ vδ
                        P₀ = sym-≡ vδp

                        P : iξ₀ ≡ iεₗ' ◆ vδ
                        P = cancelₗ-◆ iεₗ P₀
                    in P)
    --
    -- Now we check whether we are in situation 1 or 2. That is,compare (prefix◆cell) from i and from v.
      with decide-⊴ ((vεₗ ◆ vξ₁) ◆[ vεᵣ ] ⟡-⊴≡ sym-≡ ipf₀) ((iεₗ ◆ iξ₀) ◆[ iεᵣ ])
    --
    -- Case 2.2.2.1: Yes, vεₗvξ₁ is shorter than iεₗiξ₀. This means that we are in case 3 from above.
    ... | yes (vεₗvξ₁⊴iεₗiξ₀@(incl (vεₗvξ₁' , vεₗvξ₁'p)))
    --
    -- We first show that we can write vδ as (vξ₁ ◆ vεₗvξ₁')
      with refl <- (let P₀ : iεₗ ◆ iεₗ' ◆ vξ₁ ◆ vεₗvξ₁' ≡ iεₗ ◆ iεₗ' ◆ vδ
                        P₀ = vεₗvξ₁'p

                        P : vξ₁ ◆ vεₗvξ₁' ≡ vδ
                        P = cancelₗ-◆ (iεₗ ◆ iεₗ') P₀

                    in P)
    --
    -- We also already show that vεᵣ vs (vεₗvξ₁' ◆ iεᵣ), because this makes returning our result easier.
      with refl <- (let P₀ : iεₗ ◆ iεₗ' ◆ vξ₁ ◆ vεₗvξ₁' ◆ iεᵣ ≡ iεₗ ◆ iεₗ' ◆ vδ ◆ iεᵣ
                        P₀ = cong-≡ (_◆ iεᵣ) (vεₗvξ₁'p)

                        P₁ : (iεₗ ◆ iεₗ' ◆ vξ₁ ◆ vεᵣ) ≡ iεₗ ◆ iεₗ' ◆ vξ₁ ◆ vεₗvξ₁' ◆ iεᵣ
                        P₁ = (sym-≡ ipf₀) ∙-≡ P₀

                        P : vεₗvξ₁' ◆ iεᵣ ≡ vεᵣ
                        P = cancelₗ-◆ (iεₗ ◆ iεₗ' ◆ vξ₁) (sym-≡ P₁)
                    in P)
    --
    -- We give the intersection and compute the result as above
      = let s3 : Intersecting (iεₗ' ◆ vξ₀ ◆ vεₗvξ₁') iξ₁
            s3 = situation3 iεₗ' vξ₁ vεₗvξ₁' vξ iξ

            γ , ξ₀' , ξ₁' = commute-intersecting s3

            res₀ = (iεₗ ↷-MaybeSparse2CellGen ξ₀') ↶-MaybeSparse2CellGen iεᵣ
            res₁ = (iεₗ ↷-MaybeSparse2CellGen ξ₁') ↶-MaybeSparse2CellGen iεᵣ

        in _ , res₀ , res₁
    --
    --
    -- Case 2.2.2.1: No, actually, iεₗiξ₀ is shorter than vεₗvξ₁. This means that we are in situatation 4 from above (this is a mirror of situation 1)
    ... | no (¬vεₗvξ₁⊴iεₗiξ₀ , iεₗiξ₀⊴vεₗvξ₁@(incl (iεₗiξ₀' , iεₗiξ₀'p)))

    -- Next we show that we can wrvte vξ₁ as (δ ◆ iεₗiξ₀')
      with refl <- (let P₀ : (iεₗ ◆ iεₗ' ◆ vξ₁) ≡ (iεₗ ◆ iεₗ' ◆ vδ ◆ iεₗiξ₀')
                        P₀ = sym-≡ iεₗiξ₀'p

                        P : vξ₁ ≡ (vδ ◆ iεₗiξ₀')
                        P = cancelₗ-◆ (iεₗ ◆ iεₗ') P₀
                    in P)
    --
    -- We also already show that iεᵣ vs (iεₗiξ₀' ◆ vεᵣ), because thvs makes returnvng our result easver.
      with refl <- (let P₀ : (iεₗ ◆ iξ₀ ◆ iεₗiξ₀' ◆ vεᵣ) ≡ (vεₗ ◆ vξ₁ ◆ vεᵣ)
                        P₀ = cong-≡ (_◆ vεᵣ) (iεₗiξ₀'p)

                        P₁ : (iεₗ ◆ iξ₀ ◆ iεₗiξ₀' ◆ vεᵣ) ≡ (iεₗ ◆ iξ₀ ◆ iεᵣ)
                        P₁ = P₀ ∙-≡ (sym-≡ ipf₀)

                        P : iεₗiξ₀' ◆ vεᵣ ≡ iεᵣ
                        P = cancelₗ-◆ (iεₗ ◆ iξ₀) P₁
                    in P)

      = let s4 : Intersecting (iεₗ' ◆ vξ₀) (iξ₁ ◆ iεₗiξ₀')
            s4 = situation4 iεₗ' vδ iεₗiξ₀' (nonTrivialBy⊴ ¬iεₗiξ₀⊴vεₗ vεₗ⊴iεₗiξ₀) vξ iξ

            γ , ξ₀' , ξ₁' = commute-intersecting s4

            res₀ = (iεₗ ↷-MaybeSparse2CellGen ξ₀') ↶-MaybeSparse2CellGen vεᵣ
            res₁ = (iεₗ ↷-MaybeSparse2CellGen ξ₁') ↶-MaybeSparse2CellGen vεᵣ

        in _ , res₀ , res₁


    commute-single-Sparse2Cell : Sparse2Cell vis μ η -> Sparse2CellGen invis η ω
                              -> ∑ λ η' -> (MaybeSparse2CellGen invis μ η' ×-𝒰 Sparse2Cell vis η' ω)
    commute-single-Sparse2Cell [] ζ = _ , incl ζ , []
    commute-single-Sparse2Cell (ξ ∷ ξs) ζ with commute-single-Sparse2Cell ξs ζ
    ... | _ , id , ξs' = _ , id , (ξ ∷ ξs')
    ... | _ , incl ζ' , ξs' with commuteFace ξ ζ'
    ... | _ , ζ'' , id = _ , ζ'' , ξs'
    ... | _ , ζ'' , incl ξ' = _ , ζ'' , (ξ' ∷ ξs')

    commute-Sparse2Cell : Sparse2Cell vis μ η -> Sparse2Cell invis η ω
                          -> ∑ λ η' -> (Sparse2Cell invis μ η' ×-𝒰 Sparse2Cell vis η' ω)
    commute-Sparse2Cell ξ [] = _ , [] , ξ
    commute-Sparse2Cell ξ (ζ ∷ ζs) with commute-single-Sparse2Cell ξ ζ
    ... | _ , id , ξ' = let _ , ζs' , ξ'' = commute-Sparse2Cell ξ' ζs
                        in _ , ζs' , ξ''
    ... | _ , incl ζ' , ξ' = let _ , ζs' , ξ'' = commute-Sparse2Cell ξ' ζs
                            in _ , (ζ' ∷ ζs') , ξ''

    sparsify-2CellGen : {v : Visibility}
                    {a b : 0Cell G} {ϕs : FreeParts a b} {μ η : 1Cell G a b}
                  -> {μp : Partition n ϕs μ}
                  -> {ηp : Partition n ϕs η}
                  -> 2CellGen v ϕs μp ηp -> Sparse2Cell v μ η
    sparsify-2CellGen (_ ⌟) = []
    sparsify-2CellGen (_⌟[_]⌞_ {ξ₀ = ξ₀} {ξ₁ = ξ₁} ϕ ξ ξs) = (ϕ ⌟[ _ ⇒ _ ∋ ξ ]⌞ _ [ refl , refl ])
                                                          ∷ ((ϕ ◆ ξ₁) ↷-Sparse2Cell sparsify-2CellGen ξs)

    sparsify-Some2CellGen : Some2CellGen v μ η -> Sparse2Cell v μ η
    sparsify-Some2CellGen (incl ξ) = sparsify-2CellGen ξ

    sparsify-2Cell : 2Cell v μ η -> Sparse2Cell v μ η
    sparsify-2Cell [] = []
    sparsify-2Cell (ξ ∷ ξs) = sparsify-Some2CellGen ξ ◆-Sparse2Cell sparsify-2Cell ξs

    unsparsify-Sparse2CellGen : Sparse2CellGen v μ η -> Some2CellGen v μ η
    unsparsify-Sparse2CellGen (εₗ ⌟[ ξ₀ ⇒ ξ₁ ∋ ξ ]⌞ εᵣ [ refl , refl ]) = incl (εₗ ⌟[ ξ ]⌞ εᵣ ⌟)

    unsparsify-Sparse2Cell : Sparse2Cell v μ η -> 2Cell v μ η
    unsparsify-Sparse2Cell [] = []
    unsparsify-Sparse2Cell (ξ ∷ ξs) = pushDownAll (unsparsify-Sparse2CellGen ξ ∷ unsparsify-Sparse2Cell ξs) -- NOTE, we reduce here!

    commute-2Cell : 2Cell vis μ η -> 2Cell invis η ω
                    -> ∑ λ η' -> (2Cell invis μ η' ×-𝒰 2Cell vis η' ω)
    commute-2Cell ξs ζs =
      let _ , ζs' , ξs' = commute-Sparse2Cell (sparsify-2Cell ξs) (sparsify-2Cell ζs)
      in _ , unsparsify-Sparse2Cell ζs' , unsparsify-Sparse2Cell ξs'







