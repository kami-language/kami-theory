
-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Linear where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as D
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as Rewriting


module 2CellLinear (G : 2Graph 𝑖) where
  open D.2CellDefinition G
  open Rewriting.2CellRewriting G

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    η : 1Cell G b c
    ω : 1Cell G c d
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f
    v : Visibility

  record SingleFace' v {a d} (μ ν : 1Cell G a d) : 𝒰 𝑖 where
    constructor singleFace
    field face : SingleFace v a d
    field top : μ ≡ ((face .idₗ) ◆ (face .cξ₀) ◆ (face .idᵣ))
    field bot : ν ≡ ((face .idₗ) ◆ (face .cξ₁) ◆ (face .idᵣ))


  data Linear2Cell (v : Visibility) {a b : 0Cell G} :
                (μ : 1Cell G a b)
                (η : 1Cell G a b)
                -> 𝒰 𝑖 where
    [] : Linear2Cell v μ μ
    _∷_ : SingleFace' v μ η -> Linear2Cell v η ω -> Linear2Cell v μ ω


  _⧕-SingleFace_ : (μ : 1Cell G a b) -> SingleFace' v η ω -> SingleFace' v (μ ◆ η) (μ ◆ ω)
  μ ⧕-SingleFace singleFace (idₗ₁ ⌟[ face₁ ]⌞ idᵣ₁) refl-≡ refl-≡ = singleFace ((μ ◆ idₗ₁) ⌟[ face₁ ]⌞ idᵣ₁) refl-≡ refl-≡

  _⧕-Linear_ : (μ : 1Cell G a b) -> Linear2Cell v η ω -> Linear2Cell v (μ ◆ η) (μ ◆ ω)
  μ ⧕-Linear [] = []
  μ ⧕-Linear (x ∷ X) = (μ ⧕-SingleFace x) ∷ (μ ⧕-Linear X)

  linearize-2CellGen :
    {size : ℕ}
    {freeParts : FreeParts a b}
    {domPartition : Partition size freeParts μ}
    {codPartition : Partition size freeParts η}
    (cell : 2CellGen v freeParts domPartition codPartition)
    -> Linear2Cell v μ η
  linearize-2CellGen (_ ⌟) = []
  -- linearize-2CellGen (ϕ ⌟[ ξ ]⌞ cell) =
  linearize-2CellGen (D.2CellDefinition._⌟[_]⌞_ {ξ₀ = ξ₀} {ξ₁ = ξ₁} {μ = μ} ϕ ξ cell) =
    let cell' = linearize-2CellGen cell
        cell'' = ((ϕ ◆ ξ₁) ⧕-Linear cell')
    in singleFace (ϕ ⌟[ ξ ]⌞ μ) refl-≡ refl-≡ ∷ cell''

  _◆₂-Linear_ : Linear2Cell v η ω -> Linear2Cell v ω μ -> Linear2Cell v η μ
  [] ◆₂-Linear Y = Y
  (x ∷ X) ◆₂-Linear Y = x ∷ (X ◆₂-Linear Y)

  linearize : 2Cell v μ η -> Linear2Cell v μ η
  linearize [] = []
  linearize (incl x ∷ X) = linearize-2CellGen x ◆₂-Linear linearize X

