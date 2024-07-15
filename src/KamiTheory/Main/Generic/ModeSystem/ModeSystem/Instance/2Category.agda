-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category where

open import Agora.Conventions hiding (_∣_)
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Morphism.Iso.Definition
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
  renaming ( id to id'
           ; _◆_ to _◆'_
           )

import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Commutation as 2CellCommutation
import KamiTheory.Main.Generic.ModeSystem.2Cell.Decidability as 2CellDecidability
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition


module ModeSystemAs2Category (𝓂 : ModeSystem 𝑖) where
  private variable
    a b c : Mode 𝓂
    μ ν η ω : ModeHom 𝓂 a b

  open 2CellDefinition.2CellDefinition (graph 𝓂)
  open 2CellDecidability.2CellDecidability (graph 𝓂)


  -- unit-l-◆₂ₘ-2Cell : ∀{r} -> ∀{a b : Mode 𝓂} -> {μ η : ModeHom 𝓂 a b} -> {f : ModeTrans 𝓂 r μ η} 
  --                  -> incl [] ◆₂ₘ f ≡ f
  -- unit-l-◆₂ₘ-2Cell = {!!}

  postulate
    unit-l-◆₂ₘ*-2Cell : ∀{a b : Mode 𝓂} -> {μ η : ModeHom 𝓂 a b} -> {f : ModeTrans* 𝓂 all μ η} 
                    -> [ incl [] ∣ incl [] ] ◆*₂ₘ f ≡ f

    unit-r-◆₂ₘ*-2Cell : ∀{a b : Mode 𝓂} -> {μ η : ModeHom 𝓂 a b} -> {f : ModeTrans* 𝓂 all μ η} 
                    -> f ◆*₂ₘ [ incl [] ∣ incl [] ] ≡ f


    assoc-l-◆₂ₘ*-2Cell : ∀{a b : Mode 𝓂} -> {μ η ω ϕ : ModeHom 𝓂 a b}
                       -> {f : ModeTrans* 𝓂 all μ η} 
                       -> {g : ModeTrans* 𝓂 all η ω} 
                       -> {h : ModeTrans* 𝓂 all ω ϕ} 
                    -> (f ◆*₂ₘ g) ◆*₂ₘ h ≡ f ◆*₂ₘ (g ◆*₂ₘ h)
    -- unit-l-◆₂ₘ*-2Cell {f = [ _ ∣ _ ]}= {!!}

  -- {-# REWRITE unit-r-◆₂ₘ*-2Cell #-}
  -- {-# REWRITE unit-l-◆₂ₘ*-2Cell #-}
  -- {-# REWRITE assoc-l-◆₂ₘ*-2Cell #-}

  instance
    isCategoryData:ModeTrans* : isCategoryData (ModeHom 𝓂 a b) (ModeTrans* 𝓂 all)
    isCategoryData:ModeTrans* = record
                                { isSetoid:Hom = isSetoid:byId
                                ; id = [ incl [] ∣ incl [] ]
                                ; _◆_ = _◆*₂ₘ_
                                ; unit-l-◆ = incl unit-l-◆₂ₘ*-2Cell -- λ {{[ incl f0 ∣ incl f1 ]} -> ?}
                                ; unit-r-◆ = incl unit-r-◆₂ₘ*-2Cell
                                ; unit-2-◆ = incl (unit-r-◆₂ₘ*-2Cell {f = [ incl [] ∣ incl [] ]})
                                ; assoc-l-◆ = incl assoc-l-◆₂ₘ*-2Cell
                                ; assoc-r-◆ = incl (sym-≡ assoc-l-◆₂ₘ*-2Cell)
                                ; _◈_ = λ { (incl refl-≡) (incl refl-≡) → incl refl-≡}
                                }

  private instance
    isCategory:ModeHom : isCategory (ModeHom 𝓂 a b)
    isCategory:ModeHom = record { Hom = ModeTrans* 𝓂 all }

  instance
    isCategoryData:Path : isCategoryData (Mode 𝓂) (ModeHom 𝓂)
    isCategoryData:Path = record
                          { isSetoid:Hom = isSetoid:byCategoryData
                          ; id = id'
                          ; _◆_ = _◆'_
                          ; unit-l-◆ = incl refl-≅
                          ; unit-r-◆ = incl refl-≅
                          ; unit-2-◆ = incl refl-≅
                          ; assoc-l-◆ = incl refl-≅
                          ; assoc-r-◆ = incl refl-≅
                          ; _◈_ = λ p q -> incl ((⟨ ⟨ p ⟩ ⟩ ◆ₘ* ⟨ ⟨ q ⟩ ⟩  ) since record
                                { inverse-◆ = (⟨ ⟨ p ⟩ ⟩⁻¹ ◆ₘ* ⟨ ⟨ q ⟩ ⟩⁻¹)
                                ; inv-r-◆ = {!!}
                                ; inv-l-◆ = {!!}
                                })
                          }

  instance
    isCategory:byModeSystem : isCategory (Mode 𝓂)
    isCategory:byModeSystem = record { Hom = ModeHom 𝓂 }

  -- private instance
  --   _ = isCategory:byModeSystem



  instance
    is2Category:byModeSystem : is2Category (Mode 𝓂 since it)
    is2Category:byModeSystem = record
      { 2Hom = ModeTrans* 𝓂 all
      ; 2HomData = it
      ; isFunctor:Comp = {!!}
      ; isFunctor:Id = {!!}
      ; 2celliso = λ x -> ⟨ x ⟩
      }

  -- ModeSystemAs2Category : 2Category _
  -- ModeSystemAs2Category = Mode 𝓂 since it

