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

  instance
    isCategoryData:ModeTrans* : isCategoryData (ModeHom 𝓂 a b) (ModeTrans* 𝓂 all)
    isCategoryData:ModeTrans* = record
                                { isSetoid:Hom = isSetoid:byId
                                ; id = [ incl [] ∣ incl [] ]
                                ; _◆_ = {!!}
                                ; unit-l-◆ = {!!}
                                ; unit-r-◆ = {!!}
                                ; unit-2-◆ = {!!}
                                ; assoc-l-◆ = {!!}
                                ; assoc-r-◆ = {!!}
                                ; _◈_ = {!!}
                                }


  instance
    isCategoryData:Path : isCategoryData (Mode 𝓂) (ModeHom 𝓂)
    isCategoryData:Path = record
                          { isSetoid:Hom = isSetoid:byCategoryData
                          ; id = id'
                          ; _◆_ = _◆'_
                          ; unit-l-◆ = {!!}
                          ; unit-r-◆ = {!!}
                          ; unit-2-◆ = {!!}
                          ; assoc-l-◆ = {!!}
                          ; assoc-r-◆ = {!!}
                          ; _◈_ = {!!}
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


