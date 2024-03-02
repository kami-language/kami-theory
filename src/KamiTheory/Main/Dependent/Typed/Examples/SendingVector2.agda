
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.SendingVector2 where

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition

open import KamiTheory.Basics hiding (typed)
open import KamiTheory.Order.Preorder.Instances
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances


open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Example
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition


open import KamiTheory.Main.Dependent.Typed.Examples.CrispInduction
open import KamiTheory.Main.Dependent.Typed.Examples.SendingVector

module Examples3 where
  open Examples
  open Examples2

  open Judgements M

  open Typecheck M

  open SendReceiveNarrow-2Graph
  open 2CellDefinition (graph M) hiding ( [_])



  send-vec2 : εε
    ⊢
      Π NN / ＠ uu ▹
      Π Vec BB (x0) / ＠ uu ▹
      ⟨ Vec BB (x1[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ vv ★εᵈˢ★ id) ]) ∣ ＠ vv ⟩ ∥ []
      ≔ _
  send-vec2 =
    lamⱼ NNⱼ ↦
    (wk-Term send-vec ∘ⱼ x0[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ uuvv ★εᵈˢ★ id) ]ⱼ)





