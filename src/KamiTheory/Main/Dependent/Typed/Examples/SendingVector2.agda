-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

----------------------------------------------------------
--
-- Example terms in the Kami language, sending a vector - part 2
--
-- In the previous example, the length of the vector was common
-- knowledge of both processes before sending. This was required
-- for the induction to go through.
--
-- But what we actually want is of course the case where the second process
-- doesn't know the length beforehand.
--
-- The interactions between τᵈˢ and ηᵈˢ allow us to construct
-- such a program very easily on top of the previous example.
--
----------------------------------------------------------

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


open import KamiTheory.Main.Dependent.Typed.Examples.Base
open import KamiTheory.Main.Dependent.Typed.Examples.CrispInduction
open import KamiTheory.Main.Dependent.Typed.Examples.SendingVector

module ExamplesSendingVector2 where
  open ExamplesBase
  open ExamplesCrispInduction
  open ExamplesSendingVector



  -- A function of type
  --
  --    (n ∶ ℕ / ＠ u) → (v : Vec BB n / ＠ u) → Vec BB n / ＠ v
  --
  -- can be easily given by first sending `n` from `＠ u` to `＠ u ∧ v`,
  -- and then applying the previous `send-vec`-example.
  --
  -- Note that we skipped over the variable annotations in the type, which
  -- state that the length of the resulting vector is not actually n itself,
  -- but is the sent value of n.
  --
  -- In particular this example only typechecks because a "send to (u ∧ v)" followed by
  -- a "narrow (u ∧ v) to u" transformations, reduces to a "send to u" transformation;
  -- and moreover, sending and receiving at the same location reduces to the identity.
  --
  -- A detailed explanation will be available elsewhere in a forthcoming document.
  --
  send-vec2 : εε
    ⊢
      Π NN / ＠ uu ▹
      Π Vec BB (x0) / ＠ uu ▹
      ⟨ Vec BB (x1[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ vv ★εᵈˢ★ id) ]) ∣ ＠ vv ⟩ ∥ []
      ≔ _
  send-vec2 =
    lamⱼ NNⱼ ↦
    (wk-Term send-vec ∘ⱼ x0[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ uuvv ★εᵈˢ★ id) ]ⱼ)





