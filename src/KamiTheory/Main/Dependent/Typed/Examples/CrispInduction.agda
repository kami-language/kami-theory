-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

----------------------------------------------------------
--
-- Example terms in the Kami language, crisp induction
--
-- In this file we derive crisp induction rules for both
-- booleans and naturals under the `＠ u` modality.
--
-- This follows very closely 123ff. of the MTT thesis [1].
--
-- -[1]: http://www.danielgratzer.com/papers/phd-thesis.pdf
--
----------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.CrispInduction where

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


module ExamplesCrispInduction where

  open ExamplesBase


  ---------------------------------------------
  -- We can state the unit and counit of the (＠ u ⊣ ◻) adjunction.
  --
  -- We call the unit of this adjunction "dispatch", because it allows
  -- us to schedule computations (at possibly different) locations.
  --
  ηᵈˢ : ∀{u} -> ModeTrans* M all (id) (`＠` u ⨾ ◻)
  ηᵈˢ {u = u} = [ incl [] ∣ (incl (incl (id ⌟[ send u ]⌞ id ⌟) ∷ [])) ]

  _★ηᵈˢ★_ : (μ : ModeHom M k ▲) (η : ModeHom M ▲ l) -> ∀{u} -> ModeTrans* M all ((μ ◆ η)) ((μ ◆ ＠ u ◆ ◻ ◆ η))
  _★ηᵈˢ★_ μ η {u = u} = [ incl [] ∣ (incl (incl (μ ⌟[ send u ]⌞ η ⌟) ∷ [])) ]

  dispatch : ε ⊢ (Π UU /▹ x0 /▹▹ ⟨ x0[ ηᵈˢ ] ∣ ＠ uu ◆ ◻  ⟩) ∥ []
             ≔ lam↦ lam↦ mod[ ＠ uu ◆ ◻ ] x0[ ηᵈˢ ]
  dispatch = lamⱼ UUⱼ ↦
             lamⱼ Univⱼ x0ⱼ ↦
             modⱼ x0[ ηᵈˢ ]ⱼ


  --
  -- The counit on the other hand allows us to wait for the execution
  -- of previously dispatched executions. We thus call it "sync".
  --
  εᵈˢ : ∀{u} -> ModeTrans* M all ((◻ ◆ ＠ u)) (id)
  εᵈˢ {u = u} = [ incl [] ∣ (incl (incl (id ⌟[ recv u ]⌞ id ⌟) ∷ [])) ]

  _★εᵈˢ★_ : (μ : ModeHom M k ◯) (η : ModeHom M ◯ l) -> ∀{u} -> ModeTrans* M all ((μ ◆ ◻ ◆ ＠ u ◆ η)) ((μ ◆ η))
  _★εᵈˢ★_ μ η {u = u} = [ incl [] ∣ (incl (incl (μ ⌟[ recv u ]⌞ η ⌟) ∷ [])) ]

  sync : ε ⊢ (Π UU / (◻ ◆ ＠ uu) ▹ ⟨ x0 ∣ ◻ ◆ ＠ uu  ⟩ /▹▹ x0[ εᵈˢ ]) ∥ []
         ≔ lam↦ lam↦ letunmod x0 into x2[ εᵈˢ ] by x0[ εᵈˢ ]
  sync = lamⱼ UUⱼ ↦
         lamⱼ Modalⱼ (Univⱼ x0ⱼ) ↦
         letunmodⱼ x0ⱼ into Univⱼ x2[ εᵈˢ ]ⱼ by
         x0[ εᵈˢ ]ⱼ

  --
  -- We also need an alternative formulation of the counit, where
  -- there are two nested modalities instead of a single composed one in the codomain.
  --
  sync' : ∀{u} -> ε ⊢ (Π UU / (◻ ◆ ＠ u) ▹ ⟨ ⟨ x0 ∣ ◻ ⟩ ∣ ＠ u ⟩ /▹▹ x0[ εᵈˢ ]) ∥ []
         ≔ lam↦ lam↦ letunmod x0 into x2[ εᵈˢ ] by (letunmod[ ＠ u ] x0 into x3[ εᵈˢ ] by x0[ εᵈˢ ])
  sync' {u = u} =
    lamⱼ UUⱼ ↦
    lamⱼ Modalⱼ (Modalⱼ (Univⱼ x0ⱼ)) ↦
    letunmodⱼ x0ⱼ into Univⱼ x2[ εᵈˢ ]ⱼ by
    letunmodⱼ[ ＠ u ] x0ⱼ into Univⱼ x3[ εᵈˢ ]ⱼ by
    x0[ εᵈˢ ]ⱼ





  ----------------------------------------------------------
  -- boolrec-crisp
  ----------------------------------------------------------
  --
  -- Crisp induction is derived by first instantiating a
  -- helper function which works under the `＠ uu` modality.
  --

  boolrec-crisp-h : εε ⊢ (Π (Π BB / (＠ uu) ▹ UU) / ◻ ◆ ＠ uu ▹
                         ⟨
                          Π BB /▹
                          ⟨ x1 ∘[ _ ] falseₜ ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ _ ] trueₜ ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ _ ] x0[ _★ηᵈˢ★_ id id ] ∣ ◻ ⟩
                         ∣
                          ＠ uu
                         ⟩)
                          ∥ []
                       ≔ _

  boolrec-crisp-h = lamⱼ Πⱼ BBⱼ ▹ UUⱼ ↦ modⱼ
                    (lamⱼ BBⱼ ↦
                     lamⱼ Modalⱼ (Univⱼ (x1ⱼ ∘ⱼ falseⱼ)) ↦
                     lamⱼ Modalⱼ (Univⱼ (x2ⱼ ∘ⱼ trueⱼ)) ↦
                     boolrecⱼ x2ⱼ into Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id id ]ⱼ))
                       false: x1ⱼ
                       true: x0ⱼ
                    )


  --
  -- To get the proper principle, we use `sync'`, in order to transform the motive
  -- from under the (◻ ◆ ＠ uu) to the identity modality.
  --
  boolrec-crisp : εε ⊢
    Π (Π BB / (＠ uu) ▹ UU) / (◻ ◆ ＠ uu) ▹
    Π BB / ＠ uu ▹
    (x1 ∘[ ＠ uu ] falseₜ) / (◻ ◆ ＠ uu) ▹▹
    (x1 ∘[ ＠ uu ] trueₜ)  / (◻ ◆ ＠ uu) ▹▹
    (x1[ id ★εᵈˢ★ id ] ∘[ ＠ uu ] x0[ idTⱼ ]) ∥ []
    ≔ _
  boolrec-crisp =
    lamⱼ proof ↦
    lamⱼ proof ↦
    lamⱼ Univⱼ (x1ⱼ ∘ⱼ falseⱼ) ↦
    lamⱼ Univⱼ (x2ⱼ ∘ⱼ trueⱼ) ↦
      letunmodⱼ[ id ] wk-Term (wk-Term (wk-Term (wk-Term (boolrec-crisp-h)))) ∘ⱼ x3ⱼ
        into (Univⱼ (x4[ εᵈˢ ]ⱼ ∘ⱼ x3[ idTⱼ ]ⱼ))
        by
        (
          (wk-Term (wk-Term (wk-Term (wk-Term (wk-Term sync')))) ∘ⱼ (x4ⱼ ∘ⱼ x3[ id ★ηᵈˢ★ ＠ uu ]ⱼ))
          ∘ⱼ
          modⱼ ((x0ⱼ ∘ⱼ x3ⱼ ∘ⱼ modⱼ x2ⱼ ∘ⱼ modⱼ x1ⱼ))
        )






  ----------------------------------------------------------
  -- natrec-crisp
  ----------------------------------------------------------
  --
  -- We do the same again, crisp induction is derived by first
  -- instantiating a helper function which works under the `＠ uu` modality.
  --

  natrec-crisp-h : ∀{u} -> εε ⊢ (Π (Π NN / (＠ u) ▹ UU) / ◻ ◆ ＠ u ▹
                         ⟨
                          Π NN /▹
                          ⟨ x1 ∘[ ＠ u ] zeroₜ ∣ ◻ ⟩ /▹▹
                          ⟨ Π NN / ＠ u ▹ ((x2 ∘[ ＠ u ] x0) /▹▹ (x2 ∘[ ＠ u ] (sucₜ x0))) ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ ＠ u ] x0[ _★ηᵈˢ★_ id id ] ∣ ◻ ⟩
                         ∣
                          ＠ u
                         ⟩)
                          ∥ []
                       ≔ _

  natrec-crisp-h {u = u} = lamⱼ Πⱼ NNⱼ ▹ UUⱼ ↦ modⱼ
                    (lamⱼ NNⱼ ↦
                     lamⱼ Modalⱼ (Univⱼ (x1ⱼ ∘ⱼ zeroⱼ)) ↦
                     lamⱼ Modalⱼ (Πⱼ NNⱼ ▹ (Πⱼ Univⱼ (x3ⱼ ∘ⱼ x0ⱼ) ▹ Univⱼ (x4ⱼ ∘ⱼ sucⱼ x1ⱼ))) ↦
                     natrecⱼ x2ⱼ into Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id id ]ⱼ))
                       zero: x1ⱼ
                       suc: (lamⱼ NNⱼ ↦
                             lamⱼ Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id id ]ⱼ)) ↦
                             letunmodⱼ x0ⱼ
                               into (Modalⱼ (Univⱼ (x6ⱼ ∘ⱼ sucⱼ (x2[ _★ηᵈˢ★_ id id ]ⱼ))))
                               by (letunmodⱼ x3ⱼ
                                     into (Modalⱼ (Univⱼ (x7ⱼ ∘ⱼ sucⱼ (x3[ _★ηᵈˢ★_ id id ]ⱼ))))
                                     by modⱼ (x0ⱼ ∘ⱼ x3[ _★ηᵈˢ★_ id id ]ⱼ ∘ⱼ x1[ idTⱼ ]ⱼ)
                                     )
                            )
                    )

  --
  -- To get the proper principle, we use `sync'`, in order to transform the motive
  -- from under the (◻ ◆ ＠ uu) to the identity modality.
  --
  natrec-crisp : ∀{u} -> εε ⊢
    Π (Π NN / ＠ u ▹ UU) / (◻ ◆ ＠ u) ▹
    Π NN / ＠ u ▹
    (x1 ∘[ ＠ u ] zeroₜ) / (◻ ◆ ＠ u) ▹▹
    (Π NN / ＠ u ▹ ((x2 ∘[ ＠ u ] x0) /▹▹ (x2 ∘[ ＠ u ] sucₜ x0))) / (◻ ◆ ＠ u) ▹▹
    (x1[ id ★εᵈˢ★ id ] ∘[ ＠ u ] x0) ∥ []
    ≔ _
  natrec-crisp {u = u} =
    lamⱼ proof ↦
    lamⱼ proof ↦
    lamⱼ Univⱼ (x1ⱼ ∘ⱼ zeroⱼ) ↦
    lamⱼ (Πⱼ NNⱼ ▹ (Πⱼ Univⱼ (x3ⱼ ∘ⱼ x0ⱼ) ▹ Univⱼ (x4ⱼ ∘ⱼ sucⱼ x1ⱼ))) ↦
      letunmodⱼ[ id ] wk-Term (wk-Term (wk-Term (wk-Term (natrec-crisp-h)))) ∘ⱼ x3ⱼ
        into (Univⱼ (x4[ εᵈˢ ]ⱼ ∘ⱼ x3[ idTⱼ ]ⱼ))
        by
        (
          (wk-Term (wk-Term (wk-Term (wk-Term (wk-Term sync')))) ∘ⱼ (x4[ idTⱼ ]ⱼ ∘ⱼ x3[ id ★ηᵈˢ★ ＠ u ]ⱼ))
          ∘ⱼ
          modⱼ ((x0ⱼ ∘ⱼ x3ⱼ ∘ⱼ modⱼ x2ⱼ ∘ⱼ modⱼ x1ⱼ))
        )


