
----------------------------------------------------------
--
-- Example terms in the Kami language, sending a vector
--
-- In this file we build the main example, where a vector
-- is sent from process `uu` to `vv`. The length of the
-- vector is common knowledge between these processes,
-- thus located at "uu ∧ vv". This is required for the induction
-- to go through. The induction itself is the crisp-induction
-- for naturals derived in the previous example.
--
----------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.SendingVector where

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

module ExamplesSendingVector where
  open ExamplesBase
  open ExamplesCrispInduction


  ---------------------------------------------
  -- In order for the common knowledge at "uu ∧ vv"
  -- to be usable for both processes `uu` and `vv`,
  -- we need the narrowing transformation.
  --
  -- We call it τᵈˢ here. Generically, `τᵈˢ ϕ` is a transformation
  -- between states at `u` and `v` if `u ≤ v` is a smaller element.


  -- The narrowing transformation
  τᵈˢ : ∀{u v} -> u ≤ v -> ModeTrans* M all (＠ u) (＠ v)
  τᵈˢ {u = u} ϕ = [ (incl (incl (id ⌟[ narrow ϕ ]⌞ id ⌟) ∷ [])) ∣ incl [] ]

  -- The narrowing transformation with additional identities whiskered-on left and right
  _★τᵈˢ[_]★_ : (μ : ModeHom M k ▲) -> ∀{u v} -> (ϕ : u ≤ v) -> (η : ModeHom M ◯ l) -> ModeTrans* M all ((μ ◆ ＠ u ◆ η)) ((μ ◆ ＠ v ◆ η))
  _★τᵈˢ[_]★_ μ ϕ η = [ (incl (incl (μ ⌟[ narrow ϕ ]⌞ η ⌟) ∷ [])) ∣ incl [] ]

  -- Of course the common location `uu ∧ vv` is smaller than both `uu`
  -- and `vv` which means that we can narrow.
  --
  ϕu : uuvv ≤ uu
  ϕu = refl-≤-𝟚 ∷ (step ∷ (refl-≤-𝟚 ∷ []))
  --
  ϕv : uuvv ≤ vv
  ϕv = step ∷ (refl-≤-𝟚 ∷ (refl-≤-𝟚 ∷ []))


  ---------------------------------------------
  -- Sending a vector between processes by sending n elements individually.
  --
  -- Conceptually, the example is simple:
  -- We use crisp induction to 
  send-vec : εε
    ⊢
      Π NN / ＠ uuvv ▹
      Π Vec BB (x0[ τᵈˢ ϕu ]) / ＠ uu ▹
      ⟨ Vec BB (x1[ τᵈˢ ϕv ]) ∣ ＠ vv ⟩ ∥ []
      ≔ {!!}
  send-vec =
    lamⱼ NNⱼ ↦
    conv ((univ (β-red (NNⱼ) ((Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ BBⱼ (var (suc zero) (τᵈˢ ϕv))))) x0[ idTⱼ ]ⱼ)))
      ((wk-Term natrec-crisp)
      ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ_▹_ {μ = ＠ uu} (Vecⱼ (BBⱼ) (var zero (τᵈˢ ϕu))) (Modalⱼ {η = ＠ vv} (Vecⱼ (BBⱼ) (var (suc zero) (τᵈˢ ϕv))))))
      ∘ⱼ x0ⱼ
      ∘ⱼ conv (symₑ (univ (β-red NNⱼ ((Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ) (var (suc zero) (τᵈˢ ϕv))))) zeroⱼ)))
         (lamⱼ Vecⱼ BBⱼ zeroⱼ ↦ modⱼ nilⱼ)
      ∘ⱼ (
         lamⱼ NNⱼ ↦
         lamⱼ Univⱼ ((lamⱼ NNⱼ ↦ (Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ ▹ Modalⱼ (Vecⱼ (BBⱼ ) x1[ τᵈˢ ϕv ]ⱼ))) ∘ⱼ x0ⱼ) ↦ 
         conv (symₑ (univ (β-red (NNⱼ {{{!!}}}) ((Πⱼ Vecⱼ (BBⱼ {{{!!}}} ) x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) (τᵈˢ ϕv))))) (sucⱼ x1ⱼ))))
              (lamⱼ Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x1[ τᵈˢ ϕu ]ⱼ) ↦
                letunmodⱼ[ id ]
                  (
                    -- (conv (univ (β-red (NNⱼ {{{!!}}}) ((Πⱼ Vecⱼ (BBⱼ {{{!!}}}) ?  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) ?))) {!!}))
                    (conv (univ (let xx = (β-red ((NNⱼ {{{!!}}})) (((Πⱼ Vecⱼ (BBⱼ {{{!!}}}) x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) x1[ τᵈˢ ϕv ]ⱼ)))) x2ⱼ) in xx))
                      x1[ idTⱼ ]ⱼ
                     ) ∘ⱼ tailⱼ x0[ idTⱼ ]ⱼ
                  )
                  into Modalⱼ ((Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x3[ τᵈˢ ϕv ]ⱼ)))
                  by
                  (letunmodⱼ[ id ] modⱼ {η = ＠ uu} (headⱼ x1ⱼ) into (Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x4[ τᵈˢ ϕv ]ⱼ)))
                  -- by x0[ {! (? ★ηᵈˢ★ id) ◆*₂ₘ (id ★εᵈˢ★ ?)!} ]ⱼ)
                  by
                  modⱼ (
                    consⱼ
                      x0[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ vv ★εᵈˢ★ id) ]ⱼ

                      (x1ⱼ
                      )
                      )
              ))
         ))


