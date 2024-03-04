
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
  --
  -- We need to give a function `f ∶ (n ∶ ℕ / ＠ (u ∧ v)) → (v : Vec BB n / ＠ u) → Vec BB n / ＠ v`
  -- Note that we skip over the narrowing transformations required on n to make the type more readable.
  -- We construct this function by introducing only the first argument `n` with a lambda, and then
  -- do crisp induction on it with a motive
  --   C : (n ∶ ℕ / ＠ (u ∧ v)) ⊢ Vec BB n / ＠ u → Vec BB n / ＠ v.
  --
  -- This means that in the base case, we have to give a function
  --   f₀ : Vec BB 0 / ＠ u → Vec BB 0 / ＠ v
  -- which is done by simply constructing the empty vector at v using `nil`.
  --
  -- In the induction case, we can assume that we already have a function
  --   fₙ : Vec BB n / ＠ u → Vec BB n / ＠ v,
  -- which can send an n-element vector, and we have to upgrade it to a function
  --   fₛₙ : Vec BB (suc n) / ＠ u → Vec BB (suc n) / ＠ v.
  -- We do so by using fₙ to send the tail of (v : Vec BB (suc n)), and then
  -- sending the head of v by using `transform`.
  --
  -- Note that we do need crisp induction here, since our `n : ℕ` is under the `＠ (u ∧ v)`, but we don't
  -- want our result to be under that same annotation.
  --
  --
  -- The implementation of `send-vec` below is mostly complicated by the fact that we need to use the
  -- `conv` rule thrice in order to evaluate function applications in our term. In a proper typechecker
  -- this would happen automatically.
  --
  -- Also note that there are some open agda-holes left. These are places where a proof of well-formedness
  -- of the context is expected, but our partial typechecking algorithm is currently too weak to fill them.
  -- Giving them manually is possible of course, but would complicate the resulting term even more.
  -- We thus left them open.
  send-vec : εε
    ⊢
      Π NN / ＠ uuvv ▹
      Π Vec BB (x0[ τᵈˢ ϕu ]) / ＠ uu ▹
      ⟨ Vec BB (x1[ τᵈˢ ϕv ]) ∣ ＠ vv ⟩ ∥ []
      ≔ _
  send-vec =
    -- We introduce the first argument, (n ∶ ℕ / ＠ (u ∧ v))
    lamⱼ NNⱼ ↦
    -- We convert the result type by applying β-reduction
    conv ((univ (β-red (NNⱼ) ((Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ BBⱼ (var (suc zero) (τᵈˢ ϕv))))) x0[ idTⱼ ]ⱼ)))

      -- The actual work happens here, by using crisp induction, namely
      ((wk-Term natrec-crisp)
      --   1. Our motive is C : (n ∶ ℕ / ＠ (u ∧ v)) ⊢ Vec BB n / ＠ u → Vec BB n / ＠ v.
      ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ_▹_ {μ = ＠ uu} (Vecⱼ (BBⱼ) (var zero (τᵈˢ ϕu))) (Modalⱼ {η = ＠ vv} (Vecⱼ (BBⱼ) (var (suc zero) (τᵈˢ ϕv))))))
      --   2. We do induction on n.
      ∘ⱼ x0ⱼ
      --   3. In the base case we create the empty vector.
      ∘ⱼ conv (symₑ (univ (β-red NNⱼ ((Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ) (var (suc zero) (τᵈˢ ϕv))))) zeroⱼ)))
         (lamⱼ Vecⱼ BBⱼ zeroⱼ ↦ modⱼ nilⱼ)
      --   4. In the induction case we:
      ∘ⱼ (
         --  4.1. Introduce a local n' for which we have to show the induction step.
         lamⱼ NNⱼ ↦
         --  4.2. Introduce fₙ which can send an n-element vector.
         lamⱼ Univⱼ ((lamⱼ NNⱼ ↦ (Πⱼ Vecⱼ BBⱼ x0[ τᵈˢ ϕu ]ⱼ ▹ Modalⱼ (Vecⱼ (BBⱼ ) x1[ τᵈˢ ϕv ]ⱼ))) ∘ⱼ x0ⱼ) ↦ 
         --  4.3. Produce a function which can send an (n'+1)-element vector, but we have to use `conv` again.
         conv (symₑ (univ (β-red (NNⱼ {{{!!}}}) ((Πⱼ Vecⱼ (BBⱼ {{{!!}}} ) x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) (τᵈˢ ϕv))))) (sucⱼ x1ⱼ))))
              -- 4.3.1. Inside of conv, we create fₛₙ by introducing a vector v' of length (n'+1)
              (lamⱼ Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x1[ τᵈˢ ϕu ]ⱼ) ↦
              -- 4.3.2. We call fₙ on the tail of v'. We have to use conv and unmod to extract the result.
                letunmodⱼ[ id ]
                  (
                    (conv (univ (let xx = (β-red ((NNⱼ {{{!!}}})) (((Πⱼ Vecⱼ (BBⱼ {{{!!}}}) x0[ τᵈˢ ϕu ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) x1[ τᵈˢ ϕv ]ⱼ)))) x2ⱼ) in xx))
                      x1[ idTⱼ ]ⱼ
                     ) ∘ⱼ tailⱼ x0[ idTⱼ ]ⱼ
                  )
                  into Modalⱼ ((Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x3[ τᵈˢ ϕv ]ⱼ)))
                  by
                  -- 4.3.3. We prepare sending by letting the head of v'.
                  (letunmodⱼ[ id ] modⱼ {η = ＠ uu} (headⱼ x1ⱼ) into (Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (sucⱼ x4[ τᵈˢ ϕv ]ⱼ)))
                  by
                  modⱼ (
                  -- 4.3.4. We construct the result by sending (head v') and combining with the result of (fₙ (tail v'))
                    consⱼ
                      x0[ (id ★ηᵈˢ★ ＠ uu) ◆*₂ₘ (＠ vv ★εᵈˢ★ id) ]ⱼ

                      (x1ⱼ)
                      )
              ))
         ))


