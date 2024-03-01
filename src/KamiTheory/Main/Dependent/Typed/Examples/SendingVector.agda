
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.SendingVector where

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition
-- open import Agora.Order.Lattice
-- open import Agora.Data.Normal.Definition
-- open import Agora.Data.Normal.Instance.Setoid
-- open import Agora.Data.Normal.Instance.Preorder
-- open import Agora.Data.Normal.Instance.Lattice
-- open import Agora.Data.Normal.Instance.DecidableEquality

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

module Examples2 where
  open Examples

  open Judgements M

  open Typecheck M

  open SendReceiveNarrow-2Graph
  open 2CellDefinition (graph M) hiding ( [_])

  private variable
    -- n m : Nat
    p q : Term M n
    s t u : Term M n
    Γ  : Con (Entry M) n
    A C : Term M n
    B : Term M m
    U V W R : P
    k l o r : Mode M
    μ : ModeHom M k l
    η : ModeHom M o r
    ν : ModeHom M o r
    μs : Restriction k n



  -- natrec-crisp2 : ∀{u} -> εε ⊢
  --   Π (Π NN / ＠ u ▹ UU) / (◻ ◆ ＠ u) ▹
  --   Π NN / ＠ u ▹
  --   (x1 ∘[ ＠ u ] zeroₜ) / (◻ ◆ ＠ u) ▹▹
  --   (Π NN / ＠ u ▹ ((x2 ∘[ ＠ u ] x0) /▹▹ (x2 ∘[ ＠ u ] sucₜ x0))) / (◻ ◆ ＠ u) ▹▹
  --   (x1[ id ★εᵈˢ★ id ] ∘[ ＠ u ] x0) ∥ []
  --   ≔ _
  -- natrec-crisp2 {u = u} =
  --   lamⱼ proof ↦
  --   lamⱼ proof ↦
  --   lamⱼ Univⱼ (x1ⱼ ∘ⱼ zeroⱼ) ↦
  --   lamⱼ (Πⱼ NNⱼ {{{!!}}} ▹ (Πⱼ Univⱼ (x3ⱼ ∘ⱼ x0ⱼ) ▹ Univⱼ (x4ⱼ ∘ⱼ sucⱼ x1ⱼ))) ↦
  --     letunmodⱼ[ id ] wk-Term (wk-Term (wk-Term (wk-Term (natrec-crisp-h)))) ∘ⱼ x3ⱼ
  --       into (Univⱼ (x4[ εᵈˢ ]ⱼ ∘ⱼ x3[ idTⱼ ]ⱼ))
  --       by
  --       (
  --         (wk-Term (wk-Term (wk-Term (wk-Term (wk-Term sync')))) ∘ⱼ (x4[ idTⱼ ]ⱼ ∘ⱼ x3[ id ★ηᵈˢ★ ＠ u ]ⱼ))
  --         ∘ⱼ
  --         modⱼ ((x0ⱼ ∘ⱼ x3ⱼ ∘ⱼ modⱼ x2ⱼ ∘ⱼ modⱼ x1ⱼ))
  --       )




  ---------------------------------------------
  -- For sending vectors we need the narrowing
  -- transformation:

  τᵈˢ : ∀{u v} -> u ≤ v -> ModeTrans* M all (＠ u) (＠ v)
  τᵈˢ {u = u} ϕ = [ (incl (incl (id ⌟[ narrow ϕ ]⌞ id ⌟) ∷ [])) ∣ incl [] ]

  _★τᵈˢ[_]★_ : (μ : ModeHom M k ▲) -> ∀{u v} -> (ϕ : u ≤ v) -> (η : ModeHom M ◯ l) -> ModeTrans* M all ((μ ◆ ＠ u ◆ η)) ((μ ◆ ＠ v ◆ η))
  _★τᵈˢ[_]★_ μ ϕ η = [ (incl (incl (μ ⌟[ narrow ϕ ]⌞ η ⌟) ∷ [])) ∣ incl [] ]

  ϕu : uuvv ≤ uu
  ϕu = refl-≤-𝟚 ∷ (step ∷ (refl-≤-𝟚 ∷ []))

  ϕv : uuvv ≤ vv
  ϕv = step ∷ (refl-≤-𝟚 ∷ (refl-≤-𝟚 ∷ []))

  send-vec : εε
    ⊢
      Π NN / ＠ uuvv ▹
      Π Vec BB (x0[ τᵈˢ ϕu ]) / ＠ uu ▹
      ⟨ Vec BB (x1[ τᵈˢ ϕv ]) ∣ ＠ vv ⟩ ∥ []
      ≔ {!!}
  send-vec =
    lamⱼ NNⱼ ↦
    conv ((univ (β-red (NNⱼ) ((Πⱼ Vecⱼ BBⱼ x0[ {!!} ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) {!!})))) x0[ {!!} ]ⱼ)))
      ((wk-Term natrec-crisp)
      ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ_▹_ {μ = ＠ uu} (Vecⱼ (BBⱼ {{{!!}}}) (var zero (τᵈˢ ϕu))) (Modalⱼ {η = ＠ vv} (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) (τᵈˢ ϕv))))))
      ∘ⱼ x0ⱼ
      ∘ⱼ conv (symₑ (univ (β-red NNⱼ ((Πⱼ Vecⱼ BBⱼ x0[ {!!} ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) {!!})))) zeroⱼ)))
         (lamⱼ {!!} ↦ {!!})
      ∘ⱼ (
         lamⱼ NNⱼ ↦
         lamⱼ Univⱼ ((lamⱼ NNⱼ ↦ (Πⱼ {!!} ▹ {!!})) ∘ⱼ x0ⱼ) ↦ 
         conv (symₑ (univ (β-red (NNⱼ {{{!!}}}) ((Πⱼ Vecⱼ (BBⱼ {{{!!}}}) x0[ {!!} ]ⱼ  ▹ Modalⱼ (Vecⱼ (BBⱼ {{{!!}}}) (var (suc zero) {!!})))) {!!})))
              (lamⱼ {!!} ↦ {!!})
         ))


{-
      -- ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ Vecⱼ BBⱼ ? x0[ id ★τᵈˢ[ ϕu ]★ (◻ ◆ ＠ uuvv) ]ⱼ ▹ Modalⱼ (Vecⱼ BBⱼ x1[ id ★τᵈˢ[ ϕv ]★ (◻ ◆ ＠ uuvv) ]ⱼ)))

-- transₑ ({!Π-cong ? ? ?!}) (univ (β-red (NNⱼ) ((Πⱼ Vecⱼ BBⱼ x0[ (id) ★τᵈˢ[ ϕu ]★ {!!} ]ⱼ  ▹ Modalⱼ (Vecⱼ BBⱼ (var (suc zero) {!!})))) x0ⱼ))

      -}
