
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



  ---------------------------------------------
  -- For sending vectors we need the narrowing
  -- transformation:

  τᵈˢ : ∀{u v} -> u ≤ v -> ModalityTrans M all (▲ ↝ ◯ ∋ ＠ u) (▲ ↝ ◯ ∋ ＠ v)
  τᵈˢ {u = u} ϕ = _ ⇒ _ ∋ [ (incl (incl (id ⌟[ narrow ϕ ]⌞ id ⌟) ∷ [])) ∣ incl [] ]

{-
  _★τᵈˢ[_]★_ : (μ : ModeHom M k ▲) -> ∀{u v} -> (ϕ : u ≤ v) -> (η : ModeHom M ◯ l) -> ModalityTrans M all (k ↝ l ∋ (μ ◆ ＠ u ◆ η)) (k ↝ l ∋ (μ ◆ ＠ v ◆ η))
  _★τᵈˢ[_]★_ μ ϕ η = _ ⇒ _ ∋ [ (incl (incl (μ ⌟[ narrow ϕ ]⌞ η ⌟) ∷ [])) ∣ incl [] ]

  ϕu : uuvv ≤ uu
  ϕu = refl-≤-𝟚 ∷ (step ∷ (refl-≤-𝟚 ∷ []))

  ϕv : uuvv ≤ vv
  ϕv = step ∷ (refl-≤-𝟚 ∷ (refl-≤-𝟚 ∷ []))

  send-vec : εε
    ⊢
      Π NN / ＠ uuvv ▹
      Π Vec BB (x0[ τᵈˢ ϕu ]) / ＠ uu ▹
      ⟨ Vec BB (x1[ τᵈˢ ϕv ]) ∣ ＠ vv ⟩ / id
      ≔ {!!}
  send-vec =
    lamⱼ NNⱼ ↦
    conv (transₑ ({!Π-cong ? ? ?!}) (univ (β-red (NNⱼ) ((Πⱼ Vecⱼ BBⱼ x0[ (id) ★τᵈˢ[ ϕu ]★ {!!} ]ⱼ  ▹ Modalⱼ (Vecⱼ BBⱼ (var (suc zero) {!!})))) x0ⱼ)))
      ((wk-Term natrec-crisp)
      ∘ⱼ x0ⱼ
      ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ_▹_ {μ = ＠ uu} (Vecⱼ BBⱼ x0[ id ★τᵈˢ[ ϕu ]★ (◻ ◆ ＠ uuvv) ]ⱼ) (Modalⱼ {η = ＠ vv} (Vecⱼ BBⱼ x1[ {!!} ]ⱼ))))
      -- ∘ⱼ (lamⱼ NNⱼ ↦ (Πⱼ Vecⱼ BBⱼ ? x0[ id ★τᵈˢ[ ϕu ]★ (◻ ◆ ＠ uuvv) ]ⱼ ▹ Modalⱼ (Vecⱼ BBⱼ x1[ id ★τᵈˢ[ ϕv ]★ (◻ ◆ ＠ uuvv) ]ⱼ)))
      ∘ⱼ {!lamⱼ ? ↦ ?!}
      ∘ⱼ {!!})
      -}
