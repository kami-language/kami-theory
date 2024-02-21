
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Example where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition


import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as Ex

--
-- We state some 2cells as examples.
--

module SendReceiveNarrow-2Cells (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  open Ex.SendReceiveNarrow-2Graph P

  module RewriteCells where
    ---------------------------------------------
    -- evaluating send/recv pairs
    --
    -- There are two evaluation rules for the adjunction,
    -- dependending on whether send or recv comes first.
    --
    -- We state both.

    -------------------
    -- send comes first
    SR-eval-dom : (U : ⟨ P ⟩) -> 2Cell SRN vis (`＠` U ⨾ id) (`＠` U ⨾ id)
    SR-eval-dom U = incl (id ⌟[ send U ]⌞ (`＠` U ⨾ id) ⌟)
                  ∷ incl ((`＠` U ⨾ id) ⌟[ recv U ]⌞ id ⌟)
                  ∷ []

    SR-eval-cod : (U : ⟨ P ⟩) -> 2Cell SRN vis (`＠` U ⨾ id) (`＠` U ⨾ id)
    SR-eval-cod U = []


    -------------------
    -- recv comes first
    RS-eval-dom : (U : ⟨ P ⟩) -> 2Cell SRN vis (`[]` ⨾ id) (`[]` ⨾ id)
    RS-eval-dom U = incl ((`[]` ⨾ id) ⌟[ send U ]⌞ id ⌟)
                  ∷ incl (id ⌟[ recv U ]⌞ (`[]` ⨾ id) ⌟)
                  ∷ []

    RS-eval-cod : 2Cell SRN vis (`[]` ⨾ id) (`[]` ⨾ id)
    RS-eval-cod = []

    ---------------------------------------------
    -- evaluating narrow/narrow pairs
    --
    -- narrow pairs can be composed
    NN-eval-dom : {U V W : ⟨ P ⟩}
                  -> (ϕ : U ≤ V) (ψ : V ≤ W)
                  -> 2Cell SRN invis (`＠` U ⨾ id) (`＠` W ⨾ id)
    NN-eval-dom ϕ ψ = incl (id ⌟[ narrow ϕ ]⌞ id ⌟)
                    ∷ incl (id ⌟[ narrow ψ ]⌞ id ⌟)
                    ∷ []

    NN-eval-cod : {U V W : ⟨ P ⟩}
                  -> (ϕ : U ≤ V) (ψ : V ≤ W)
                  -> 2Cell SRN invis (`＠` U ⨾ id) (`＠` W ⨾ id)
    NN-eval-cod ϕ ψ = incl (id ⌟[ narrow (ϕ ⟡ ψ) ]⌞ id ⌟)
                    ∷ []


module Examples where

  open import Data.Fin using (#_ ; zero ; suc)
  open import Data.List using (_∷_ ; [])

  open import Agora.Order.Preorder
  open import Agora.Order.Lattice
  open import Agora.Data.Normal.Definition
  open import Agora.Data.Normal.Instance.Setoid
  open import Agora.Data.Normal.Instance.Preorder
  open import Agora.Data.Normal.Instance.Lattice
  open import Agora.Data.Normal.Instance.DecidableEquality

  open import KamiTheory.Data.Open.Definition
  open import KamiTheory.Data.UniqueSortedList.Definition
  open import KamiTheory.Order.StrictOrder.Base
  open import KamiTheory.Order.StrictOrder.Instances.UniqueSortedList

  PP : Preorder _
  PP = -- QQ
    ′_′ (Normalform ((𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 3))) since isNormalizable:𝒪ᶠⁱⁿ⁻ʷᵏ)) {_} {{isPreorder:𝒩 {{isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ {{isSetoid:𝒫ᶠⁱⁿ}} {{isPreorder:𝒫ᶠⁱⁿ}} {{isDecidablePreorder:≤-𝒫ᶠⁱⁿ}}}}}}

  instance
    isProp:≤ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)
    isProp:≤ = {!!}

  open Ex.SendReceiveNarrow-2Graph PP {{{!isProp:≤!}}}


  uu : ⟨ PP ⟩
  uu = (((⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  vv : ⟨ PP ⟩
  vv = (((⦗ # 1 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  ww : ⟨ PP ⟩
  ww = (((⦗ # 2 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  G : 2Graph _
  G = (SRN {{isProp:≤}})

  pat : 2CellLinePattern G vis _ 1
  pat = record { State = S ; start = tt ; step = s }
    where
      S : ℕ -> 𝒰₀
      S zero = 𝟙-𝒰
      S (suc i) = 𝟙-𝒰

      s : {i : ℕ} → S i → {a b : 0Cell G} (ξ : SingleFace G vis a b) →
          Maybe (SubSingleFace G vis ξ ×-𝒰 𝟙-𝒰)
      s st (idₗ₁ ⌟[ send U ]⌞ idᵣ₁) with U ≟ vv
      ... | no p = nothing
      ... | yes p = yes (record
                          { extₗ = idₗ₁
                          ; keepₗ = id
                          ; keepᵣ = id
                          ; extᵣ = idᵣ₁
                          ; proofₗ = {!!}
                          ; proofᵣ = {!!}
                          } , tt)
      s st (idₗ₁ ⌟[ recv U ]⌞ idᵣ₁) = nothing
      -- s st (idₗ₁ ⌟[ narrow x ]⌞ idᵣ₁) = nothing


  ξ₀ : Some2CellGen G vis id _
  ξ₀ = incl ((id) ⌟[ send uu ]⌞ (id) ⌟[ send vv ]⌞ (id) ⌟)

  -- We try to find the send vv face
  result = findNext G pat _ (get ξ₀)

  ξ : 2Cell G vis (`＠` vv ⨾ id) (`＠` vv ⨾ id)
  ξ = SendReceiveNarrow-2Cells.RewriteCells.SR-eval-dom PP {{{!!}}} vv

  -- now lets try to find sth in a 2cell
  result2 = findAll G pat ξ
