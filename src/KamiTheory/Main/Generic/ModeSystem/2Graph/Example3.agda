-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

----------------------------------------------------------
--
-- In this file we define the modes and modalities, and generating 2-cells of
-- the mode-theory of Kami.
--
----------------------------------------------------------


{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Graph.Example3 where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


module PolySendReceive-2Graph (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  private variable
    U V : ⟨ P ⟩

  ---------------------------------------------
  -- modes

  -- modes are "copies" of MLTT inside our type theory
  --
  -- For Kami, each mode corresponds to a different point
  -- of view on the system: The local mode ▲ corresponds
  -- to code executed locally on a single node. The global
  -- mode ◯ corresponds to code related to the whole distributed
  -- system, i.e., in particular synchronization of computations.
  --
  data Mode-PolySR : Set (𝑖 ⌄ 0) where
    ▲ : ⟨ P ⟩ -> Mode-PolySR -- the local mode
    ◯ : Mode-PolySR -- the global mode

  ---------------------------------------------
  -- mode homomorphisms (modalities)
  --
  -- Modalities are morphisms between modes, and are
  -- what occurs most prominently in the resulting type theory.
  -- Types and terms happen to be "under a modality", and
  -- the modality itself describes how the global and local
  -- points of view interact.
  --
  -- The (＠ u ∶ ▲ → ◯) modality shows that we can embed the
  -- local point of view into the global point of view by placing
  -- local code at a location u in the global system.
  --
  -- The `[] ∶ ◯ → ▲` modality shows that we can embed the
  -- global point of view into the local point of view by
  -- allowing types and terms to be "quoted": local code
  -- can refer to global computations which it aims to schedule.
  --
  data BaseModeHom-PolySR : (m n : Mode-PolySR) -> 𝒰 (𝑖 ⌄ 0) where
    `＠` : ∀(U : ⟨ P ⟩) -> BaseModeHom-PolySR (▲ U) ◯
    `[]` : ∀{U} -> BaseModeHom-PolySR ◯ (▲ U)

  ---------------------------------------------
  -- mode transformations
  --
  -- Mode Transformations are morphisms between modalities,
  -- they describe how the different "changes of point of view"
  -- interact.
  --
  -- The narrowing transformation is the easiest to describe:
  -- we have (narrow ∶ ＠ u ⇒ ＠ v) for any locations (u ≤ v).
  -- That is, if types/terms are available at a sublocation u
  -- of v, they are also available at v.
  --
  -- The other two transformations form an adjunction, with
  --
  --  - `send ∶ id ⇒ (＠ u ◆ ◻)` means that local code can
  --    be scheduled to run at a possibly different location.
  --
  --  - `recv ∶ (◻ ◆ ＠ v) ∶ ⇒ id` means that globally, if
  --    a node contains a quoted global computation, this computation,
  --    can be executed, and thus synchronized across nodes.
  --
  -- We also call these transformations "schedule" and "sync" elsewhere.
  --
  data BaseModeTrans-PolySR : Visibility -> {m n : Mode-PolySR} (μs ηs : Path BaseModeHom-PolySR m n) -> 𝒰 𝑖 where
    -- narrow : U ≤ V -> BaseModeTrans-PolySR invis (`＠` U ⨾ id) (`＠` V ⨾ id)
    send : ∀ U -> BaseModeTrans-PolySR vis id (`＠` U ⨾ `[]` ⨾ id)
    recv : ∀ U -> BaseModeTrans-PolySR vis (`[]` ⨾ `＠` U ⨾ id) id


  ------------------------------------------------------------------------
  -- Decidability
  --
  -- In order for the normalization to work, we have to show that our types
  -- have decidable equality.

  decide-≡-Mode-PolySR : (x y : Mode-PolySR) → isDecidable (x ≡ y)
  decide-≡-Mode-PolySR (▲ U) (▲ V) with U ≟ V
  ... | no x = no λ {refl -> x refl}
  ... | yes refl-≡ = yes refl
  decide-≡-Mode-PolySR (▲ _) ◯ = no (λ ())
  decide-≡-Mode-PolySR ◯ (▲ _) = no (λ ())
  decide-≡-Mode-PolySR ◯ ◯ = yes refl-≡

  instance
    hasDecidableEquality:Mode-PolySR : hasDecidableEquality Mode-PolySR
    hasDecidableEquality:Mode-PolySR = record { _≟_ = decide-≡-Mode-PolySR }

  β-decide-≡-Mode-PolySR : ∀{x} -> decide-≡-Mode-PolySR x x ≡ yes refl
  β-decide-≡-Mode-PolySR = {!!}

  {-# REWRITE β-decide-≡-Mode-PolySR #-}

  decide-≡-BaseModeHom-PolySR : ∀{a b} -> (x y : BaseModeHom-PolySR a b) → isDecidable (x ≡ y)
  decide-≡-BaseModeHom-PolySR (`＠` U) (`＠` V) with U ≟ V
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  decide-≡-BaseModeHom-PolySR `[]` `[]` = yes refl

  instance
    hasDecidableEquality:BaseModeHom-PolySR : ∀{a b} -> hasDecidableEquality (BaseModeHom-PolySR a b)
    hasDecidableEquality:BaseModeHom-PolySR = record { _≟_ = decide-≡-BaseModeHom-PolySR }

  β-decide-≡-BaseModeHom-PolySR : ∀{a b} -> {x : BaseModeHom-PolySR a b} -> decide-≡-BaseModeHom-PolySR x x ≡ yes refl
  β-decide-≡-BaseModeHom-PolySR = {!!}

  {-# REWRITE β-decide-≡-BaseModeHom-PolySR #-}

  decide-≡-BaseModeTrans-PolySR : ∀{v a b} -> {μ η : Path BaseModeHom-PolySR a b} -> (x y : BaseModeTrans-PolySR v μ η) → isDecidable (x ≡ y)
  decide-≡-BaseModeTrans-PolySR (send U) (send .U) = yes refl
  decide-≡-BaseModeTrans-PolySR (recv U) (recv .U) = yes refl
  -- decide-≡-BaseModeTrans-PolySR (narrow ϕ) (narrow ψ) with force-≡ ϕ ψ
  -- ... | refl = yes refl

  instance
    hasDecidableEquality:BaseModeTrans-PolySR : ∀{v a b} -> {μ η : Path BaseModeHom-PolySR a b} -> hasDecidableEquality (BaseModeTrans-PolySR v μ η)
    hasDecidableEquality:BaseModeTrans-PolySR = record { _≟_ = decide-≡-BaseModeTrans-PolySR }

  β-decide-≡-BaseModeTrans-PolySR : ∀{v a b} -> {μ η : Path BaseModeHom-PolySR a b} -> {x : BaseModeTrans-PolySR v μ η} -> decide-≡-BaseModeTrans-PolySR x x ≡ yes refl
  β-decide-≡-BaseModeTrans-PolySR = {!!}

  {-# REWRITE β-decide-≡-BaseModeTrans-PolySR #-}

  show-BaseModeHom : ∀{a b} -> BaseModeHom-PolySR a b → Text
  show-BaseModeHom (`＠` U) = "＠"
  show-BaseModeHom `[]` = "◻"

  instance
    hasShow:BaseModeHom-PolySR : ∀{a b} -> hasShow (BaseModeHom-PolySR a b)
    hasShow:BaseModeHom-PolySR = record { show = show-BaseModeHom }


  ------------------------------------------------------------------------
  -- The generating graph of the Kami Mode Theory (PolySR)
  --
  -- It consists of exactly the modes, modalities and mode transformations
  -- described above.
  is2Graph:Mode-PolySR : is2Graph _ Mode-PolySR
  is2Graph:Mode-PolySR = record
    { Edge = BaseModeHom-PolySR
    ; Face = BaseModeTrans-PolySR
    }

  PolySR : 2Graph _
  PolySR = Mode-PolySR since is2Graph:Mode-PolySR -- record
    -- { Point = Mode-PolySR
    -- ; Edge = BaseModeHom-PolySR
    -- ; Face = BaseModeTrans-PolySR
    -- }


