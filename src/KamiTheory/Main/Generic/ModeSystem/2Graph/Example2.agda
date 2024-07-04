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

module KamiTheory.Main.Generic.ModeSystem.2Graph.Example2 where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


module SendNarrow-2Graph (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

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
  data Mode-SN : Set (𝑖 ⌄ 0) where
    ▲ : ⟨ P ⟩ -> Mode-SN -- the local mode
    ◯ : Mode-SN -- the global mode

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
  data BaseModeHom-SN : (m n : Mode-SN) -> 𝒰 (𝑖 ⌄ 0) where
    `＠` : ∀(U : ⟨ P ⟩) -> BaseModeHom-SN (▲ U) ◯
    `[]` : ∀{U} -> BaseModeHom-SN ◯ (▲ U)

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
  data BaseModeTrans-SN : Visibility -> {m n : Mode-SN} (μs ηs : Path BaseModeHom-SN m n) -> 𝒰 𝑖 where
    -- narrow : U ≤ V -> BaseModeTrans-SN invis (`＠` U ⨾ id) (`＠` V ⨾ id)
    send : ∀ U -> BaseModeTrans-SN vis id (`＠` U ⨾ `[]` ⨾ id)
    -- recv : ∀ U -> BaseModeTrans-SN vis (`[]` ⨾ `＠` U ⨾ id) id


  ------------------------------------------------------------------------
  -- Decidability
  --
  -- In order for the normalization to work, we have to show that our types
  -- have decidable equality.

  decide-≡-Mode-SN : (x y : Mode-SN) → isDecidable (x ≡ y)
  decide-≡-Mode-SN (▲ U) (▲ V) with U ≟ V
  ... | no x = no λ {refl -> x refl}
  ... | yes refl-≡ = yes refl
  decide-≡-Mode-SN (▲ _) ◯ = no (λ ())
  decide-≡-Mode-SN ◯ (▲ _) = no (λ ())
  decide-≡-Mode-SN ◯ ◯ = yes refl-≡

  instance
    hasDecidableEquality:Mode-SN : hasDecidableEquality Mode-SN
    hasDecidableEquality:Mode-SN = record { _≟_ = decide-≡-Mode-SN }

  β-decide-≡-Mode-SN : ∀{x} -> decide-≡-Mode-SN x x ≡ yes refl
  β-decide-≡-Mode-SN = {!!}

  {-# REWRITE β-decide-≡-Mode-SN #-}

  decide-≡-BaseModeHom-SN : ∀{a b} -> (x y : BaseModeHom-SN a b) → isDecidable (x ≡ y)
  decide-≡-BaseModeHom-SN (`＠` U) (`＠` V) with U ≟ V
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  decide-≡-BaseModeHom-SN `[]` `[]` = yes refl

  instance
    hasDecidableEquality:BaseModeHom-SN : ∀{a b} -> hasDecidableEquality (BaseModeHom-SN a b)
    hasDecidableEquality:BaseModeHom-SN = record { _≟_ = decide-≡-BaseModeHom-SN }

  β-decide-≡-BaseModeHom-SN : ∀{a b} -> {x : BaseModeHom-SN a b} -> decide-≡-BaseModeHom-SN x x ≡ yes refl
  β-decide-≡-BaseModeHom-SN = {!!}

  {-# REWRITE β-decide-≡-BaseModeHom-SN #-}

  decide-≡-BaseModeTrans-SN : ∀{v a b} -> {μ η : Path BaseModeHom-SN a b} -> (x y : BaseModeTrans-SN v μ η) → isDecidable (x ≡ y)
  decide-≡-BaseModeTrans-SN (send U) (send .U) = yes refl
  -- decide-≡-BaseModeTrans-SN (recv U) (recv .U) = yes refl
  -- decide-≡-BaseModeTrans-SN (narrow ϕ) (narrow ψ) with force-≡ ϕ ψ
  -- ... | refl = yes refl

  instance
    hasDecidableEquality:BaseModeTrans-SN : ∀{v a b} -> {μ η : Path BaseModeHom-SN a b} -> hasDecidableEquality (BaseModeTrans-SN v μ η)
    hasDecidableEquality:BaseModeTrans-SN = record { _≟_ = decide-≡-BaseModeTrans-SN }

  β-decide-≡-BaseModeTrans-SN : ∀{v a b} -> {μ η : Path BaseModeHom-SN a b} -> {x : BaseModeTrans-SN v μ η} -> decide-≡-BaseModeTrans-SN x x ≡ yes refl
  β-decide-≡-BaseModeTrans-SN = {!!}

  {-# REWRITE β-decide-≡-BaseModeTrans-SN #-}

  show-BaseModeHom : ∀{a b} -> BaseModeHom-SN a b → Text
  show-BaseModeHom (`＠` U) = "＠"
  show-BaseModeHom `[]` = "◻"

  instance
    hasShow:BaseModeHom-SN : ∀{a b} -> hasShow (BaseModeHom-SN a b)
    hasShow:BaseModeHom-SN = record { show = show-BaseModeHom }


  ------------------------------------------------------------------------
  -- The generating graph of the Kami Mode Theory (SN)
  --
  -- It consists of exactly the modes, modalities and mode transformations
  -- described above.
  is2Graph:Mode-SN : is2Graph _ Mode-SN
  is2Graph:Mode-SN = record
    { Edge = BaseModeHom-SN
    ; Face = BaseModeTrans-SN
    }

  SN : 2Graph _
  SN = Mode-SN since is2Graph:Mode-SN -- record
    -- { Point = Mode-SN
    -- ; Edge = BaseModeHom-SN
    -- ; Face = BaseModeTrans-SN
    -- }


