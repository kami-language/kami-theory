
----------------------------------------------------------
--
-- In this file we define the modes and modalities, and generating 2-cells of
-- the mode-theory of Kami.
--
----------------------------------------------------------


{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Graph.Example where

open import Agora.Conventions
open import Agora.Order.Preorder
open import KamiTheory.Basics

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


module SendReceiveNarrow-2Graph (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

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
  data Mode-SRN : Set where
    ▲ : Mode-SRN -- the local mode
    ◯ : Mode-SRN -- the global mode

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
  data BaseModeHom-SRN : (m n : Mode-SRN) -> 𝒰 (𝑖 ⌄ 0) where
    `＠` : ∀(U : ⟨ P ⟩) -> BaseModeHom-SRN ▲ ◯
    `[]` : BaseModeHom-SRN ◯ ▲

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
  data BaseModeTrans-SRN : Visibility -> {m n : Mode-SRN} (μs ηs : Path BaseModeHom-SRN m n) -> 𝒰 𝑖 where
    narrow : U ≤ V -> BaseModeTrans-SRN invis (`＠` U ⨾ id) (`＠` V ⨾ id)
    send : ∀ U -> BaseModeTrans-SRN vis id (`＠` U ⨾ `[]` ⨾ id)
    recv : ∀ U -> BaseModeTrans-SRN vis (`[]` ⨾ `＠` U ⨾ id) id


  ------------------------------------------------------------------------
  -- Decidability
  --
  -- In order for the normalization to work, we have to show that our types
  -- have decidable equality.

  decide-≡-Mode-SRN : (x y : Mode-SRN) → isDecidable (x ≡ y)
  decide-≡-Mode-SRN ▲ ▲ = yes refl-≡
  decide-≡-Mode-SRN ▲ ◯ = no (λ ())
  decide-≡-Mode-SRN ◯ ▲ = no (λ ())
  decide-≡-Mode-SRN ◯ ◯ = yes refl-≡

  instance
    hasDecidableEquality:Mode-SRN : hasDecidableEquality Mode-SRN
    hasDecidableEquality:Mode-SRN = record { _≟_ = decide-≡-Mode-SRN }

  β-decide-≡-Mode-SRN : ∀{x} -> decide-≡-Mode-SRN x x ≡ yes refl
  β-decide-≡-Mode-SRN = {!!}

  {-# REWRITE β-decide-≡-Mode-SRN #-}

  decide-≡-BaseModeHom-SRN : ∀{a b} -> (x y : BaseModeHom-SRN a b) → isDecidable (x ≡ y)
  decide-≡-BaseModeHom-SRN (`＠` U) (`＠` V) with U ≟ V
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  decide-≡-BaseModeHom-SRN `[]` `[]` = yes refl

  instance
    hasDecidableEquality:BaseModeHom-SRN : ∀{a b} -> hasDecidableEquality (BaseModeHom-SRN a b)
    hasDecidableEquality:BaseModeHom-SRN = record { _≟_ = decide-≡-BaseModeHom-SRN }

  β-decide-≡-BaseModeHom-SRN : ∀{a b} -> {x : BaseModeHom-SRN a b} -> decide-≡-BaseModeHom-SRN x x ≡ yes refl
  β-decide-≡-BaseModeHom-SRN = {!!}

  {-# REWRITE β-decide-≡-BaseModeHom-SRN #-}

  decide-≡-BaseModeTrans-SRN : ∀{v a b} -> {μ η : Path BaseModeHom-SRN a b} -> (x y : BaseModeTrans-SRN v μ η) → isDecidable (x ≡ y)
  decide-≡-BaseModeTrans-SRN (send U) (send .U) = yes refl
  decide-≡-BaseModeTrans-SRN (recv U) (recv .U) = yes refl
  decide-≡-BaseModeTrans-SRN (narrow ϕ) (narrow ψ) with force-≡ ϕ ψ
  ... | refl = yes refl

  instance
    hasDecidableEquality:BaseModeTrans-SRN : ∀{v a b} -> {μ η : Path BaseModeHom-SRN a b} -> hasDecidableEquality (BaseModeTrans-SRN v μ η)
    hasDecidableEquality:BaseModeTrans-SRN = record { _≟_ = decide-≡-BaseModeTrans-SRN }

  β-decide-≡-BaseModeTrans-SRN : ∀{v a b} -> {μ η : Path BaseModeHom-SRN a b} -> {x : BaseModeTrans-SRN v μ η} -> decide-≡-BaseModeTrans-SRN x x ≡ yes refl
  β-decide-≡-BaseModeTrans-SRN = {!!}

  {-# REWRITE β-decide-≡-BaseModeTrans-SRN #-}

  show-BaseModeHom : ∀{a b} -> BaseModeHom-SRN a b → Text
  show-BaseModeHom (`＠` U) = "＠"
  show-BaseModeHom `[]` = "◻"

  instance
    hasShow:BaseModeHom-SRN : ∀{a b} -> hasShow (BaseModeHom-SRN a b)
    hasShow:BaseModeHom-SRN = record { show = show-BaseModeHom }


  ------------------------------------------------------------------------
  -- The generating graph of the Kami Mode Theory (SRN)
  --
  -- It consists of exactly the modes, modalities and mode transformations
  -- described above.
  SRN : 2Graph _
  SRN = record
    { Point = Mode-SRN
    ; Edge = BaseModeHom-SRN
    ; Face = BaseModeTrans-SRN
    }



