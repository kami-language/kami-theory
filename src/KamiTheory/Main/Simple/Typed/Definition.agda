-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
-- SPDX-FileCopyrightText: 2024 Olivia Röhrig
-- SPDX-FileCopyrightText: 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--
-- SPDX-License-Identifier: MIT
--
----------------------------------------------------------
--
-- Typing rules of the Kami language
--
-- This file contains the typing rules for terms and types. It
-- very closely follows the setup of MTT [1] (pages 108ff.), and differs only in
-- the fact that our representation of terms is *not* intrinsically
-- typed, and the substitution calculus works without typing
-- information - the required data is already part of the untyped
-- terms.
--
-- Apart from that, our representation of modalities is a mixture
-- between the informal and formal versions of MTT: our contexts
-- are merely lists of types with modality annotations, but a separate
-- list of the same size carries the "denominator", respectively
-- the context restriction data.
--
-- The file was originally taken from a project [2] by Joakim Öhman et al.,
-- but the typing rules themselves follow MTT.
--
-- -[1]: http://www.danielgratzer.com/papers/phd-thesis.pdf
-- -[2]: https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda
--
----------------------------------------------------------


{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Simple.Typed.Definition where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)

open import Data.Vec using ([] ; _∷_ ; _++_ ; lookup) renaming (Vec to StdVec ; map to map-Vec)

open import KamiTheory.Basics hiding (typed)
open import KamiTheory.Main.Dependent.Untyped.Definition

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition




module Judgements (P : ModeSystem 𝑖) where



  infixl 30 _∙_
  infix 30 Πⱼ_▹_
  -- infix 30 Σⱼ_▹_
  infixl 24 _∘ⱼ_

  open Term

  private variable
    k l o q r mm nn : Mode P
    μ : ModeHom P k l
    ν : ModeHom P o q
    η : ModeHom P o q
    ω : ModeHom P mm nn
    ρ : ModeHom P mm nn

  ---------------------------------------------
  -- Before we can give the rules of the type theory,
  -- we have to introduce the concept of "restrictions"
  -- for a context, that describe which variables have
  -- been restricted with which modality.
  --
  -- Effectively, it is a list of modalities which matching
  -- domain/codomain of the same length as the context.
  --
  data Restriction : (Mode P) -> ℕ -> 𝒰 𝑖 where
    [] : Restriction k 0
    _∷_ : ModeHom P k l -> Restriction l n -> Restriction k (suc n)

  private variable
    M : Restriction k n
    N : Restriction k n

  -- Given a restriction with domain k, we can precompose
  -- the first modality with a morphism (μ : l → k) to get
  -- a restriction with domain l.
  --
  -- This is the operation denoted by Γ.{μ} in MTT.
  --
  _↳_ : ModeHom P l k -> Restriction k n -> Restriction l n
  μ ↳ [] = []
  μ ↳ (x ∷ M) = μ ◆ x ∷ M

  --
  -- We state rewrite rules for restrictions.
  --
  postulate
    comp-↳ : (ν ◆ μ ↳ M) ≡ ν ↳ μ ↳ M
    id-↳ : (id ↳ M) ≡ M

  {-# REWRITE comp-↳ #-}
  {-# REWRITE id-↳ #-}

  --
  -- We write Γ ⊢ t ∶ A ∥ M to say that t is a
  -- well-formed term in context Γ under a restriction M
  --
  data Target (n : ℕ) : 𝒰 𝑖 where
    _∥_ : Term P n -> Restriction k n -> Target n

  pattern _∥[_]_ T k M = _∥_ {k = k} T M

  infix 21 _∥_
  infixr 22 _↳_


  private variable
    Γ  : Con (Entry P) n
    A B : Term P n
    C D : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Entry P n
    t s : Term P n
    f g : Term P n
    x : Fin n


  wk1-Entry : Entry P n -> Entry P (suc n)
  wk1-Entry (A // μ) = wk1 A // μ

  -- Well-typed variables
  --
  -- When we extract a variable from the context, we need not only
  -- record its type and its modality annotation (in E), but also record the restriction modality (η)
  -- under which it was found.
  --
  data _∶_⇒_∈_∥_ : (x : Fin n) (E : Entry P n) (η : ModeHom P k l) (Γ : Con (Entry P) n) (M : Restriction k n) → 𝒰 𝑖 where
    zero :          x0 ∶ wk1-Entry ((A) / ω) ⇒ η ∈ (Γ ∙ (A / ω)) ∥ (η ∷ M)
    suc  : (h : x ∶ (A / ω) ⇒ η ∈ Γ ∥ M) → (x +1) ∶ wk1-Entry ((A) / ω) ⇒ (μ ◆ η) ∈ (Γ ∙ F) ∥ (μ ∷ M)



  ----------------------------------------------------------
  -- The judgements for contexts, types, terms and equality have to be stated mutual-recursively.
  --
  -- well-formed contexts
  data ⊢Ctx_∥_ : Con (Entry P) n → Restriction k n → 𝒰 𝑖

  -- well-formed types
  data _⊢Type_ (Γ : Con (Entry P) n) : Target n -> 𝒰 𝑖

  -- well-formed terms
  data _⊢_∶_ (Γ : Con (Entry P) n) : Term P n → Target n → 𝒰 𝑖

  -- equality for types
  data _⊢Type_＝_∥_ (Γ : Con (Entry P) n) : Term P n → Term P n -> Restriction k n → 𝒰 𝑖

  -- equality for terms
  data _⊢_＝_∶_ (Γ : Con (Entry P) n) : Term P n → Term P n → Target n → 𝒰 𝑖


  ----------------------------------------------------------
  -- Here come the definitions:

  -------------------
  -- Well-formed context
  --
  data ⊢Ctx_∥_ where

    -- The empty context is well-formed.
    ε   : ⊢Ctx_∥_ {k = k} ε []

    -- The rule for context extension requires that if
    -- the context is to be extended by a type `A` with modality
    -- `μ`, then it has to be well-formed with respect to a
    -- `μ`-restricted context.
    _∙_ : ∀{M : Restriction o n}
        -> ⊢Ctx Γ ∥ M
        -> ∀{η : ModeHom P q o}
        -> ∀{μ : ModeHom P l o}
        → Γ ⊢Type A ∥ μ ↳ M
        → ⊢Ctx Γ ∙ (A / μ) ∥ (η ∷ M)


  -------------------
  -- Well-formed types
  --
  data _⊢Type_ Γ where


