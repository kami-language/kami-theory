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

module KamiTheory.Main.Dependent.Typed.Definition where

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
    -- The rules for standard data types such as bools or naturals
    -- are valid under any context restriction `M`. They do require
    -- the context to be well-formed, however.
    NNⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Type (NN ∥ M)
    BBⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Type (BB ∥ M)
    Emptyⱼ : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Type (Empty ∥ M)
    Unitⱼ  : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Type (Unit ∥ M)
    UUⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Type (UU ∥ M)

    -- A vector, having a type parameter, does not require anything
    -- for the context. Otherwise it is again valid under any context restriction.
    Vecⱼ   : Γ ⊢Type (A ∥ M) → Γ ⊢ t ∶ NN ∥ M  → Γ ⊢Type (Vec A t ∥ M)

    -- Sigma types are standard. They do not have any interactions with context
    -- restrictions, and require their first type parameter to be under an
    -- identity modality. This follows MTT, but might change in the future
    -- to allow other modalities as well.
    Σⱼ_▹_  : {M : Restriction k _}
            → Γ ⊢Type (A ∥ M)
            → Γ ∙ (A // (k ↝ k ∋ id)) ⊢Type (B ∥ (id ∷ M))
            → Γ ⊢Type ((Σ A // incl (k ↝ k ∋ id) ▹ B) ∥ M)

    -- Pi types follow MTT: the bound variable is allowed to be under a
    -- non-identity modality `μ`, thus the type has to be well-formed after
    -- additionally restricting the context by `μ`.
    Πⱼ_▹_  : Γ ⊢Type (A ∥ μ ↳ M)
              → Γ ∙ (A / μ) ⊢Type (B ∥ (id ∷ M))
              → Γ ⊢Type ((Π A / μ ▹ B) ∥ M)


    -- Universes: The rule is standard, if a term is of type universe,
    -- we can conclude that it is actually a type.
    Univⱼ : Γ ⊢ X ∶ UU ∥ M → Γ ⊢Type (X ∥ M)

    -- Modal types: Similar with Pi types, a type under modality annotation
    -- has to be well-formed after restricting the context.
    Modalⱼ : Γ ⊢Type (A ∥ (η ↳ M)) -> Γ ⊢Type ⟨ A ∣ η ⟩ ∥ M



  -------------------
  -- Well-formed term of a type
  data _⊢_∶_ Γ where

    -- For every typing rule, there is a similar term rule,
    -- which describes the elements of the universe:
    NNⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢ NN ∶ UU ∥ M
    BBⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢ BB ∶ UU ∥ M
    UUⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢ UU ∶ UU ∥ M
    Vecⱼ   : Γ ⊢ A ∶ UU ∥ M → Γ ⊢ t ∶ NN ∥ M  → Γ ⊢ Vec A t ∶ UU ∥ M
    Πⱼ_▹_  : Γ ⊢ A ∶ UU ∥ μ ↳ M
              → Γ ∙ (A / μ) ⊢ B ∶ UU ∥ (id ∷ M)
              → Γ ⊢ (Π A / μ ▹ B) ∶ UU ∥ M
    Σⱼ_▹_  : {M : Restriction k _}
            → Γ ⊢ A ∶ UU ∥ M
            → Γ ∙ (A // (k ↝ k ∋ id)) ⊢ B ∶ UU ∥ (id ∷ M)
            → Γ ⊢ (Σ A // incl (k ↝ k ∋ id) ▹ B) ∶ UU ∥ M
    Modalⱼ : Γ ⊢ A ∶ UU ∥ (η ↳ M) -> Γ ⊢ ⟨ A ∣ η ⟩ ∶ UU ∥ M


    -- The rules for introducing and eliminating modality types
    -- are the same as in MTT
    --
    -- A type X under modality η can be introduced if X can
    -- be derived in an η-restricted context.
    modⱼ : Γ ⊢ t ∶ X ∥ (η ↳ M) -> Γ ⊢ mod[ η ] t ∶ ⟨ X ∣ η ⟩ ∥ M
    --
    -- The elimination rule is inverse, a modal type can be eliminated
    -- by assuming a value under a modality annotation. Note that
    -- we also support a "framing modality" μ.
    letunmodⱼ[_]_into_by_ :
                 ∀ (μ : ModeHom P k l)
              -> Γ ⊢ t ∶ ⟨ X ∣ η ⟩ ∥ μ ↳ M
              -> Γ ∙ (⟨ X ∣ η ⟩ / μ) ⊢Type Y ∥ (id ∷ M)
              -> Γ ∙ (X / (η ◆ μ)) ⊢ s ∶ (Y [ mod[ μ ] (var x0 id) ]↑) ∥ (id ∷ M)
              -> Γ ⊢ letunmod[ μ ] t into Y by s ∶ (Y [ t ]) ∥ M

    -------------------------
    --  The transition rule
    --
    --
    -------------------------



    -- The variable rule is special, and is the main interaction point between
    -- the system of modalities and the terms of the type theory:
    -- Variables are annotated with mode-transformations, which denote transitions
    -- between different modalities. These transitions commute with all terms,
    -- and thus only have to be recorded at those nodes of the term tree, whose
    -- value is unknown: the variables.
    var       : ∀ {A x}
              -- -> {{ΓP : isTrue (⊢Ctx Γ)}}
              → x ∶ (A // (k ↝ l ∋ μ)) ⇒ η ∈ Γ ∥ M
              → (ζ : ModeTrans* P all (μ) (η))
              → Γ ⊢ (var x (incl (_ ⇒ _ ∋ ζ))) ∶ A ^[ _ ⇒ _ ∋ ζ ] ∥ M


    -- The lambda rule allows to move a variable with modality annotation into
    -- the context.
    lamⱼ_↦_      : ∀ {t}
              → Γ ⊢Type (A ∥ η ↳ M)
              → Γ ∙ (A / η) ⊢ t ∶ B ∥ (id ∷ M)
              → Γ ⊢ lam↦ t ∶ (Π A / η ▹ B) ∥ M

    -- The application rule does the reverse - to apply a function whose variable
    -- is under η, the argument has to be well-formed under η-restriction.
    _∘ⱼ_      : ∀ {g a}
              → Γ ⊢ g ∶ (Π A / η ▹ B) ∥ M
              → Γ ⊢ a ∶ A ∥ (η ↳ M)
              → Γ ⊢ g ∘[ η ] a ∶ B [ untransform-Term a ] ∥ M


    -- Introducing and eliminating sigma types is standard. We allow only
    -- types with identity modality annotation for the bound variable.
    introⱼΣ_▹_by_,_  : ∀ {A B} -> ∀{t u}
              -> {M : Restriction k _}
              → (Γ ⊢Type (A ∥ M))
              → (Γ ∙ (A // (k ↝ k ∋ id)) ⊢Type B ∥ (id ∷ M))
              → Γ ⊢ t ∶ A ∥ M
              → Γ ⊢ u ∶ B [ t ] ∥ M
              → Γ ⊢ t ,, u ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) ∥ M

    fstⱼ      : ∀ {A B} -> ∀{t}
              -> {M : Restriction k _}
              → Γ ⊢ t ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) ∥ M
              → Γ ⊢ fstₜ t ∶ A ∥ M

    sndⱼ      : ∀ {A B} -> ∀{t}
              -> {M : Restriction k _}
              → Γ ⊢ t ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) ∥ M
              → Γ ⊢ sndₜ t ∶ B [ fstₜ t ] ∥ M



    -- Introduction and elimination for booleans, standard.
    falseⱼ     : -- {{ΓP : isTrue (⊢Ctx Γ)}} →
                 Γ ⊢ falseₜ ∶ BB  ∥ M

    trueⱼ     : -- {{ΓP : isTrue (⊢Ctx Γ)}} →
                Γ ⊢ trueₜ ∶ BB  ∥ M

    -- Note that we only allow elimination if the value is
    -- under identity modality.
    boolrecⱼ_into_false:_true:_   : ∀ {G}
              → Γ       ⊢ b ∶ BB  ∥ M
              → Γ ∙ (BB // _ ↝ k ∋ id) ⊢Type G ∥ (_∷_ {k = k} id M)
              → Γ       ⊢ f ∶ G [ falseₜ ]  ∥ M
              → Γ       ⊢ t ∶ G [ trueₜ ]  ∥ M
              → Γ       ⊢ boolrec b into G false: f true: t ∶ G [ b ]  ∥ M

    -- Introduction and elimination for natural numbers, standard.
    zeroⱼ     : --  {{ΓP : isTrue (⊢Ctx Γ)}} →
                 Γ ⊢ zeroₜ ∶ NN  ∥ M

    sucⱼ      : ∀ {n}
              → Γ ⊢      n ∶ NN  ∥ M
              → Γ ⊢ sucₜ n ∶ NN  ∥ M

    natrecⱼ_into_zero:_suc:_   : ∀ {G s z n}
              → Γ       ⊢ n ∶ NN  ∥ M
              → Γ ∙ (NN // _ ↝ k ∋ id) ⊢Type (G ∥[ k ] (id ∷ M))
              → Γ       ⊢ z ∶ G [ zeroₜ ]  ∥ M
              → Γ       ⊢ s ∶ (Π NN // incl (k ↝ _ ∋ id) ▹ (G // incl (k ↝ _ ∋ id) ▹▹ (G [ sucₜ (var x0 id) ]↑)))  ∥ M
              → Γ       ⊢ natrec G z s n ∶ G [ n ]  ∥ M


    -- Introduction and elimination of vectors.
    nilⱼ      : ∀ {A}
              → Γ ⊢ nilₜ ∶ Vec A zeroₜ  ∥ M

    consⱼ     : ∀ {A v vs n}
              → Γ ⊢         v ∶ A  ∥ M
              → Γ ⊢        vs ∶ Vec A n  ∥ M
              → Γ ⊢ consₜ v vs ∶ Vec A (sucₜ n)  ∥ M

    headⱼ     : ∀ {A vs n}
              → Γ ⊢ vs ∶ Vec A (sucₜ n)  ∥ M
              → Γ ⊢ headₜ vs ∶ A  ∥ M

    tailⱼ     : ∀ {A vs n}
              → Γ ⊢ vs ∶ Vec A (sucₜ n)  ∥ M
              → Γ ⊢ tailₜ  vs ∶ Vec A n  ∥ M


    -- The conversion rule: If it can be shown that two types A and B are equal,
    -- then terms of type A can be converted into terms of type B.
    conv      : ∀ {t A B}
              → Γ ⊢Type A ＝ B ∥ M
              → Γ ⊢ t ∶ A ∥ M
              → Γ ⊢ t ∶ B ∥ M


  pattern letunmodⱼ_into_by_ t G s = letunmodⱼ[ id ] t into G by  s



  -- Type equality
  data _⊢Type_＝_∥_ Γ where
    univ   : ∀ {A B}
          → Γ ⊢ A ＝ B ∶ UU ∥ M
          → Γ ⊢Type A ＝ B ∥ M

    reflₑ   : ∀ {A}
          → Γ ⊢Type A ∥ M
          → Γ ⊢Type A ＝ A ∥ M

    symₑ    : ∀ {A B}
          → Γ ⊢Type A ＝ B ∥ M
          → Γ ⊢Type B ＝ A ∥ M

    transₑ  : ∀ {A B C}
          → Γ ⊢Type A ＝ B ∥ M
          → Γ ⊢Type B ＝ C ∥ M
          → Γ ⊢Type A ＝ C ∥ M

    Π-cong :
             Γ     ⊢Type (A ∥ M)
          → Γ     ⊢Type A ＝ B ∥ M
          → Γ ∙ (A / μ) ⊢Type C ＝ D ∥ (η ∷ N)
          → Γ     ⊢Type (Π A / μ ▹ C) ＝ (Π B / μ ▹ D) ∥ N

    Σ-cong :
             Γ     ⊢Type (A ∥ M)
          → Γ     ⊢Type A ＝ B ∥ M
          → Γ ∙ (A / μ) ⊢Type C ＝ D ∥ (η ∷ N)
          → Γ     ⊢Type (Σ A / μ ▹ C) ＝ (Σ B / μ ▹ D) ∥ N


  -- Term equality
  --
  -- NOTE: We currently don't most equalities (except β-reduction) for our examples so we skip stating them.
  -- They would be all very standard.
  data _⊢_＝_∶_ Γ where
    reflₑ          : ∀ {t A}
                  → Γ ⊢ t ∶ A
                  → Γ ⊢ t ＝ t ∶ A


  --     sym           : ∀ {t u A}
  --                   → Γ ⊢Sort t ＝ u ∶ A
  --                   → Γ ⊢Sort u ＝ t ∶ A
  --     trans         : ∀ {t u r A}
  --                   → Γ ⊢Sort t ＝ u ∶ A
  --                   → Γ ⊢Sort u ＝ r ∶ A
  --                   → Γ ⊢Sort t ＝ r ∶ A
  --     conv          : ∀ {A B t u}
  --                   → Γ ⊢Sort t ＝ u ∶ A
  --                   → Γ ⊢Sort A ＝ B
  --                   → Γ ⊢Sort t ＝ u ∶ B
  --     Π-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ＝ H       ∶ U
  --                   → Γ ∙ F ⊢ G ＝ E       ∶ U
  --                   → Γ     ⊢ Π F ▹ G ＝ Π H ▹ E ∶ U
  --     Σ-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ＝ H       ∶ U
  --                   → Γ ∙ F ⊢ G ＝ E       ∶ U
  --                   → Γ     ⊢ Σ F ▹ G ＝ Σ H ▹ E ∶ U
  --     app-cong      : ∀ {a b f g F G}
  --                   → Γ ⊢Sort f ＝ g ∶ Π F ▹ G
  --                   → Γ ⊢Sort a ＝ b ∶ F
  --                   → Γ ⊢Sort f ∘ a ＝ g ∘ b ∶ G [ a ]

    β-red         : ∀ {a t F G}
                  → Γ     ⊢Type F ∥ (η ↳ M)
                  → Γ ∙ (F / η) ⊢ t ∶ G ∥ (id ∷ M)
                  → Γ     ⊢ a ∶ F ∥ (η ↳ M)
                  → Γ     ⊢ (lam↦ t) ∘[ η ] a ＝ t [ a ] ∶ G [ a ] ∥ M

{-
  --     η-eq          : ∀ {f g F G}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ f ∶ Π F ▹ G
  --                   → Γ     ⊢ g ∶ Π F ▹ G
  --                   → Γ ∙ F ⊢ wk1 f ∘ var x0 ＝ wk1 g ∘ var x0 ∶ G
  --                   → Γ     ⊢ f ＝ g ∶ Π F ▹ G
  --     fst-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ＝ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort fst t ＝ fst t' ∶ F
  --     snd-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ＝ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort snd t ＝ snd t' ∶ G [ fst t ]
  --     Σ-β₁          : ∀ {F G t u}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ∶ F
  --                   → Γ ⊢Sort u ∶ G [ t ]
  --                   → Γ ⊢Sort fst (prod t u) ≡ t ∶ F
  --     Σ-β₂          : ∀ {F G t u}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ∶ F
  --                   → Γ ⊢Sort u ∶ G [ t ]
  --                   → Γ ⊢Sort snd (prod t u) ≡ u ∶ G [ fst (prod t u) ]
  --     Σ-η           : ∀ {p r F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort p ∶ Σ F ▹ G
  --                   → Γ ⊢Sort r ∶ Σ F ▹ G
  --                   → Γ ⊢Sort fst p ≡ fst r ∶ F
  --                   → Γ ⊢Sort snd p ≡ snd r ∶ G [ fst p ]
  --                   → Γ ⊢Sort p ≡ r ∶ Σ F ▹ G
  --     suc-cong      : ∀ {m n}
  --                   → Γ ⊢Sort m ≡ n ∶ ℕ
  --                   → Γ ⊢Sort suc m ≡ suc n ∶ ℕ
  --     natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
  --                   → Γ ∙ ℕ ⊢ F ≡ F′
  --                   → Γ     ⊢ z ≡ z′ ∶ F [ zero ]
  --                   → Γ     ⊢ s ≡ s′ ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ n ≡ n′ ∶ ℕ
  --                   → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∶ F [ n ]
  --     natrec-zero   : ∀ {z s F}
  --                   → Γ ∙ ℕ ⊢ F
  --                   → Γ     ⊢ z ∶ F [ zero ]
  --                   → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ natrec F z s zero ≡ z ∶ F [ zero ]
  --     natrec-suc    : ∀ {n z s F}
  --                   → Γ     ⊢ n ∶ ℕ
  --                   → Γ ∙ ℕ ⊢ F
  --                   → Γ     ⊢ z ∶ F [ zero ]
  --                   → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
  --                           ∶ F [ suc n ]
  --     Emptyrec-cong : ∀ {A A' e e'}
  --                   → Γ ⊢Sort A ≡ A'
  --                   → Γ ⊢Sort e ≡ e' ∶ Empty
  --                   → Γ ⊢Sort Emptyrec A e ≡ Emptyrec A' e' ∶ A
  --     η-unit        : ∀ {e e'}
  --                   → Γ ⊢Sort e ∶ Unit
  --                   → Γ ⊢Sort e' ∶ Unit
  --                   → Γ ⊢Sort e ≡ e' ∶ Unit



-}
