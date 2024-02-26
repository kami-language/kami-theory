-- Original file by Joakim Öhman et al.
-- See here: https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda
--
-- Original license:
-- ```
--   Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--   Permission is hereby granted, free of charge, to any person obtaining a copy
--   of this software and associated documentation files (the "Software"), to deal
--   in the Software without restriction, including without limitation the rights
--   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
--   copies of the Software, and to permit persons to whom the Software is
--   furnished to do so, subject to the following conditions:

--   The above copyright notice and this permission notice shall be included in all
--   copies or substantial portions of the Software.

--   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
--   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
--   SOFTWARE.
-- ```

-- {-# OPTIONS --without-K #-}

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Definition where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
-- open import Agora.Order.Preorder
-- open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition




-- module _ {P : 𝒰 _} {{_ : Preorder (ℓ₀ , ℓ₀ , ℓ₀) on P}} {{_ : hasDecidableEquality P}} where
module Judgements (P : ModeSystem 𝑖) where
-- {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasFiniteMeets ′ P ′ }} where
       -- {{_ : hasDecidableEquality P}} where

  -- open DUN.KamiUntyped P hiding (_∷_)
  _★_ = _◆-Modality_


  infixl 30 _∙_
  infix 30 Πⱼ_▹_
  infix 30 Σⱼ_▹_
  -- infix 30 ⟦_⟧ⱼ_▹_

  data TermTransitions n : 𝒰 𝑖 where
    incl : Term P n -> TermTransitions n
    * : TermTransitions n


  open Term

  private variable
    -- n m : Nat
    k l o q r : Mode P
    μs : Modality P
    ωs : Modality P
    ηs : Modality P
    μ : ModeHom P k l
    η : ModeHom P o q
    -- ω : ModeHom P q r
    ττ : TermTransitions n
    τ σ : Term P n -- Transitions
    ξ ξ₀ ξ₁ : Term P n -- Transitions
    Γ  : Con (Entry P) n
    A B : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Entry P n
    t s : Term P n
    f g : Term P n
    G : Term P (1+ n)
    x : Fin n
    -- U V R : P


  wk1-Entry : Entry P n -> Entry P (suc n)
  wk1-Entry (A // μ) = wk1 A // μ

  -- Well-typed variables
  data _∶_∈_ : (x : Fin n) (E : Entry P n) (Γ : Con (Entry P) n) → 𝒰 𝑖 where
    zero :                       x0 ∶ wk1-Entry E ∈ (Γ ∙ E)
    suc  : (h : x ∶ E ∈ Γ) → (x +1) ∶ wk1-Entry E ∈ (Γ ∙ F)





  data ⊢Ctx_ : Con (Entry P) n → 𝒰 𝑖
  data _⊢Tr_ (Γ : Con (Entry P) n) : Term P n -> 𝒰 𝑖
  data _⊢Sort_ (Γ : Con (Entry P) n) : Term P n -> 𝒰 𝑖
  data _⊢Entry_ (Γ : Con (Entry P) n) : Entry P n -> 𝒰 𝑖
  data _⊢[_]_∶_ (Γ : Con (Entry P) n) : TermTransitions n -> Term P n → Entry P n → 𝒰 𝑖

  _⊢_∶_ : (Γ : Con (Entry P) n) -> Term P n -> Entry P n -> 𝒰 𝑖
  _⊢_∶_ Γ t A = Γ ⊢[ incl end ] t ∶ A


  -- id-◯ : ModeHom P ◯ ◯
  -- id-◯ = id

  data _⊢Tr_＝_ (Γ : Con (Entry P) n) : Term P n -> Term P n -> 𝒰 𝑖 where
    tt : Γ ⊢Tr ξ₀ ＝ ξ₁


  -- Well-formed context
  data ⊢Ctx_ where
    ε   : ⊢Ctx ε
    _∙_ : ⊢Ctx Γ
        → Γ ⊢Entry E
        → ⊢Ctx Γ ∙ E

  data _⊢Tr_ Γ where
    -- trⱼ : Γ ⊢Entry A / μ
    --       -> (ξ : Transition μs ηs vis)
    --       -> Γ ⊢Tr A / μ ⇒ ηs
    -- _≫ⱼ_ : Γ ⊢Tr ξ₀ -> Γ ⊢Tr ξ₁ -> Γ ⊢Tr (ξ₀ ≫ ξ₁)


  -- Well-formed type
  data _⊢Sort_ Γ where
    UUⱼ    : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Sort UU
    NNⱼ    : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Sort NN
    -- Vecⱼ   : Γ ⊢Sort A → Γ ⊢ t ∶ NN / ▲ U → Γ ⊢Sort Vec A t
    Emptyⱼ : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Sort Empty
    Unitⱼ  : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Sort Unit

    Πⱼ_▹_  : Γ ⊢Entry (A / μ) → Γ ∙ E ⊢Sort B → Γ ⊢Sort Π (A / μ) ▹ B
    Σⱼ_▹_  : Γ ⊢Entry (A / μ) → Γ ∙ F ⊢Sort G → Γ ⊢Sort Σ (A / μ) ▹ G
    -- univ   : Γ ⊢Sort A ∶ UU
    --       → Γ ⊢Sort A

    -- Kami types
    -- Locⱼ : (U : P) -> Γ ⊢Sort L -> Γ ⊢Sort (L ＠ U)

    -- Well-formed entry
  data _⊢Entry_ Γ where
    NNⱼ    : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (NN / μ)
    -- Emptyⱼ : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (Empty / ▲ U)
    -- Unitⱼ  : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (Unit / ▲ U)
    -- Leafⱼ : ∀{l} -> {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (gen (leaf l) [] / ▲ U) -- leafs are NN, Unit, Empty

    -- UUⱼ    : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (UU / ▲ U)

    Vecⱼ   : Γ ⊢Entry (A / μ) → Γ ⊢ t ∶ NN / μ  → Γ ⊢Entry (Vec A t / μ)

    Πⱼ_▹_  : Γ ⊢Entry (A / μ)
              → Γ ∙ (A / μ) ⊢Entry (B / η)
              → Γ ⊢Entry ((Π (A / μ) ▹ B) / η)

    -- Σⱼ_▹_  : ∀{q} -> Γ ⊢Entry (A / ωs)
    --         → Γ ∙ (A / ωs) ⊢Entry (B / ωs)
    --         → Γ ⊢Entry ((Σ (A / ωs) ▹ B) / ωs)

    -------------------
    -- Kami universes

    -- Univ-⇄ⱼ : Γ ⊢ X ∶ Univ-⇄ R A / ◯
    --           → Γ ⊢Entry (X / ⇄ R A)

    -------------------
    -- Kami types (global ◯)
    -- Locⱼ : (U : P) -> Γ ⊢Entry (L / ▲ U) -> Γ ⊢Entry ((L ＠ U) / ◯)
    -- Comⱼ : Γ ⊢Entry (A / ◯) -> Γ ⊢Entry (Com R A / ◯)

    -------------------
    -- Kami modality system
    Modalⱼ : Γ ⊢Entry (A / (η ◆ μ)) -> Γ ⊢Entry Modal A η / μ

    -- narrowⱼ : (ϕ : U ≤ V)
    --            -> Γ ⊢Entry X / `＠` U ⨾ μs
    --            -> Γ ⊢Entry X / `＠` V ⨾ μs

    -------------------
    -- Mode transformations (transitions)

    Trⱼ : ∀{m} -> Γ ⊢Entry Tr / id {m = m}
    -- []▹ⱼ : Γ ⊢Entry [ τ ]▹ A / μ




  -- Well-formed term of a type
  data _⊢[_]_∶_ Γ where

    -------------------
    -- Standard modality intro and "elim"

    modⱼ : Γ ⊢[ ττ ] t ∶ X / (η ◆ μ) -> Γ ⊢[ ττ ] mod t ∶ Modal X η / μ

    letunmodⱼ : Γ ⊢[ incl τ ] t ∶ Modal X η / μ
              -> Γ ∙ (X / (η ◆ μ)) ⊢[ incl σ ] s ∶ Y / μ
              -> Γ ⊢[ incl (τ ≫ (σ [ unmod t ])) ] letunmod η t s ∶ Y [ unmod t ] / μ

    unmodⱼ : Γ ⊢[ * ] t ∶ Modal X η / μ -> Γ ⊢[ * ] unmod t ∶ X / (η ◆ μ)



    -------------------
    -- Transformations between modehoms (transitions)

    trⱼ : ∀{m} -> Γ ⊢Entry A / μ
          → (ξ : ModalityTrans P vis (_ ↝ _ ∋ μ) (_ ↝ _ ∋ η))
          → Γ ⊢ A / ((_ ↝ _ ∋ μ)) ⇒ ((_ ↝ _ ∋ η)) ∶ Tr / id {m = m}

    _≫ⱼ_ : Γ ⊢ ξ₀ ∶ Tr / μ
         → Γ ⊢ ξ₁ ∶ Tr / μ
         → Γ ⊢ (ξ₀ ≫ ξ₁) ∶ Tr / μ

    endⱼ : ∀{m} -> Γ ⊢ end ∶ Tr / id {m = m}

    transformⱼ : ∀ (ζ : ModalityTrans P vis (_ ↝ _ ∋ μ) (_ ↝ _ ∋ η))
                 -> Γ ⊢[ incl τ ] t ∶ A / μ
                 -> Γ ⊢[ incl (τ ≫ A / ((_ ↝ _ ∋ μ)) ⇒ ((_ ↝ _ ∋ η))) ] transform (incl ζ) t ∶ A / η

    castⱼ : Γ ⊢Tr τ ＝ σ
            -> Γ ⊢[ incl τ ] t ∶ A / μ
            -> Γ ⊢[ incl σ ] t ∶ A / μ


    -- trⱼ : Γ ⊢Entry A / μ
    --     → ModeTrans μs ηs vis
    --     → Γ ∙ (A / ηs) ⊢ B ∶ Tr // ◯ ↝ ◯ ∋ id
    --     →  Γ ⊢ A / μ ⇒ ηs > B ∶ Tr // ◯ ↝ ◯ ∋ id
    -- execⱼ : Γ ⊢[ σ ] t ∶ [ τ ]▹ A / μ
    --          → Γ ⊢[ σ ≫ τ ] exec t ∶ (A / μ)
    -- prepareⱼ : Γ ⊢[ σ ] t ∶ A / μ
    --          → Γ ⊢ prepare t ∶ [ σ ]▹ A / μ

    -- let-inⱼ : Γ ⊢ t ∶ A / ηs
    --         → Γ ∙ (A / ηs) ⊢[ σ ] s ∶ B / ωs
    --         → Γ ⊢[ σ [ t ] ] let-in t s ∶ B [ t ] / ωs

    -- let-trⱼ : Γ ⊢ t ∶ A / μ
    --         → Γ ∙ (A / ηs) ⊢[ σ ] s ∶ B / ωs
    --         → Γ ⊢[ A / μ ⇒ ηs > σ ] let-tr t s ∶ B [ t ] / ωs


    -------------------
    -- Interactions between modalities
    -- sendⱼ : ∀ U -> Γ ⊢ t ∶ X / μ -> Γ ⊢ send t ∶ X / `＠` U ⨾ `[]` ⨾ μs
    -- recvⱼ : ∀ U -> Γ ⊢ t ∶ X / `[]` ⨾ `＠` U ⨾ μs -> Γ ⊢ recv t ∶ X / μ


    -------------------
    -- normal terms

    -- Vars allow mode transformations between modalities
    var       : ∀ {A x}
              -> {{ΓP : isTrue (⊢Ctx Γ)}}
              → x ∶ (A // (k ↝ l ∋ μ)) ∈ Γ
              → (ζ : ModalityTrans P all (_ ↝ _ ∋ μ) (_ ↝ _ ∋ η))
              → Γ ⊢ (Term.var x (incl ζ)) ∶ A // (k ↝ l ∋ η)


    lamⱼ      : ∀ {t}
              → Γ ⊢Entry (A / (η ◆ μ))
              → Γ ∙ (A / (η ◆ μ)) ⊢[ incl τ ] t ∶ B / μ
              → Γ ⊢ lam η t ∶ Π (A / η) ▹[ τ ] B / μ

    _∘ⱼ_      : ∀ {g a}
              → Γ ⊢[ incl τ ] g ∶ Π (A / η) ▹[ ξ ] B / μ
              → Γ ⊢[ incl σ ] a ∶ A / (η ◆ μ)
              → Γ ⊢[ incl ((ξ₀ ∥ ξ₁) ≫ (ξ [ untransform-Term a ])) ] g ∘ a ∶ B [ untransform-Term a ] / μ


{-
    prodⱼ     : ∀ A B -> ∀{t u}
              → {{_ : isTrue (Γ ⊢Entry (A / μ))}}
              → {{_ : isTrue (Γ ∙ (A / μ) ⊢Sort B)}}
              → Γ ⊢ t ∶ A / μ
              → Γ ⊢ u ∶ G [ t ] / μ
              → Γ ⊢ t ,ₜ u ∶ Σ F ▹ G / μ

    fstⱼ      : ∀ A B -> ∀{t}
              → {{_ : isTrue (Γ ⊢Entry (A / μ))}}
              → {{_ : isTrue (Γ ∙ (A / μ) ⊢Sort B)}}
              → Γ ⊢ t ∶ Σ (A / μ) ▹ B / μ
              → Γ ⊢ fstₜ t ∶ A / μ

    sndⱼ      : ∀ A B -> ∀{t}
              → {{_ : isTrue (Γ ⊢Entry (A / μ))}}
              → {{_ : isTrue (Γ ∙ (A / μ) ⊢Sort B)}}
              → Γ ⊢ t ∶ Σ (A / μ) ▹ B / μ
              → Γ ⊢ sndₜ t ∶ B [ fstₜ t ] / μ
              -}

    --------------------------------------------------
    -- Booleans
    falseⱼ     : {{ΓP : isTrue (⊢Ctx Γ)}}
               → Γ ⊢ falseₜ ∶ BB  / μ

    trueⱼ     : {{ΓP : isTrue (⊢Ctx Γ)}}
               → Γ ⊢ trueₜ ∶ BB  / μ

    boolrecⱼ   : ∀ {G} -> {μ : ModeHom P k l}
              → Γ ∙ (BB / μ) ⊢Entry G / μ
              → Γ       ⊢ f ∶ G [ falseₜ ]  / μ
              → Γ       ⊢ t ∶ G [ trueₜ ]  / μ
              → Γ       ⊢ b ∶ BB  / μ
              → Γ       ⊢ natrec k G f t b ∶ G [ b ]  / μ

    --------------------------------------------------
    -- Natural numbers

    zeroⱼ     :  {{ΓP : isTrue (⊢Ctx Γ)}}
              → Γ ⊢ zeroₜ ∶ NN  / μ

    sucⱼ      : ∀ {n}
              → Γ ⊢      n ∶ NN  / μ
              → Γ ⊢ sucₜ n ∶ NN  / μ

    natrecⱼ   : ∀ {G s z n} -> {μ : ModeHom P k l}
              → Γ ∙ (NN / μ) ⊢Entry G / μ
              → Γ       ⊢ z ∶ G [ zeroₜ ]  / μ
              → Γ       ⊢ s ∶ Π (NN / μ) ▹ ((G / μ) ▹▹ G [ sucₜ (var x0 id) ]↑)  / μ
              → Γ       ⊢ n ∶ NN  / μ
              → Γ       ⊢ natrec k G z s n ∶ G [ n ]  / μ

{-
    nilⱼ      : ∀ {A}
              → Γ ⊢ nilₜ ∶ Vec A zeroₜ  / μ
 
    consⱼ     : ∀ {A v vs n}
              → Γ ⊢         v ∶ A  / μ
              → Γ ⊢        vs ∶ Vec A n  / μ
              → Γ ⊢ consₜ v vs ∶ Vec A (sucₜ n)  / μ

    vecrecⱼ   : ∀ {G A z s l vs}
              → Γ ∙ (NN / `＠` (U ∧ V) ⨾ μs) ∙ (Vec (wk1 A) (var x0) / `＠` U ⨾ μs) ⊢Entry G / `＠` V ⨾ ηs -- note l and vs don't have to be in the same location as G
              → Γ ⊢ z ∶ (G [ nilₜ ] [ zeroₜ ]) / `＠` V ⨾ ηs -- we have a proof of G for zero vector
              → Γ ⊢ s ∶ Π (NN / `＠` (U ∧ V) ⨾ μs) ▹ -- for all vector lengths l
                            Π (Vec (wk1 A) (var x0) / `＠` U ⨾ μs) ▹ -- for all vectors vs of that length
                            Π (wk1 (wk1 A) / `＠` U ⨾ μs) ▹ -- for all v : A
                              (((wk1 G) / `＠` V ⨾ ηs) ▹▹ -- given a proof of G we get a proof of G [ l+1 ] [ v :: vs ]
                                -- (wk1 (wk1 (wk1 G)) [ consₜ (var (x0 +1)) (var ((x0 +1) +1 +1)) ])) / `＠` V ⨾ ηs -- vector is innermost A var v appended to Vec var vs
                                --                    [ sucₜ (var (((x0 +1) +1 ))) ] -- length is suc of outermost NN var l
                                (wk1 (wk1 (wk1 G)) [ sucₜ (var (((x0 +1) +1 ) +1)) ] -- length is suc of outermost NN var l
                                                   [ consₜ (var (x0 +1)) (var ((x0 +1) +1)) ])) / `＠` V ⨾ ηs -- vector is innermost A var v appended to Vec var vs
              → Γ ⊢ l ∶ NN / `＠` (U ∧ V) ⨾ μs
              → Γ ⊢ vs ∶ Vec A l / `＠` U ⨾ μs
              → Γ ⊢ vecrec G z s l vs ∶ G [ wk1 vs ] [ l ]  / `＠` V ⨾ ηs


{-
    -------------------
    -- Interaction of Communication with global types

    -- If we have a communication value, we can create a global value
    -- by packing the comm-type and the comm-value into a "tuple" with `com`
    -- comⱼ : Γ ⊢Entry (X / ⇄ R A)
    --         -> Γ ⊢ t ∶ X / ⇄ R A
    --         -> Γ ⊢ com X t ∶ Com R A / ◯

    -- -- we can project to the first (type) component
    -- comtypeⱼ : Γ ⊢Entry (A / ◯)
    --         -> Γ ⊢ a ∶ Com R A / ◯
    --         -> Γ ⊢ comtype a ∶ Univ-⇄ R A / ◯

    -- -- we can project to the second (value) component
    -- comvalⱼ : Γ ⊢Entry (A / ◯)
    --         -> Γ ⊢ a ∶ Com R A / ◯
    --         -> Γ ⊢ comval a ∶ comtype a / ⇄ R A

-}
    -------------------
    -- Communication

    -- We end a communication by giving a value of the
    -- required type
    -- endⱼ : Γ ⊢ a ∶ A / ◯ -> Γ ⊢ end a ∶ End / ⇄ R A

{-
    -- If we have:
    --  - `a`: a com of type `X` which gives us a value of type A
    --  - `b`: a com of type `Y` which (assuming a : A) gives us B,
    -- we can compose these communications to get one of type `X ≫ Y`
    -- _>ⱼ_ : Γ ⊢ a ∶ X / ⇄ R A
    --       -> Γ ∙ (A / ◯) ⊢ b ∶ Y / ⇄ R (wk1 B)
    --       -> Γ ⊢ (a > b) ∶ X ≫ Y / ⇄ R B

    -- -- If we have a value (a ∶ A ＠ U) then we can share it so it is
    -- -- available at V.
    -- shareⱼ : Γ ⊢Entry (A / ▲ V)
    --       -> Γ ⊢ a ∶ (A ＠ U) / ◯
    --       -> (ϕ : V ≤ U)
    --       -> Γ ⊢ share a ∶ Share A U V / ⇄ R (A ＠ V)
-}

    -------------------
    -- Location


    -- If we have a value of a local type `A` (i.e. with ▲ U annotation), we can view it
    -- as `(A ＠ U)` which is a global type (with ◯ annotation). Note that if U is not subset
    -- of the currently implemented locations, it is not allowed to give a term here. Instead,
    -- the `locskip` constructor has to be used
    -- locⱼ : (U ≤ W)
    --      -> Γ ⊢ t ∶ A / ▲ U
    --      -> Γ ⊢ loc U t ∶ (A ＠ U) / ◯

    -- locskipⱼ : ¬(U ≤ W)
    --      -> Γ ⊢ loc U star ∶ (A ＠ U) / ◯

{-
    -- If the currently to be implemented type (`A ＠ U`) is not part of the currently to
    -- be implemented locations (U ≰ W), then we can trivially give a term by using `locskip`.
    -- locskipⱼ : ¬(U ≤ W) -> Γ ⊢ locskip ∶ (A ＠ U) / ◯

    -- If we have a global term `A ＠ U` we can view it as a local term.
    -- unlocⱼ : Γ ⊢ t ∶ (A ＠ U) / ◯ -> Γ ⊢ unloc t ∶ A / ▲ U

    -------------------
    -- Generic

    -- Πⱼ_▹_     : ∀ {F G}
    --           → Γ     ⊢ F ∶ U
    --           → Γ ∙ F ⊢ G ∶ U
    --           → Γ     ⊢ Π F ▹ G ∶ U
    -- Σⱼ_▹_     : ∀ {F G}
    --           → Γ     ⊢ F ∶ U
    --           → Γ ∙ F ⊢ G ∶ U
    --           → Γ     ⊢ Σ F ▹ G ∶ U
    ℕⱼ        : {{_ : isTrue (⊢Ctx Γ)}} → Γ ⊢ NN ∶ UU / μ
    Vecⱼ      : ∀ {F l}
              → Γ ⊢ F ∶ UU / μ
              → Γ ⊢ l ∶ NN / μ
              → Γ ⊢ Vec F l ∶ UU / μ

    -- Emptyⱼ    : ⊢ Γ → Γ ⊢Sort Empty ∶ U
    -- Unitⱼ     : ⊢ Γ → Γ ⊢Sort Unit ∶ U
-}

{-

      -- zeroⱼ     : ⊢ Γ
      --           → Γ ⊢Sort zero ∶ ℕ
      -- sucⱼ      : ∀ {n}
      --           → Γ ⊢Sort       n ∶ ℕ
      --           → Γ ⊢Sort suc n ∶ ℕ
      -- natrecⱼ   : ∀ {G s z n}
      --           → Γ ∙ ℕ ⊢ G
      --           → Γ       ⊢ z ∶ G [ zero ]
      --           → Γ       ⊢ s ∶ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
      --           → Γ       ⊢ n ∶ ℕ
      --           → Γ       ⊢ natrec G z s n ∶ G [ n ]

      -- Emptyrecⱼ : ∀ {A e}
      --           → Γ ⊢Sort A → Γ ⊢Sort e ∶ Empty → Γ ⊢Sort Emptyrec A e ∶ A

      -- starⱼ     : ⊢ Γ → Γ ⊢Sort star ∶ Unit

      -- conv      : ∀ {t A B}
      --           → Γ ⊢Sort t ∶ A
      --           → Γ ⊢Sort A ≡ B
      --           → Γ ⊢Sort t ∶ B

    -- Type equality
    -- data _⊢_≡_ (Γ : Con (Entry P) n) : Term P n → Term P n → Set where
    --   univ   : ∀ {A B}
    --         → Γ ⊢Sort A ≡ B ∶ U
    --         → Γ ⊢Sort A ≡ B
    --   refl   : ∀ {A}
    --         → Γ ⊢Sort A
    --         → Γ ⊢Sort A ≡ A
    --   sym    : ∀ {A B}
    --         → Γ ⊢Sort A ≡ B
    --         → Γ ⊢Sort B ≡ A
    --   trans  : ∀ {A B C}
    --         → Γ ⊢Sort A ≡ B
    --         → Γ ⊢Sort B ≡ C
    --         → Γ ⊢Sort A ≡ C
    --   Π-cong : ∀ {F H G E}
    --         → Γ     ⊢ F
    --         → Γ     ⊢ F ≡ H
    --         → Γ ∙ F ⊢ G ≡ E
    --         → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E
    --   Σ-cong : ∀ {F H G E}
    --         → Γ     ⊢ F
    --         → Γ     ⊢ F ≡ H
    --         → Γ ∙ F ⊢ G ≡ E
    --         → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E

    -- Term equality
  --   data _⊢_≡_∶_ (Γ : Con (Entry P) n) : Term P n → Term P n → Term P n → Set where
  --     refl          : ∀ {t A}
  --                   → Γ ⊢Sort t ∶ A
  --                   → Γ ⊢Sort t ≡ t ∶ A
  --     sym           : ∀ {t u A}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort u ≡ t ∶ A
  --     trans         : ∀ {t u r A}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort u ≡ r ∶ A
  --                   → Γ ⊢Sort t ≡ r ∶ A
  --     conv          : ∀ {A B t u}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort A ≡ B
  --                   → Γ ⊢Sort t ≡ u ∶ B
  --     Π-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ≡ H       ∶ U
  --                   → Γ ∙ F ⊢ G ≡ E       ∶ U
  --                   → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E ∶ U
  --     Σ-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ≡ H       ∶ U
  --                   → Γ ∙ F ⊢ G ≡ E       ∶ U
  --                   → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E ∶ U
  --     app-cong      : ∀ {a b f g F G}
  --                   → Γ ⊢Sort f ≡ g ∶ Π F ▹ G
  --                   → Γ ⊢Sort a ≡ b ∶ F
  --                   → Γ ⊢Sort f ∘ a ≡ g ∘ b ∶ G [ a ]
  --     β-red         : ∀ {a t F G}
  --                   → Γ     ⊢ F
  --                   → Γ ∙ F ⊢ t ∶ G
  --                   → Γ     ⊢ a ∶ F
  --                   → Γ     ⊢ (lam t) ∘ a ≡ t [ a ] ∶ G [ a ]
  --     η-eq          : ∀ {f g F G}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ f ∶ Π F ▹ G
  --                   → Γ     ⊢ g ∶ Π F ▹ G
  --                   → Γ ∙ F ⊢ wk1 f ∘ var x0 ≡ wk1 g ∘ var x0 ∶ G
  --                   → Γ     ⊢ f ≡ g ∶ Π F ▹ G
  --     fst-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ≡ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort fst t ≡ fst t' ∶ F
  --     snd-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ≡ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort snd t ≡ snd t' ∶ G [ fst t ]
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

  -- -- Term reduction
  -- data _⊢_⇒_∶_ (Γ : Con (Entry P) n) : Term P n → Term P n → Term P n → Set where
  --   conv           : ∀ {A B t u}
  --                 → Γ ⊢Sort t ⇒ u ∶ A
  --                 → Γ ⊢Sort A ≡ B
  --                 → Γ ⊢Sort t ⇒ u ∶ B
  --   app-subst      : ∀ {A B t u a}
  --                 → Γ ⊢Sort t ⇒ u ∶ Π A ▹ B
  --                 → Γ ⊢Sort a ∶ A
  --                 → Γ ⊢Sort t ∘ a ⇒ u ∘ a ∶ B [ a ]
  --   β-red          : ∀ {A B a t}
  --                 → Γ     ⊢ A
  --                 → Γ ∙ A ⊢ t ∶ B
  --                 → Γ     ⊢ a ∶ A
  --                 → Γ     ⊢ (lam t) ∘ a ⇒ t [ a ] ∶ B [ a ]
  --   fst-subst      : ∀ {t t' F G}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ⇒ t' ∶ Σ F ▹ G
  --                 → Γ ⊢Sort fst t ⇒ fst t' ∶ F
  --   snd-subst      : ∀ {t t' F G}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ⇒ t' ∶ Σ F ▹ G
  --                 → Γ ⊢Sort snd t ⇒ snd t' ∶ G [ fst t ]
  --   Σ-β₁           : ∀ {F G t u}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ∶ F
  --                 → Γ ⊢Sort u ∶ G [ t ]
  --                 → Γ ⊢Sort fst (prod t u) ⇒ t ∶ F
  --   Σ-β₂           : ∀ {F G t u}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ∶ F
  --                 → Γ ⊢Sort u ∶ G [ t ]
  --                 -- TODO(WN): Prove that 𝔍 ∶ G [ t ] is admissible
  --                 → Γ ⊢Sort snd (prod t u) ⇒ u ∶ G [ fst (prod t u) ]
  --   natrec-subst   : ∀ {z s n n′ F}
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ n ⇒ n′ ∶ ℕ
  --                 → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∶ F [ n ]
  --   natrec-zero    : ∀ {z s F}
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ natrec F z s zero ⇒ z ∶ F [ zero ]
  --   natrec-suc     : ∀ {n z s F}
  --                 → Γ     ⊢ n ∶ ℕ
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∶ F [ suc n ]
  --   Emptyrec-subst : ∀ {n n′ A}
  --                 → Γ ⊢Sort A
  --                 → Γ     ⊢ n ⇒ n′ ∶ Empty
  --                 → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∶ A

  -- Type reduction
  data _⊢_⇒_ (Γ : Con (Entry P) n) : Term P n → Term P n → Set where
    univ : ∀ {A B}
        → Γ ⊢Sort A ⇒ B ∶ U
        → Γ ⊢Sort A ⇒ B

  -- Term reduction closure
  data _⊢_⇒*_∶_ (Γ : Con (Entry P) n) : Term P n → Term P n → Term P n → Set where
    id  : ∀ {A t}
        → Γ ⊢Sort t ∶ A
        → Γ ⊢Sort t ⇒* t ∶ A
    _⇨_ : ∀ {A t t′ u}
        → Γ ⊢Sort t  ⇒  t′ ∶ A
        → Γ ⊢Sort t′ ⇒* u  ∶ A
        → Γ ⊢Sort t  ⇒* u  ∶ A

  -- Type reduction closure
  data _⊢_⇒*_ (Γ : Con (Entry P) n) : Term P n → Term P n → Set where
    id  : ∀ {A}
        → Γ ⊢Sort A
        → Γ ⊢Sort A ⇒* A
    _⇨_ : ∀ {A A′ B}
        → Γ ⊢Sort A  ⇒  A′
        → Γ ⊢Sort A′ ⇒* B
        → Γ ⊢Sort A  ⇒* B

  -- Type reduction to whnf
  _⊢_↘_ : (Γ : Con (Entry P) n) → Term P n → Term P n → Set
  Γ ⊢Sort A ↘ B = Γ ⊢Sort A ⇒* B × Whnf B

  -- Term reduction to whnf
  _⊢_↘_∶_ : (Γ : Con (Entry P) n) → Term P n → Term P n → Term P n → Set
  Γ ⊢Sort t ↘ u ∶ A = Γ ⊢Sort t ⇒* u ∶ A × Whnf u

  -- Type equality with well-formed types
  _⊢_:≡:_ : (Γ : Con (Entry P) n) → Term P n → Term P n → Set
  Γ ⊢Sort A :≡: B = Γ ⊢Sort A × Γ ⊢Sort B × (Γ ⊢Sort A ≡ B)

  -- Term equality with well-formed terms
  _⊢_:≡:_∶_ : (Γ : Con (Entry P) n) → Term P n → Term P n → Term P n → Set
  Γ ⊢Sort t :≡: u ∶ A = (Γ ⊢Sort t ∶ A) × (Γ ⊢Sort u ∶ A) × (Γ ⊢Sort t ≡ u ∶ A)

  -- Type reduction closure with well-formed types
  record _⊢_:⇒*:_ (Γ : Con (Entry P) n) (A B : Term P n) : Set where
    constructor [_,_,_]
    field
      ⊢A : Γ ⊢Sort A
      ⊢B : Γ ⊢Sort B
      D  : Γ ⊢Sort A ⇒* B

  open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

  -- Term reduction closure with well-formed terms
  record _⊢_:⇒*:_∶_ (Γ : Con (Entry P) n) (t u A : Term P n) : Set where
    constructor [_,_,_]
    field
      ⊢t : Γ ⊢Sort t ∶ A
      ⊢u : Γ ⊢Sort u ∶ A
      d  : Γ ⊢Sort t ⇒* u ∶ A

  open _⊢_:⇒*:_∶_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

  -- Well-formed substitutions.
  data _⊢ˢ_∶_ (Δ : Con Term m) : (σ : Subst m n) (Γ : Con (Entry P) n) → Set where
    id  : ∀ {σ} → Δ ⊢ˢ σ ∶ ε
    _,_ : ∀ {A σ}
        → Δ ⊢ˢ tail σ ∶ Γ
        → Δ ⊢  head σ ∶ subst (tail σ) A
        → Δ ⊢ˢ σ      ∶ Γ ∙ A

  -- Conversion of well-formed substitutions.
  data _⊢ˢ_≡_∶_ (Δ : Con Term m) : (σ σ′ : Subst m n) (Γ : Con (Entry P) n) → Set where
    id  : ∀ {σ σ′} → Δ ⊢ˢ σ ≡ σ′ ∶ ε
    _,_ : ∀ {A σ σ′}
        → Δ ⊢ˢ tail σ ≡ tail σ′ ∶ Γ
        → Δ ⊢  head σ ≡ head σ′ ∶ subst (tail σ) A
        → Δ ⊢ˢ      σ ≡ σ′      ∶ Γ ∙ A

  -- Note that we cannot use the well-formed substitutions.
  -- For that, we need to prove the fundamental theorem for substitutions.

  ⟦_⟧ⱼ_▹_ : (W : BindingType) → ∀ {F G}
      → Γ     ⊢ F
      → Γ ∙ F ⊢ G
      → Γ     ⊢ ⟦ W ⟧ F ▹ G
  ⟦ BΠ ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
  ⟦ BΣ ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

  ⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
      → Γ     ⊢ F ∶ U
      → Γ ∙ F ⊢ G ∶ U
      → Γ     ⊢ ⟦ W ⟧ F ▹ G ∶ U
  ⟦ BΠ ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
  ⟦ BΣ ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

  -}

-}
