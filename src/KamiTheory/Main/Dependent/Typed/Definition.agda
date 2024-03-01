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




record RModeHom (P : ModeSystem 𝑖) (k : Mode P) : 𝒰 𝑖 where
  constructor incl
  field {cod} : Mode P
  field hom : ModeHom P k cod

open RModeHom public

module Judgements (P : ModeSystem 𝑖) where



  infixl 30 _∙_
  infix 30 Πⱼ_▹_
  -- infix 30 Σⱼ_▹_
  infixl 24 _∘ⱼ_
  -- infix 30 ⟦_⟧ⱼ_▹_



  open Term

  private variable
    k l o q r mm nn : Mode P

  data Restriction : (Mode P) -> ℕ -> 𝒰 𝑖 where
    [] : Restriction k 0
    _∷_ : ModeHom P k l -> Restriction l n -> Restriction k (suc n)

  getRest : Restriction k n -> ∑ λ l -> ModeHom P k l
  getRest [] = _ , id
  getRest (x ∷ xs) = _ , x ◆ getRest xs .snd

  -- Restriction : (Mode P) -> ℕ -> 𝒰 _
  -- Restriction k n = StdVec (RModeHom P k) n

  private variable
    μs : Modality P
    ωs : Modality P
    ηs : Modality P
    μ : ModeHom P k l
    ν : ModeHom P o q
    η : ModeHom P o q
    ω : ModeHom P mm nn
    ρ : ModeHom P mm nn
    τ σ : Term P n -- Transitions
    ξ ξ₀ ξ₁ : Term P n -- Transitions
    Γ  : Con (Entry P) n
    A B : Term P n
    C D : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Entry P n
    t s : Term P n
    f g : Term P n
    G : Term P (1+ n)
    x : Fin n
    M : Restriction k n
    N : Restriction k n
    -- U V R : P


  wk1-Entry : Entry P n -> Entry P (suc n)
  wk1-Entry (A // μ) = wk1 A // μ

  -- Well-typed variables
  data _∶_∈_ : (x : Fin n) (E : Entry P n) (Γ : Con (Entry P) n) → 𝒰 𝑖 where
    zero :                       x0 ∶ wk1-Entry E ∈ (Γ ∙ E)
    suc  : (h : x ∶ E ∈ Γ) → (x +1) ∶ wk1-Entry E ∈ (Γ ∙ F)

  data _∶[_]_⇒_∈_∥_ : (x : Fin n) (ρ : ModeHom P mm nn) (E : Entry P n) (η : ModeHom P k l) (Γ : Con (Entry P) n) (M : Restriction k n) → 𝒰 𝑖 where
    zero :          x0 ∶[ getRest M .snd ] wk1-Entry E ⇒ η ∈ (Γ ∙ E) ∥ (η ∷ M)
    suc  : (h : x ∶[ ρ ] E ⇒ η ∈ Γ ∥ M) → (x +1) ∶[ ρ ] wk1-Entry E ⇒ (μ ◆ η) ∈ (Γ ∙ F) ∥ (μ ∷ M)


  _↳_ : ModeHom P l k -> Restriction k n -> Restriction l n
  μ ↳ [] = []
  μ ↳ (x ∷ M) = μ ◆ x ∷ M


  postulate
    comp-↳ : (ν ◆ μ ↳ M) ≡ ν ↳ μ ↳ M
    id-↳ : (id ↳ M) ≡ M

  {-# REWRITE comp-↳ #-}
  {-# REWRITE id-↳ #-}


  -- map-Vec (λ η -> incl (μ ◆ hom η))

  data Target (n : ℕ) : 𝒰 𝑖 where
    _∥_ : Term P n -> Restriction k n -> Target n

  infix 21 _∥_

  infixr 22 _↳_

  pattern _∥[_]_ T k M = _∥_ {k = k} T M



  data ⊢Ctx_∥_ : Con (Entry P) n → Restriction k n → 𝒰 𝑖

  data _⊢Entry_ (Γ : Con (Entry P) n) : Target n -> 𝒰 𝑖

  data _⊢_∶_ (Γ : Con (Entry P) n) : Term P n → Target n → 𝒰 𝑖
  data _⊢Entry_＝_∥_ (Γ : Con (Entry P) n) : Term P n → Term P n -> Restriction k n → 𝒰 𝑖
  data _⊢_＝_∶_ (Γ : Con (Entry P) n) : Term P n → Term P n → Target n → 𝒰 𝑖



  -- Well-formed context
  data ⊢Ctx_∥_ where
    ε   : ⊢Ctx_∥_ {k = k} ε []
    _∙_ : ∀{M : Restriction o n}
        -> ⊢Ctx Γ ∥ M
        -> ∀{η : ModeHom P q o}
        -> ∀{μ : ModeHom P l o}
        → Γ ⊢Entry A ∥ μ ↳ M
        → ⊢Ctx Γ ∙ (A / μ) ∥ (η ∷ M)






    -- Well-formed entry
  data _⊢Entry_ Γ where
    NNⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Entry (NN ∥ M)

    BBⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Entry (BB ∥ M)
    -- Emptyⱼ : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (Empty / ▲ U)
    -- Unitⱼ  : {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (Unit / ▲ U)
    -- Leafⱼ : ∀{l} -> {{ΓP : isTrue (⊢Ctx Γ)}} → Γ ⊢Entry (gen (leaf l) [] / ▲ U) -- leafs are NN, Unit, Empty

    UUⱼ    : {{ΓP : isTrue (⊢Ctx Γ ∥ M)}} → Γ ⊢Entry (UU ∥ M)

    Vecⱼ   : Γ ⊢Entry (A ∥ M) → Γ ⊢ t ∶ NN ∥ M  → Γ ⊢Entry (Vec A t ∥ M)

    Πⱼ_▹_  : Γ ⊢Entry (A ∥ μ ↳ M)
              → Γ ∙ (A / μ) ⊢Entry (B ∥ (id ∷ M))
              → Γ ⊢Entry ((Π A / μ ▹ B) ∥ M)

    -- Σⱼ_▹_  : {μ : ModeHom P k l}
    --         → Γ ⊢Entry (A / μ)
    --         → Γ ∙ (A / μ) ⊢Entry (B / μ)
    --         → Γ ⊢Entry ((Σ A // incl (k ↝ k ∋ id) ▹ B) / μ)

    -------------------
    -- Kami universes

    Univⱼ : Γ ⊢ X ∶ UU ∥ M
              → Γ ⊢Entry (X ∥ M)

    -------------------
    -- Kami modality system
    Modalⱼ : Γ ⊢Entry (A ∥ (η ↳ M)) -> Γ ⊢Entry ⟨ A ∣ η ⟩ ∥ M






  -- Well-formed term of a type
  data _⊢_∶_ Γ where

{-
    -------------------
    -- Types as terms of UU
    NNⱼ    : Γ ⊢ NN ∶ UU / μ
    BBⱼ    : Γ ⊢ BB ∶ UU / μ

    UUⱼ    : Γ ⊢ UU ∶ UU / μ

    Vecⱼ   : Γ ⊢ A ∶ UU / μ → Γ ⊢ t ∶ NN / μ  → Γ ⊢ Vec A t ∶ UU / μ

    Πⱼ_▹_  : Γ ⊢ A ∶ UU / μ ◆ η
              → Γ ∙ (A / μ ◆ η) ⊢ B ∶ UU / η
              → Γ ⊢ (Π A / μ ▹ B) ∶ UU / η

    Σⱼ_▹_  : {μ : ModeHom P k l}
            → Γ ⊢ A ∶ UU / μ
            → Γ ∙ (A / μ) ⊢ B ∶ UU / μ
            → Γ ⊢ (Σ A // incl (k ↝ k ∋ id) ▹ B) ∶ UU / μ

    Modalⱼ : Γ ⊢ A ∶ UU / (η ◆ μ) -> Γ ⊢ ⟨ A ∣ η ⟩ ∶ UU / μ

-}

    -------------------
    -- Standard modality intro and "elim"

    modⱼ : Γ ⊢ t ∶ X ∥ (η ↳ M) -> Γ ⊢ mod[ η ] t ∶ ⟨ X ∣ η ⟩ ∥ M


    letunmodⱼ[_]_into_by_ :
                 ∀ (μ : ModeHom P k l)
              -> Γ ⊢ t ∶ ⟨ X ∣ η ⟩ ∥ μ ↳ M
              -> Γ ∙ (⟨ X ∣ η ⟩ / μ) ⊢Entry Y ∥ (id ∷ M)
              -> Γ ∙ (X / (η ◆ μ)) ⊢ s ∶ (Y [ mod[ μ ] (var x0 id) ]↑) ∥ (id ∷ M)
              -> Γ ⊢ letunmod[ μ ] t into Y by s ∶ (Y [ t ]) ∥ M

    -- letunmodⱼ[_]_into_by_ :
    --              ∀ (μ : ModeHom P k l)
    --           -> Γ ⊢ t ∶ ⟨ X ∣ η ⟩ / μ ◆ ω
    --           -> Γ ∙ (⟨ X ∣ η ⟩ / μ ◆ ω) ⊢Entry Y / ω
    --           -> Γ ∙ (X / (η ◆ μ ◆ ω)) ⊢ s ∶ Y [ mod[ μ ] (var x0 id) ]↑ / ω
    --           -> Γ ⊢ letunmod[ μ ] t into Y by s ∶ Y [ t ] / ω



{-
    -------------------
    -- Transformations between modehoms (transitions)


    transformⱼ : ∀ (ζ : ModalityTrans P vis (_ ↝ _ ∋ μ) (_ ↝ _ ∋ η))
                 -> Γ ⊢ t ∶ A / μ
                 -> Γ ⊢ transform (incl ζ) t ∶ A / η


    -------------------
    -- normal terms
    -}

    -- Vars allow mode transformations between modalities
    var       : ∀ {A x}
--               -> {{ΓP : isTrue (⊢Ctx Γ)}}
              → x ∶[ ρ ] (A // (k ↝ l ∋ μ)) ⇒ η ∈ Γ ∥ M
              -- → (ζ : ModalityTrans P all (_ ↝ _ ∋ μ) (_ ↝ _ ∋ η))
              → (ζ : ModeTrans* P all (μ ◆ ρ) (η ◆ ρ))
              → Γ ⊢ (Term.var x (incl (_ ⇒ _ ∋ ζ))) ∶ A ^[ _ ⇒ _ ∋ (ζ) ] ∥ M
              -- → Γ ⊢ (Term.var x (incl (_ ⇒ _ ∋ ζ))) ∶ A ^[ _ ⇒ _ ∋ (ζ ↶-ModeTrans* ρ) ] ∥ M



    lamⱼ_↦_      : ∀ {t}
              → Γ ⊢Entry (A ∥ η ↳ M)
              → Γ ∙ (A / η) ⊢ t ∶ B ∥ (id ∷ M)
              → Γ ⊢ lam↦ t ∶ (Π A / η ▹ B) ∥ M

    _∘ⱼ_      : ∀ {g a}
              -- → Γ ⊢ g ∶ (Π A / (η ◆ μ) ▹ B) / μ
              -- → Γ ⊢ a ∶ A / (η ◆ μ)
              → Γ ⊢ g ∶ (Π A / (η) ▹ B) ∥ M
              → Γ ⊢ a ∶ A ∥ (η ↳ M)
              → Γ ⊢ g ∘[ η ] a ∶ B [ untransform-Term a ] ∥ M

{-

    introⱼΣ_▹_by_,_  : ∀ {A B} -> ∀{t u}
              -> {μ : ModeHom P k l}
              → (Γ ⊢Entry (A / μ))
              → (Γ ∙ (A / μ) ⊢Entry B / μ)
              → Γ ⊢ t ∶ A / μ
              → Γ ⊢ u ∶ B [ t ] / μ
              → Γ ⊢ t ,, u ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) / μ

    fstⱼ      : ∀ {A B} -> ∀{t}
              -> {μ : ModeHom P k l}
              -- → {{_ : isTrue (Γ ⊢Entry (A / μ))}}
              -- → {{_ : isTrue (Γ ∙ (A / μ) ⊢Sort B)}}
              → Γ ⊢ t ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) / μ
              → Γ ⊢ fstₜ t ∶ A / μ

    sndⱼ      : ∀ {A B} -> ∀{t}
              -> {μ : ModeHom P k l}
              -- → {{_ : isTrue (Γ ⊢Entry (A / μ))}}
              -- → {{_ : isTrue (Γ ∙ (A / μ) ⊢Sort B)}}
              → Γ ⊢ t ∶ (Σ A // incl (k ↝ k ∋ id) ▹ B) / μ
              → Γ ⊢ sndₜ t ∶ B [ fstₜ t ] / μ
              -}


    --------------------------------------------------
    -- Booleans
    falseⱼ     : -- {{ΓP : isTrue (⊢Ctx Γ)}} →
                 Γ ⊢ falseₜ ∶ BB  ∥ M

    trueⱼ     : -- {{ΓP : isTrue (⊢Ctx Γ)}} →
                Γ ⊢ trueₜ ∶ BB  ∥ M

    boolrecⱼ_into_false:_true:_   : ∀ {G}
              → Γ       ⊢ b ∶ BB  ∥ M
              → Γ ∙ (BB // _ ↝ k ∋ id) ⊢Entry G ∥ (_∷_ {k = k} id M)
              → Γ       ⊢ f ∶ G [ falseₜ ]  ∥ M
              → Γ       ⊢ t ∶ G [ trueₜ ]  ∥ M
              → Γ       ⊢ boolrec b into G false: f true: t ∶ G [ b ]  ∥ M

    --------------------------------------------------
    -- Natural numbers

    zeroⱼ     : --  {{ΓP : isTrue (⊢Ctx Γ)}} →
                 Γ ⊢ zeroₜ ∶ NN  ∥ M

    sucⱼ      : ∀ {n}
              → Γ ⊢      n ∶ NN  ∥ M
              → Γ ⊢ sucₜ n ∶ NN  ∥ M

    natrecⱼ_into_zero:_suc:_   : ∀ {G s z n}
              → Γ       ⊢ n ∶ NN  ∥ M
              → Γ ∙ (NN // _ ↝ k ∋ id) ⊢Entry (G ∥[ k ] (id ∷ M))
              → Γ       ⊢ z ∶ G [ zeroₜ ]  ∥ M
              → Γ       ⊢ s ∶ (Π NN // incl (k ↝ _ ∋ id) ▹ (G // incl (k ↝ _ ∋ id) ▹▹ (G [ sucₜ (var x0 id) ]↑)))  ∥ M
              → Γ       ⊢ natrec G z s n ∶ G [ n ]  ∥ M
{-

    conv      : ∀ {t A B}
              → Γ ⊢Entry (A / μ) ＝ (B / μ)
              → Γ ⊢ t ∶ A / μ
              → Γ ⊢ t ∶ B / μ

-}

  pattern letunmodⱼ_into_by_ t G s = letunmodⱼ[ id ] t into G by  s


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

-}







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




  -- Type equality
  data _⊢Entry_＝_∥_ Γ where
    univ   : ∀ {A B}
          → Γ ⊢ A ＝ B ∶ UU ∥ M
          → Γ ⊢Entry A ＝ B ∥ M

    reflₑ   : ∀ {A}
          → Γ ⊢Entry A ∥ M
          → Γ ⊢Entry A ＝ A ∥ M

    symₑ    : ∀ {A B}
          → Γ ⊢Entry A ＝ B ∥ M
          → Γ ⊢Entry B ＝ A ∥ M

    transₑ  : ∀ {A B C}
          → Γ ⊢Entry A ＝ B ∥ M
          → Γ ⊢Entry B ＝ C ∥ M
          → Γ ⊢Entry A ＝ C ∥ M

    Π-cong :
             Γ     ⊢Entry (A ∥ M)
          → Γ     ⊢Entry A ＝ B ∥ M
          → Γ ∙ (A / μ) ⊢Entry C ＝ D ∥ (η ∷ N)
          → Γ     ⊢Entry (Π A / μ ▹ C) ＝ (Π B / μ ▹ D) ∥ N

    Σ-cong :
             Γ     ⊢Entry (A ∥ M)
          → Γ     ⊢Entry A ＝ B ∥ M
          → Γ ∙ (A / μ) ⊢Entry C ＝ D ∥ (η ∷ N)
          → Γ     ⊢Entry (Σ A / μ ▹ C) ＝ (Σ B / μ ▹ D) ∥ N


  -- Term equality
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
                  → Γ     ⊢Entry F ∥ (η ↳ M)
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

{-
{-

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
-}
