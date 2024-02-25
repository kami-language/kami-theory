
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Instances where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Modality.Definition

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product


-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

-- module Typecheck (P' : Preorder (ℓ₀ , ℓ₀ , ℓ₀)) {{_ : hasDecidableEquality ⟨ P' ⟩}} {{_ : isDecidablePreorder ′ ⟨ P' ⟩ ′}} {{_ : hasFiniteMeets ′ ⟨ P' ⟩ ′}} where
-- {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

module Typecheck (P : ModeSystem 𝑖) where

  open Judgements P

  -- private
  --   P : 𝒰 _
  --   P = ⟨ graph P' ⟩

  private variable
    -- n m : Nat
    k l : Mode P
    μs : ModeHom P k l
    p q : Term P n
    t u : Term P n
    Γ  : Con (Entry P) n
    A B : Term P n
    E F : Entry P n
    -- W : P

  private
    _>>=_ = bind-Maybe

  {-# TERMINATING #-}
  derive-Entry : ∀ (Γ : Con (Entry P) n) E -> Maybe (Γ ⊢Entry E)
  derive-Ctx : ∀ (Γ : Con (Entry P) n) -> Maybe (⊢Ctx Γ)
  derive-Term-Sort↓,Mod↓ : ∀ Γ -> (t A : Term P n) → (p : SomeModeHom P) -> Maybe (Γ ⊢ t ∶ A // p)

  --derive-Entry Γ (UU / μs)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (NN / μs)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (Vec A t // μs) = do
    A′ <- derive-Entry Γ (A // μs )
    t′ <- derive-Term-Sort↓,Mod↓ Γ t NN (μs)
    just (Vecⱼ A′ t′)

  derive-Entry Γ (gen (main 𝓀-Modal) ([] ⦊ term A ∷ [] ⦊ modality (l ↝ k0 ∋ μ) ∷ []) // k1 ↝ m ∋ μs) with k0 ≟ k1
  ... | no p = nothing
  ... | yes refl-≡ = do
          A' <- derive-Entry Γ (A / μ ◆ μs)
          just (Modalⱼ A')

  derive-Entry Γ (Tr // ◯ ↝ ◯ ∋ id) = yes Trⱼ
  -- map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)


  --derive-Entry Γ (Unit / μs)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  --derive-Entry Γ (L ＠ U / ◯)  = map-Maybe (Locⱼ U) (derive-Entry Γ (L / μs))
  --derive-Entry Γ (Com R A / ◯)  = map-Maybe Comⱼ (derive-Entry Γ (A / ◯))
  {- derive-Entry Γ (Σ (A / ML p) ▹ B / ML q) with p ≟ q
  ... | left x = nothing
  ... | just refl-≡ = do
    A' <- derive-Entry Γ (A / ML p)
    B' <- derive-Entry (Γ ∙ (A / ML q)) (B / ML q)
    just (Σⱼ A' ▹ B')
  derive-Entry Γ (Π (A / ML p) ▹ B / ML q) = do
    A' <- derive-Entry Γ (A / ML p)
    B' <- derive-Entry (Γ ∙ (A / ML p)) (B / ML q)
    just (Πⱼ A' ▹ B')
    -}
  derive-Entry Γ E = nothing


  derive-Ctx ε = just ε
  derive-Ctx (Γ ∙ E) = do
    E' <- derive-Entry Γ E
    Γ' <- derive-Ctx Γ
    just (Γ' ∙ E')
{-
  derive-Sort : ∀ (Γ : Con (Term P) n) E -> Maybe (Γ ⊢Sort E)
  derive-Sort Γ (UU)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (NN)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Empty) = map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Unit)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  -- derive-Sort Γ (L ＠ U)  = map-Maybe (Locⱼ U) (derive-Sort Γ (L))
  derive-Sort Γ E = nothing
-}

  infer-Var : ∀ Γ -> (t : Fin n) -> ∑ λ (E : Entry P n) -> (t ∶ E ∈ Γ)
  infer-Var (Γ ∙ x) x0 = _ , zero
  infer-Var (Γ ∙ x) (_+1 t) with (E , Ep) <- infer-Var Γ t = _ , suc Ep

  derive-Var-Sort↓,Mod↓ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → (p : SomeModeHom P) -> Maybe (t ∶ A // p ∈ Γ)
  derive-Var-Sort↓,Mod↓ Γ t A p with infer-Var Γ t
  ... | (E , Ep) with E ≟ (A // p)
  ... | no p = nothing
  ... | yes refl-≡ = yes Ep

  derive-Var-Sort↓,Mod↑ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → Maybe (∑ λ μs -> t ∶ A // μs ∈ Γ)
  derive-Var-Sort↓,Mod↑ Γ t A with infer-Var Γ t
  ... | ((A' // μs) , Ap) with A ≟ A'
  ... | no p = nothing
  ... | yes refl-≡ = yes (μs , Ap)


  ------------------------------------------------------------------------
  -- Terms (infering Sort, infering Mod)

  -- derive-Term-Sort↑,Mod↑ : ∀ Γ -> (t : Term P n) -> Maybe (∑ λ (E : Entry P n) -> Γ ⊢ t ∶ E)
  -- derive-Term-Sort↑,Mod↑ Γ (var x) with ((A / p) , Ep) <- infer-Var Γ x = do
  --   G' <- derive-Ctx Γ
  --   just ((A / p) , var {{ΓP = because G'}} Ep)

  -- derive-Term-Sort↑,Mod↑ Γ t = nothing

  ------------------------------------------------------------------------
  -- Terms (checking Sort, infering Mod)
  -- derive-Term-Sort↓,Mod↑ : ∀ Γ -> (t A : Term P n) -> Maybe (∑ λ (μs : Modality P) -> Γ ⊢ t ∶ (A // μs))
  -- derive-Term-Sort↓,Mod↑ Γ (var x) A with derive-Var-Sort↓,Mod↑ Γ x A
  -- ... | nothing = nothing
  -- ... | yes (μs , Ap) = do
  --   G' <- derive-Ctx Γ
  --   yes (μs , var {{ΓP = because G'}} Ap)

  -- derive-Term-Sort↓,Mod↑ Γ t A = nothing

  ------------------------------------------------------------------------
  -- Terms (checking Sort, checking Mod)

  -------------------
  -- modalities
  derive-Term-Sort↓,Mod↓ Γ (mod t) (Modal A q) p = nothing

  -- modality interactions
  -- derive-Term-Sort↓,Mod↓ Γ (narrow t) A (k ↝ l ∋ (`＠` V ⨾ μs)) with derive-Term-Sort↓,Mod↑ Γ t A
  -- ... | nothing = nothing
  -- ... | yes (m ↝ m ∋ id , t') = nothing
  -- ... | yes (.◯ ↝ n ∋ `[]` ⨾ ηs , t') = nothing
  -- ... | yes (.▲ ↝ n ∋ `＠` U ⨾ ηs , t') with n ≟ l
  -- ... | no p = nothing
  -- ... | yes refl with μs ≟ ηs
  -- ... | no p = nothing
  -- ... | yes refl with decide-≤ U V
  -- ... | no p = nothing
  -- ... | yes ϕ = yes (narrowⱼ ϕ t')

  -------------------
  -- standard MLTT
  derive-Term-Sort↓,Mod↓ Γ (var x (incl (μ ⇒ η ∋ ξ))) A η' with (derive-Var-Sort↓,Mod↑ Γ x A)
  ... | nothing = nothing
  ... | yes (μ' , A') with (_ ↝ _ ∋ μ) ≟ μ'
  ... | no p = nothing
  ... | yes refl with (_ ↝ _ ∋ η) ≟ η'
  ... | no p = nothing
  ... | yes refl = do
    G' <- derive-Ctx Γ
    just (var {{ΓP = because G'}} A' (_ ⇒ _ ∋ ξ))


  derive-Term-Sort↓,Mod↓ Γ (var x id) A μ = nothing
  derive-Term-Sort↓,Mod↓ Γ (var x fail) A μ = nothing

  -- derive-Term-Sort↓,Mod↓ Γ (lam t) (Π (A / p) ▹ B) q = do
  --   A' <- derive-Entry Γ (A / p)
  --   t' <- derive-Term-Sort↓,Mod↓ (Γ ∙ (A / p)) t B q
  --   just (lamⱼ A' t')
  -- derive-Term-Sort↓,Mod↓ Γ (t ∘ s) B p = nothing -- for checking an application we need `infer-Term`
  derive-Term-Sort↓,Mod↓ Γ _ A p = nothing

  instance
    isDerivable:Con : isDerivable (⊢Ctx Γ)
    isDerivable:Con = record { derive = derive-Ctx _ }

  instance
    isDerivable:Entry : isDerivable (Γ ⊢Entry E)
    isDerivable:Entry = record { derive = derive-Entry _ _ }
{-
  instance
    isDerivable:Sort : isDerivable (Γ ⊢Sort A)
    isDerivable:Sort = record { derive = derive-Sort _ _ }
-}
  instance
    isDerivable:Term : isDerivable (Γ ⊢ t ∶ A / μs)
    isDerivable:Term = record { derive = derive-Term-Sort↓,Mod↓ _ _ _ _ }

  -- instance
  --   isDerivable:ModeTrans : ∀{m n v} -> {μs ηs : ModeHom P m n} -> isDerivable (ModeTrans μs ηs v)
  --   isDerivable:ModeTrans = record { derive = derive-ModeTrans _ _ }


