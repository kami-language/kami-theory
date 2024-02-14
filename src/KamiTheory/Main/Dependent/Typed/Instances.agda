
module KamiTheory.Main.Dependent.Typed.Instances where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product


-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

module Typecheck (P' : Preorder (ℓ₀ , ℓ₀ , ℓ₀)) {{_ : hasDecidableEquality ⟨ P' ⟩}} where
-- {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

  private
    P : 𝒰 _
    P = ⟨ P' ⟩

  private variable
    -- n m : Nat
    k l : Mode
    μs : Modality P k l
    p q : Term P n
    t u : Term P n
    Γ  : Con (Entry P) n
    A B : Term P n
    E F : Entry P n
    W : P

  private
    _>>=_ = bind-Maybe

  {-# TERMINATING #-}
  derive-Entry : ∀ (Γ : Con (Entry P) n) E -> Maybe (W ∣ Γ ⊢Entry E)
  derive-Ctx : ∀ (Γ : Con (Entry P) n) -> Maybe (W ⊢Ctx Γ)
  derive-Term : ∀ Γ -> (t A : Term P n) → (p : Modality P k l) -> Maybe (W ∣ Γ ⊢ t ∶ A / p)

  --derive-Entry Γ (UU / μs)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (NN / μs)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (Vec A t / μs) = do
    A′ <- derive-Entry Γ (A / μs )
    t′ <- derive-Term Γ t NN (μs)
    just (Vecⱼ A′ t′)

  --derive-Entry Γ (Empty / μs) = map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)
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
  derive-Sort : ∀ (Γ : Con (Term P) n) E -> Maybe (W ∣ Γ ⊢Sort E)
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

  derive-Var : ∀ Γ -> (t : Fin n) -> (A : Term P n) → (p : Modality P k l) -> Maybe (t ∶ A / p ∈ Γ)
  derive-Var Γ t A p with infer-Var Γ t
  ... | (E , Ep) with E ≟ (A / p)
  ... | no p = nothing
  ... | yes refl-≡ = yes Ep
  derive-Var Γ t A p | _ = nothing

  derive-Term Γ (var x) A p = do
    A' <- (derive-Var Γ x A p)
    G' <- derive-Ctx Γ
    just (var {{ΓP = because G'}} A')
  derive-Term Γ _ A p = nothing

  instance
    isDerivable:Con : isDerivable (W ⊢Ctx Γ)
    isDerivable:Con = record { derive = derive-Ctx _ }

  instance
    isDerivable:Entry : isDerivable (W ∣ Γ ⊢Entry E)
    isDerivable:Entry = record { derive = derive-Entry _ _ }
{-
  instance
    isDerivable:Sort : isDerivable (W ∣ Γ ⊢Sort A)
    isDerivable:Sort = record { derive = derive-Sort _ _ }
-}
  instance
    isDerivable:Term : isDerivable (W ∣ Γ ⊢ t ∶ A / μs)
    isDerivable:Term = record { derive = derive-Term _ _ _ _ }


