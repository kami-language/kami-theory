
module KamiTheory.Main.Dependent.Typed.Instances where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const)
open import Agora.Order.Preorder

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product


module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

  private variable
    -- n m : Nat
    p q : Term P n
    t u : Term P n
    Γ  : Con (Term P) n
    A B : Term P n

  private
    _>>=_ = bind-Maybe

  {-# TERMINATING #-}
  derive-Entry : ∀ (Γ : Con (Term P) n) E -> Maybe (Γ ⊢Entry E)
  derive-Ctx : ∀ (Γ : Con (Term P) n) -> Maybe (⊢ Γ)

  derive-Entry Γ (UU / ▲ U)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (NN / ▲ U)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (Empty / ▲ U) = map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (Unit / ▲ U)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (L ＠ U / ◯)  = map-Maybe (Locⱼ U) (derive-Entry Γ (L / ▲ U))
  derive-Entry Γ (Com R A / ◯)  = map-Maybe Comⱼ (derive-Entry Γ (A / ◯))
  derive-Entry Γ (Σ (A / ML p) ▹ B / ML q) with p ≟ q
  ... | left x = nothing
  ... | just refl-≡ = do
    A' <- derive-Entry Γ (A / ML p)
    B' <- derive-Entry (Γ ∙ (A / ML q)) (B / ML q)
    just (Σⱼ A' ▹ B')
  derive-Entry Γ (Π (A / ML p) ▹ B / ML q) = do
    A' <- derive-Entry Γ (A / ML p)
    B' <- derive-Entry (Γ ∙ (A / ML p)) (B / ML q)
    just (Πⱼ A' ▹ B')
  derive-Entry Γ E = nothing


  derive-Ctx ε = just ε
  derive-Ctx (Γ ∙ E) = do
    E' <- derive-Entry Γ E
    Γ' <- derive-Ctx Γ
    just (Γ' ∙ E')

  derive-Sort : ∀ (Γ : Con (Term P) n) E -> Maybe (Γ ⊢Sort E)
  derive-Sort Γ (UU)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (NN)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Empty) = map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Unit)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (L ＠ U)  = map-Maybe (Locⱼ U) (derive-Sort Γ (L))
  derive-Sort Γ E = nothing


  infer-Var : ∀ Γ -> (t : Fin n) -> ∑ λ (E : Term P n) -> (t ∶ E ∈ Γ)
  infer-Var (Γ ∙ x) x0 = _ , zero
  infer-Var (Γ ∙ x) (_+1 t) with (E , Ep) <- infer-Var Γ t = _ , suc Ep

  derive-Var : ∀ Γ -> (t : Fin n) -> (A p : Term P n) -> Maybe (t ∶ A / p ∈ Γ)
  derive-Var Γ t A p with infer-Var Γ t
  ... | ((B / q) , Ep) with A ≟ B | p ≟ q
  ... | no x | Y = nothing
  ... | yes x | no x₁ = nothing
  ... | yes refl-≡ | yes refl-≡ = yes Ep
  derive-Var Γ t A p | _ = nothing

  derive-Term : ∀ Γ -> (t A p : Term P n) -> Maybe (Γ ⊢ t ∶ A / p)
  derive-Term Γ (var x) A p = do
    A' <- (derive-Var Γ x A p)
    G' <- derive-Ctx Γ
    just (var {{ΓP = because G'}} A')
  derive-Term Γ _ A p = nothing

  instance
    isDerivable:Con : isDerivable (⊢ Γ)
    isDerivable:Con = record { derive = derive-Ctx _ }

  instance
    isDerivable:Entry : isDerivable (Γ ⊢Entry A)
    isDerivable:Entry = record { derive = derive-Entry _ _ }

  instance
    isDerivable:Sort : isDerivable (Γ ⊢Sort A)
    isDerivable:Sort = record { derive = derive-Sort _ _ }

  instance
    isDerivable:Term : isDerivable (Γ ⊢ t ∶ A / p)
    isDerivable:Term = record { derive = derive-Term _ _ _ _ }


