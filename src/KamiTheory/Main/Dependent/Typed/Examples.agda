

module KamiTheory.Main.Dependent.Typed.Examples where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const)
open import Agora.Order.Preorder
open import Data.Fin.Base

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances

-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product



module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

  private variable
    -- n m : Nat
    p q : Term P n
    t u : Term P n
    Γ  : Con (Term P) n
    A B : Term P n
    U V : P

  _⊢_/_≔_ : (Γ : Con (Term P) n) -> Term P n → Term P n -> Term P n → Set
  Γ ⊢ A / p ≔ t = Γ ⊢ t ∶ A / p

  εε : Con (Term P) zero
  εε = ε

  T0 : εε ⊢Sort NN
  T0 = NNⱼ

  t0 : εε ⊢ (NN / ▲ U) ▹▹ (NN ×× NN) / ▲ U
          ≔ lam (var zero ,ₜ var zero)

  t0 = lamⱼ NNⱼ (prodⱼ NN NN (var zero) (var zero))

  t1 : ε ⊢ _ ∶ ((((NN ＠ U) / ◯) ×× (NN ＠ U)) / ◯) ▹▹ (NN ×× NN) / ▲ U
  t1 = lamⱼ (Σⱼ Locⱼ _ NNⱼ ▹ Locⱼ _ NNⱼ) (prodⱼ NN NN (unlocⱼ (fstⱼ (NN ＠ _) (NN ＠ _) (var zero))) ((unlocⱼ (sndⱼ (NN ＠ _) (NN ＠ _) (var zero)))))

