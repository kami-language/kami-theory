

module KamiTheory.Main.Dependent.Typed.Examples where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances

open import KamiTheory.Data.Open.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Order.StrictOrder.Base

-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product




-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

module Examples where
  P : 𝒰 _
  P = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 3))

  uu : P
  uu = (⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  vv : P
  vv = (⦗ # 1 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  ww : P
  ww = (⦗ # 2 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  all = uu ∨ vv ∨ ww

  _⟶_ = _▹▹_

  private variable
    -- n m : Nat
    p q : Term P n
    t u : Term P n
    Γ  : Con (Term P) n
    A B C : Term P n
    U V W R : P

  _∣_⊢_/_≔_ : (W : P) -> (Γ : Con (Term P) n) -> Term P n → Term P n -> Term P n → Set
  W ∣ Γ ⊢ A / p ≔ t = W ∣ Γ ⊢ t ∶ A / p




  εε : Con (Term P) zero
  εε = ε

  T0 : all ∣ εε ⊢Sort NN
  T0 = NNⱼ

  t0 : all ∣ εε ⊢ (NN / ▲ U) ▹▹ (NN ×× NN) / ▲ U
          ≔ lam (var zero ,ₜ var zero)

  t0 = lamⱼ NNⱼ (prodⱼ NN NN (var zero) (var zero))

  t1 : all ∣ ε ⊢ _ ∶ ((((NN ＠ U) / ◯) ×× (NN ＠ U)) / ◯) ▹▹ (NN ×× NN) / ▲ U
  t1 = lamⱼ (Σⱼ Locⱼ _ NNⱼ ▹ Locⱼ _ NNⱼ) (prodⱼ NN NN (unlocⱼ (fstⱼ (NN ＠ _) (NN ＠ _) (var zero))) ((unlocⱼ (sndⱼ (NN ＠ _) (NN ＠ _) (var zero)))))

  t2 : uu ∣ ε ⊢ _ ∶ NN ＠ vv / ◯
  t2 = locskipⱼ λ { (incl (take (incl (drop ())) ∷ a))}


  {-
  ---------------------------------------------
  -- communication

  -- We can send a value
  c0 : all ∣ ε ⊢ _ ∶ ((NN ＠ uu) / ◯ ⟶ Com all (NN ＠ (uu ∧ vv))) / ◯
  c0 = lamⱼ (Locⱼ _ NNⱼ) (comⱼ (Shareⱼ uu _ π₀-∧ NNⱼ) (shareⱼ NNⱼ (var zero) π₀-∧))

  -- We can join two communications
  c1 : all ∣ ε ⊢ _ ∶
       (
         (( (NN ＠ uu) / ◯ ⟶ Com R (NN ＠ vv)) / ◯)
      ⟶ (((((NN ＠ vv) / ◯ ⟶ Com R (NN ＠ ww)) / ◯)
      ⟶  ((NN ＠ uu) / ◯ ⟶ Com R (NN ＠ ww))))
       ) / ◯
  c1 = lamⱼ (Πⱼ Locⱼ _ NNⱼ ▹ Comⱼ (Locⱼ _ NNⱼ))
       (lamⱼ ((Πⱼ Locⱼ _ NNⱼ ▹ Comⱼ (Locⱼ _ NNⱼ)))
       (lamⱼ (Locⱼ _ NNⱼ)
      (comⱼ (Univ-Comⱼ (comtypeⱼ (Locⱼ _ NNⱼ) (var (suc (suc zero)) ∘ⱼ var zero))
        ≫ⱼ Univ-Comⱼ ((comtypeⱼ (Locⱼ _ NNⱼ) (var (suc (suc zero)) ∘ⱼ var zero ))))
      (comvalⱼ (Locⱼ _ NNⱼ) ((var (suc (suc zero)) ∘ⱼ var zero))
        >ⱼ comvalⱼ (Locⱼ _ NNⱼ) ((var (suc (suc zero)) ∘ⱼ var zero))) )))
  -}


