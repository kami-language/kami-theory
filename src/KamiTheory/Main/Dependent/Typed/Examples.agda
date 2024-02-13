

module KamiTheory.Main.Dependent.Typed.Examples where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Normal.Definition
open import Agora.Data.Normal.Instance.Setoid
open import Agora.Data.Normal.Instance.Preorder
open import Agora.Data.Normal.Instance.Lattice
open import Agora.Data.Normal.Instance.DecidableEquality

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances

open import KamiTheory.Data.Open.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Order.StrictOrder.Instances.UniqueSortedList
open import KamiTheory.Main.Dependent.Untyped.Definition




module Examples where
  -- instance
  --   hasDecidableEquality:𝔽 : hasDecidableEquality (𝔽 n)
  --   hasDecidableEquality:𝔽 = hasDecidableEquality:byStrictOrder

  -- isStrictOrder:𝒫ᶠⁱⁿ𝔽3 : hasStrictOrder (𝒫ᶠⁱⁿ (𝔽 3))
  -- isStrictOrder:𝒫ᶠⁱⁿ𝔽3 = it

  -- 𝒫𝔽3 : SortableDecidablePreorder _
  -- 𝒫𝔽3 = 𝒫ᶠⁱⁿ (𝔽 3)

  -- QQ : Preorder _
  -- QQ = 𝒪ᶠⁱⁿ (𝒫𝔽3)

  -- {-# INLINE QQ #-}

  PP : Preorder _
  PP = -- QQ
     ′_′ (Normalform ((𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 3))) since isNormalizable:𝒪ᶠⁱⁿ⁻ʷᵏ)) {_} {{isPreorder:𝒩 {{isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ {{isSetoid:𝒫ᶠⁱⁿ}} {{isPreorder:𝒫ᶠⁱⁿ}} {{isDecidablePreorder:≤-𝒫ᶠⁱⁿ}}}}}}



  uu : ⟨ PP ⟩
  uu = (((⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  vv : ⟨ PP ⟩
  vv = (((⦗ # 1 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  ww : ⟨ PP ⟩
  ww = (((⦗ # 2 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  all = uu ∨ vv ∨ ww

  open Typecheck (PP) {{hasDecidableEquality:𝒩}}


  P : 𝒰 _
  P = ⟨ PP ⟩



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

  ttt = derive-Var (εε ∙ (NN / ▲ uu)) zero NN (▲ uu)

  P0 : all ∣ εε ∙ (NN / ▲ uu) ⊢ var zero ∶ NN / ▲ uu
  P0 = proof

  P1 : all ∣ εε ∙ (NN / ▲ uu) ∙ (NN / ▲ vv) ⊢ var (suc zero) ∶ NN / ▲ uu
  P1 = proof

  P2 : all ∣ εε ∙ (NN / ▲ U) ∙ wk (liftn (step id) n0) (NN / ▲ U) ⊢ var (suc zero) ∶ NN [ zeroₜ ] / ▲ U
  P2 = {!proof!}

  P2' : all ∣ ε ∙ (NN / ▲ U) ∙ (NN / ▲ U) ⊢ var (suc zero) ∶ NN / ▲ U
  P2' = {!proof!}


  -- +ₙ : all ∣ εε ⊢ lam (lam (natrec NN (var (suc zero)) _ _)) ∶ (NN / ▲ U) ▹▹ ((NN / ▲ U) ▹▹ NN) / ▲ U
  -- +ₙ {U = U} = lamⱼ NNⱼ (lamⱼ NNⱼ (natrecⱼ {G = NN} NNⱼ proof (lamⱼ NNⱼ (lamⱼ NNⱼ (sucⱼ (var zero)))) (var zero)))

{-
  -- zerov :  all ∣ εε  ⊢ _ ∶ Π (NN / ▲ U) ▹ (Vec NN (var zero)) / ▲ U
  -- zerov = lamⱼ NNⱼ (natrecⱼ                   -- lets call this NNⱼ variable l
  --                     {G = Vec NN (var zero)} -- we want to produce a Vec NN l
  --                     (Vecⱼ NNⱼ (var zero))   -- that is a valid type in (ε ∙ NNⱼ)
  --                     nilⱼ                    -- for l=0 we give empty vector
  --                     (lamⱼ NNⱼ (lamⱼ                     -- now lets call this NNⱼ variable n
  --                                 (Vecⱼ NNⱼ (var zero))   -- and this vec variable vv (it has length n)
  --                                 (consⱼ -- we want to append to vv
  --                                        {!zeroⱼ!} -- we want to append zero (ugh)
  --                                        {!(var zero)!}))) -- we want to append to vv, yes!
  --                     (var zero))             -- we recurse on l



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
-}

