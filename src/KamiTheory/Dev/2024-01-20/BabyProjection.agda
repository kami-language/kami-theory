{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2024-01-20.BabyProjection where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Data.List.Base using (map; _++_)
open import Function.Base using (_∘_)
open import Relation.Nullary using (¬_)
open import Level


open import KamiTheory.Dev.2024-01-20.Basics

open import KamiTheory.Dev.2024-01-20.UniqueSortedList
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base
open import KamiTheory.Dev.2024-01-20.Baby


module _ where
  -- discard entries in R′ ∖ R
  πVec : ∀ {R′} (R : List Nat) → R ⊆ R′ → RVec LType R′ → RVec LType R
  πVec {R′ = R′} [] _ _ = ⟦⟧
  πVec {R′ = r′ ∷ R′} (r ∷ R) p (x ∷ xs) with r ≟ r′
  ... | yes refl = x ∷ (πVec R (∷∷⊆ p) xs) 
  πVec {R′ = .r ∷ R′} (r ∷ R) (keep p) (x ∷ xs) | no ¬p = refl ↯ ¬p
  πVec {R′ = r′ ∷ R′} (r ∷ R) (drop p) (x ∷ xs) | no ¬p = πVec (r ∷ R) p xs

  π : ∀ {R′ : Roles} (R : Roles) → fst R ⊆ fst R′ → Type R′ → Type R
  π ([] , []) stop b = ∅
  π {R′ = (R′ , pR′)} (R , snd) x (◂ v) = ◂ (πVec R x v)
  π R x (x₁ ⇒ x₃) = (π R x x₁) ⇒ π R x x₃
  
  π⋆ : ∀ {R′ : Roles} → (R : Roles) → fst R ⊆ fst R′ → Context R′ → Context R
  π⋆ R p C = map (π R p) C
  
  π∈ : ∀ {R R′ R⊆R′ Γ} {T : Type R′} → T ∈ Γ → (π R R⊆R′ T) ∈ (π⋆ R R⊆R′ Γ)
  π∈ here = here
  π∈ (there x) = there (π∈ x)

  πChoose : ∀ {R′} → (R : List Nat) → (R⊆R′ : R ⊆ R′) → (m : Choose R′) → Choose R
  πChoose [] empty m = done
  πChoose (r ∷ R) (keep R⊆R′) (choose x m) = choose x (πChoose R R⊆R′ m)
  πChoose R (drop R⊆R′) (choose x m) = πChoose R R⊆R′ m

  πsubset : ∀ {R′ a m} {R : Roles} {R⊆R′ : fst R ⊆ fst R′} → ◂ (subsetc (πVec (fst R) R⊆R′ a) (πChoose (fst R) R⊆R′ m)) ≡  π {R′} R R⊆R′ (◂ (subsetc a m))
  πsubset = {!!}

  π◂ : ∀ {R′ a} {R : Roles} {R⊆R′ : fst R ⊆ fst R′} → π {R′} R R⊆R′ (◂ a) ≡ ◂ (πVec (fst R) R⊆R′ a)
  π◂ {R = [] , []} {R⊆R′ = stop} = refl
  π◂ {R = [] , []} {R⊆R′ = drop R⊆R′} = refl
  π◂ {R = x ∷ fst₁ , snd} = refl

  πCommunicate : ∀ {R R′} {R⊆R′ : R ⊆ R′} → (c : Communicate R′) → Communicate R ⊎ {!!}
  πCommunicate {R = R} (from (r , pr) to (s , ps)) with r ∈? R | s ∈? R
  ... | yes r∈R | yes s∈R = inj₁ (from (r , r∈R) to (s , s∈R))
  ... | yes p | no ¬p = {!!}
  ... | no ¬p | P = {!!}

  π⇒ : ∀ {R′ A B} {R : Roles} {R⊆R′ : fst R ⊆ fst R′} → π {R′} R R⊆R′ (A ⇒ B) ≡ π R R⊆R′ A ⇒ π R R⊆R′ B
  π⇒ = {!!}

  coe : ∀ {ℓ} {X Y : Set ℓ} (x : X) (eq : X ≡ Y) → Y
  coe x refl = x
  
  transp-⊢ : ∀ {R T T′ Γ Δ} → _,_⊢_ {R} Γ Δ T → T ≡ T′ → Γ , Δ ⊢ T′
  transp-⊢ Ts refl = Ts


  π⊢ : ∀ {R′ Γ Δ} {T : Type R′} → (R : Roles) → (R⊆R′ : fst R ⊆ fst R′) → (Γ , Δ ⊢ T) → Σ _ λ Δ → (π⋆ R R⊆R′ Γ) , Δ ⊢ (π R R⊆R′ T)
  π⊢ {Δ = Δ} R R⊆R′ tt = Δ , transp-⊢ tt {!!}
  π⊢ {Δ = Δ} R R⊆R′ (var x) = Δ , var (π∈ x)
  π⊢ R R⊆R′ (pvar x m) = let _ , pp = (π⊢ R R⊆R′ x) in _ , transp-⊢ (pvar (transp-⊢ pp π◂) (πChoose (fst R) R⊆R′ m)) πsubset
  π⊢ R R⊆R′ (mrg x x₁ m) = {!!}
  π⊢ {Δ = Δ} (R , pR) R⊆R′ (sync {a = a} x (from (r , pr) to (s , ps))) with r ∈? R | s ∈? R
  ... | yes p | yes p₁ = let _ , pp = (π⊢ (R , pR) R⊆R′ x) in _ , transp-⊢ (sync (transp-⊢ pp π◂) (from (r , p) to (s , p₁))) {!πupdate!}
  ... | yes r∈R | no s∉R = _ , transp-⊢ (send {Δ = Δ} (r , r∈R) s∉R (lookup a (r , pr))) {!!}
  ... | no r∉R | yes s∈R = _ , transp-⊢ (recv {Δ = Δ} (s , s∈R) r∉R (lookup a (s , ps))) {!!}
  ... | no r∉R | no s∉R =  Δ , transp-⊢ tt {!Δ!} 
  π⊢ R R⊆R′ (abs x) = {!!}
  π⊢ R R⊆R′ (app x x₁) = let
      _ , pp = (π⊢ R R⊆R′ x)
      _ , pp₁ = (π⊢ R R⊆R′ x₁)
    in _ , app (transp-⊢ pp π⇒) pp₁
  π⊢ {Δ = Δ} R R⊆R′ (recv (r , r∈R′) x T) with r ∈? (fst R)
  ... | yes p = _ , transp-⊢ (recv {Δ = Δ} (r , p) (λ s∈R → ⊆∈ s∈R R⊆R′ ↯ x) T) {!!}
  ... | no ¬p = _ , transp-⊢ tt {!!} 
  π⊢ {Δ = Δ} R R⊆R′ (send (r , r∈R′) x T) with r ∈? (fst R)
  ... | yes p =  _ , transp-⊢ (send {Δ = Δ} (r , p) (λ s∈R → ⊆∈ s∈R R⊆R′ ↯ x) T) {!!}
  ... | no ¬p = _ , transp-⊢ tt {!!}
