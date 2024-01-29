{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-20.Baby where

open import KamiD.Dev.2024-01-20.UniqueSortedList
{-
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Relation.Binary.PropositionalEquality using (subst; cong)
open import Data.Unit using (⊤)
-}
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Agda.Builtin.Equality using (_≡_; refl)



-- open import Agora.Conventions using (′_′; ⟨_⟩; _since_)


module _ {n : Nat} where
  Roles = Σ (List (Fin n)) UniqueSorted

  data LType : Set where
    tt : LType
    ℕ : LType

  data Type : (R : Roles) → Set where
    ∅ : Type ([] , [])
    ⟦_⟧ : ∀ {r} → (t : LType) → Type ([ r ] , [-])
    _◂_ : ∀ {r R} → (t : LType) → (ts : Type R) → (p : UniqueSorted (r ∷ (fst R))) → Type (r ∷ (fst R) , p)
    _⟶_ : ∀ {R} → Type R → Type R → Type R

  -- discard entries in R′ ∖ R
  π : ∀ {R′} (R : Roles) → fst R ⊆ fst R′ → Type R′ → Type R
  π R s (t ⟶ t′) = (π R s t) ⟶ (π R s t′)
  π {[] , []} ([] , []) x ∅ = ∅
  π {R′} ([] , []) x x₁ = ∅
  π {r′ ∷ .[] , .[-]} (r ∷ [] , [-]) x ⟦ t ⟧ = ⟦ t ⟧
  π {r′ ∷ .[] , .[-]} (.r′ ∷ x₁ ∷ R , _) (succ x) ⟦ t ⟧ = x ↯ ⊈[] λ ()
  π {r′ ∷ .[] , .[-]} (r ∷ x₁ ∷ R , _) (app x) ⟦ t ⟧ = x ↯ ⊈[] λ ()
  π {r′ ∷ _ , P′} (.r′ ∷ R , P) (succ R⊆R′) ((t ◂ x₁) .P′) = (t ◂ (π (R , popSort P) R⊆R′ x₁)) P
  π {r′ ∷ _ , P′} (r ∷ R , P) (app R⊆R′) ((t ◂ x₁) .P′) with r ≟ r′
  ... | yes refl =  (t ◂ (π (R , popSort P) (∷⊆ R⊆R′) x₁)) P
  ... | no ¬p = π (r ∷ R , P) R⊆R′ x₁


  Context : (R : Roles) → Set
  Context R = List (Type R)

  mutual

    data SyncContext : Set₁ where
      [] : SyncContext
      _∷_ : ∀ {R} {Γ : Context R} → {T : Type R} → Γ ⊩ T → SyncContext → SyncContext
      
    -- global terms
    infix 3 _⊩_
    _⊩_ : {R : Roles} → (Γ : Context R) → Type R → Set₁
    Γ ⊩ T = Γ , [] ⊢ T 


    infix 3 _,_⊢_
    data _,_⊢_ {R : Roles} : (Γ : Context R) → (Δ : SyncContext) → Type R → Set₁ where

      var : ∀ {T : Type R} {Γ : Context R}
            → T ∈ Γ
              ------------
            → Γ ⊩ T

      abs : ∀ {T T′ : Type R} {Γ : Context R} {Δ : SyncContext}
          → T ∷ Γ , Δ ⊢ T′
            -----------------
          → Γ , Δ ⊢ T ⟶ T′

      comm : ∀ {Δ R′} {Γ′ : Context R′} {C : Type R′} {p : Γ′ ⊩ C} {Γ : Context R}
             → (R⊆R′ : fst R ⊆ fst R′)
               -----------------
             → Γ , p ∷ Δ ⊢ (π R R⊆R′ C)


