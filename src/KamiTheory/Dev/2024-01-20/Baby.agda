-- SPDX-FileCopyrightText: 2024 Olivia Röhrig
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Dev.2024-01-20.Baby where

open import KamiTheory.Dev.2024-01-20.UniqueSortedList

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Data.List.Base using (map; _++_)
open import Function.Base using (_∘_)
open import Relation.Nullary using (¬_)
open import Level

open import Data.Fin using (Fin; cast) renaming (zero to 𝟘 ; suc to 𝕤)
open import KamiTheory.Dev.2024-01-20.Basics
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base


module _ where

  _×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
  A × B = Σ A (λ _ → B)

  Roles : Set
  Roles = Σ (List Nat) isUniqueSorted

  data LType : Set where
    tt : LType
    ℕ : LType

  infixr 5 _∷_

  data RVec {ℓ} (A : Set ℓ) : (R : List Nat) → Set ℓ where
    ⟦⟧  : RVec A []
    _∷_ : ∀ {r R} (x : A) (xs : RVec A R) → RVec A (r ∷ R)

  ⟦_⟧ : ∀ {ℓ} {r : Nat} {A : Set ℓ} (a : A) → RVec A [ r ]
  ⟦ a ⟧ = a ∷ ⟦⟧

  Elem : ∀ (R : List Nat) → Set
  Elem R = Σ Nat (_∈ R)


  data Type (R : Roles) : Set where
    ◂ : RVec LType (fst R) → Type R
    _⇒_ : Type R → Type R → Type R

  ∅ : Type ([] , [])
  ∅ = ◂ ⟦⟧

  
  Context : (R : Roles) → Set
  Context R = List (Type R)

  

  data Choose : (R : List Nat) → Set where
    done : Choose []
    choose : ∀ {r R} → Bool -> Choose R -> Choose (r ∷ R)

  -- i-th entry of (subset v f) is tt if (f i) and the i-th entry of v otherwise
  subsetc : ∀ {R} → RVec LType R → (m : Choose R) → RVec LType R
  subsetc ⟦⟧ done = ⟦⟧
  subsetc (x ∷ x₂) (choose false m) = tt ∷ (subsetc x₂ m)
  subsetc (x ∷ x₂) (choose true m) = x ∷ (subsetc x₂ m)
  
  -- i-th entry of (merge v w f) is the i-th entry of v if (f i) and the i-th entry of w otherwise
  mergec : ∀ {R} → RVec LType R → RVec LType R → (m : Choose R) → RVec LType R
  mergec ⟦⟧ ⟦⟧ done = ⟦⟧
  mergec (x ∷ xs) (y ∷ ys) (choose false m) = y ∷ (mergec xs ys m)
  mergec (x ∷ xs) (y ∷ ys) (choose true m) = x ∷ (mergec xs ys m)
  
  data Communicate : (R : List Nat) → Set where
    from_to_ : ∀ {R} → Elem R → Elem R → Communicate R

  lookup : ∀ {R : List Nat} → RVec LType R → Elem R → LType
  lookup (x ∷ xs) (_ , here) = x
  lookup (x ∷ xs) (r , there snd) = lookup xs (r , snd)
  
  tabulate : ∀ {A : Set} {R : List Nat} → (Elem R → A) → RVec A R
  tabulate {R = []}  f = ⟦⟧
  tabulate {R = r ∷ _} f = f (r , here) ∷ tabulate (λ (s , p) → f (s , there p))
  
  updateAt : ∀ {A : Set} {R : List Nat} → RVec A R → Elem R → (A → A) → RVec A R
  updateAt (x ∷ xs) (_ , here) f = f x ∷ xs
  updateAt {R = r ∷ _} (x ∷ xs) (s , there i) f = x ∷ updateAt xs (s , i) f

  -- t-th entry of (csync v f) is the (f t)-th entry of v
  csync : ∀ {R} → RVec LType R → Communicate R → RVec LType R
  csync v (from r to s) = updateAt v r λ _ → lookup v s

  repeat : LType → (R : List Nat) → RVec LType R
  repeat T R = tabulate λ _ → T
  
  single :  ∀ {R : List Nat} → Elem R → LType → RVec LType R
  single {R} r T = updateAt (repeat tt R) r (λ _ → T)
  
  
  infix 3 _,_⊢_
  data _,_⊢_ {R : Roles} : (Γ : Context R) → (Δ : List (LType × (Nat × Nat))) → Type R → Set₁ where

    tt : ∀ {Γ Δ}
           ------------
          → Γ , Δ ⊢ ◂ (repeat tt (fst R))

    var : ∀ {Γ Δ A}
          → A ∈ Γ
            ------------
          → Γ , Δ ⊢ A

    -- we may ignore the state at some roles
    pvar : ∀ {Γ Δ a}
          → Γ , Δ ⊢ ◂ a → (m : Choose (fst R))
          ------------
          → Γ , Δ ⊢ ◂ (subsetc a m) -- green slime

    -- we may merge state at roles
    mrg : ∀ {Γ Δ a b}
          → Γ , Δ ⊢ ◂ a →  Γ , Δ ⊢ ◂ b → (m : Choose (fst R))
            ------------
          → Γ , Δ ⊢ ◂ (mergec a b m) -- green slime

    -- we may communicate state between roles
    sync : ∀ {Γ Δ a}
          → Γ , Δ ⊢ ◂ a → (c : Communicate (fst R))
            ------------
          → Γ , Δ ⊢ ◂ (csync a c) -- green slime

    abs : ∀ {Γ Δ A B}
        → A ∷ Γ , Δ ⊢ B
          -----------------
        → Γ , Δ ⊢ A ⇒ B

    app : ∀ {Γ Δ Δ′ A B}
        → Γ , Δ ⊢ A ⇒ B → Γ , Δ′ ⊢ A -- what?
          ---------------------------------
        → Γ , (Δ ++ Δ′) ⊢ B -- green slime

    recv : ∀ {s Δ} {Γ : Context R}
        → (r : Elem (fst R)) → ¬ (s ∈ (fst R)) → (T : LType)
           -----------------------------------------
        → Γ , (T , (fst r , s)) ∷ Δ ⊢ ◂ (single r T)

    send : ∀ {s Δ} {Γ : Context R}
        → (r : Elem (fst R)) → ¬ (s ∈ (fst R)) → (T : LType)
           -----------------------------------------
        → Γ , (T , (s , fst r)) ∷ Δ ⊢ ◂ (repeat tt (fst R))


-- maybe make "global" from partial terms
{-

  roles0and1 : Roles
  roles0and1 = ( 0 ∷ [ 1 ] , z<n ∷ [-])

  role2 : Roles
  role2 = ([ 1 ] , [-])

  ⟦1n⟧ : Type roles0and1
  ⟦1n⟧ = ◂ (ℕ ∷ ⟦ tt ⟧)
  
  ⟦n1⟧ : Type roles0and1
  ⟦n1⟧ = ◂ (tt ∷ ⟦ ℕ ⟧)
  
  ⟦nn⟧ : Type roles0and1
  ⟦nn⟧ = ◂ (ℕ ∷ ⟦ ℕ ⟧)
  
  -- role 𝟙 sends an ℕ to role 𝟘, "global" version
  syncn : Type roles0and1
  syncn = ⟦1n⟧ ⇒ ⟦nn⟧

  syncnt : [] , [] ⊢ syncn
  syncnt = abs (sync (var here) (from (1 , there here) to (0 , here))) -- ?λ { 𝟘 → 𝟘 ; (𝕤 𝟘) → 𝟘})

  -- role 𝟘 sends a ℕ to role 𝟙, "global" version
  recvn : Type role2
  recvn = ◂ ⟦ tt ⟧ ⇒ ◂ ⟦ ℕ ⟧
  
  t : Type role2
  t = ◂ ⟦ tt ⟧
  
  n : Type role2
  n = ◂ ⟦ ℕ ⟧
  -}
  {-
  recvnt : [] , syncnt ∷ [] ⊢ (t ⇒ n)
  recvnt =  (comm syncnt (drop refl⊆))

  -- role 1 applies its function to the ℕ received from role 1 and sends the result back, global version
  gctx : List (Type roles0and1)
  gctx = ⟦n1⟧ ∷ [ ⟦1n⟧ ⇒ ⟦1n⟧ ] -- role 0 has an ℕ, role 1 has a map from ℕ -> ℕ

  globappf : gctx , [] ⊢ ⟦nn⟧
  globappf = app {Δ = []} (abs (sync (var here) (from (1 , there here) to (0 , here)))) -- send result from 1 to 0
             (app {Δ = []} (var (there here)) -- apply f
             (pvar (app {Δ = []} (abs (sync (var here) (from (0 , here) to (1 , there here)))) (var here)) (choose true (choose false done)))) -- send input ℕ from 0 to 1

  -- if we have both roles, we can merge their state
  merget : [] , [] ⊢ ⟦1n⟧ ⇒ (⟦n1⟧ ⇒ ⟦nn⟧)
  merget = abs (abs (mrg (var here) (var (there here)) (choose false (choose true done))))

-}
