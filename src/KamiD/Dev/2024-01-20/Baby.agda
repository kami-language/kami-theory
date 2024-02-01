{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-20.Baby where

open import KamiD.Dev.2024-01-20.UniqueSortedList

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; _∷_; tabulate; lookup) renaming ([] to ⟦⟧; [_] to ⟦_⟧)
open import Data.List.Base using (map; _++_)

open import Data.Fin using (Fin) renaming (zero to 𝟘 ; suc to 𝕤)
open import KamiD.Dev.2024-01-20.Basics
open import KamiD.Dev.2024-01-20.StrictOrder.Base


module _ where
  Roles : ∀ {n : Nat} → Set
  Roles {n} = Σ (List (Fin n)) isUniqueSorted

  data LType : Set where
    tt : LType
    ℕ : LType

  data Type (n : Nat) (R : Roles {n}) : Set where
    ◂ : Vec LType (length (fst R)) → Type n R -- green slime?
    _⇒_ : Type n R → Type n R → Type n R


  ∅ : {n : Nat} → Type n ([] , [])
  ∅ {n} = ◂ {n} ⟦⟧

  -- discard entries in R′ ∖ R
  πVec : ∀ {n} (R R′ : List (Fin n)) → R ⊆ R′ → Vec LType (length R′) → Vec LType (length R)
  πVec [] R′ _ _ = ⟦⟧
  πVec (r ∷ R) (r′ ∷ R′) p (x ∷ xs) with r ≟ r′
  ... | yes refl = x ∷ (πVec R R′ (∷∷⊆ p) xs) 
  πVec (r ∷ R) (.r ∷ R′) (both p) (x ∷ xs) | no ¬p = refl ↯ ¬p
  πVec (r ∷ R) (r′ ∷ R′) (grow p) (x ∷ xs) | no ¬p = πVec (r ∷ R) R′ p xs

  π : ∀ {n} {R′ : Roles {n}} (R : Roles {n}) → fst R ⊆ fst R′ → Type n R′ → Type n R
  π ([] , []) _ _ = ∅
  π {R′ = (R′ , pR′)} (R , snd) x (◂ v) = ◂ (πVec R R′ x v)
  π R x (x₁ ⇒ x₃) = (π R x x₁) ⇒ π R x x₃
  

  Context : ∀ {n} → (R : Roles {n}) → Set
  Context {n} R = List (Type n R)

  π⋆ : ∀ {n} {R′ : Roles {n}} (R : Roles {n}) → fst R ⊆ fst R′ → Context {n} R′ → Context {n} R
  π⋆ R p C = map (π R p) C

  -- t-th entry of (gsync v f) is the (f t)-th entry of v
  gsync : ∀ {n} {A : Set} → Vec A n → (f : Fin n → Fin n) → Vec A n
  gsync v f = tabulate λ r → lookup v (f r)

  mutual

    data SyncContext : Set₁ where
      [] : SyncContext
      _∷_ : ∀ {n R} {Γ : Context {n} R} → {T : Type n R} → Γ ⊩ T → SyncContext → SyncContext

    _⋆_ :  SyncContext → SyncContext → SyncContext
    [] ⋆ C2 = C2
    (x ∷ C1) ⋆ C2 = C1 ⋆ (x ∷ C2)
      
    -- global terms
    infix 3 _⊩_
    _⊩_ : ∀ {n} {R : Roles {n}} → (Γ : Context R) → Type n R → Set₁
    Γ ⊩ T = Γ , [] ⊢ T 


    infix 3 _,_⊢_
    data _,_⊢_ {n} {R : Roles {n}} : (Γ : Context R) → (Δ : SyncContext) → Type n R → Set₁ where

      var : ∀ {T : Type n R} {Γ : Context R} {Δ : SyncContext}
            → T ∈ Γ
              ------------
            → Γ , Δ ⊢ T

      sync : ∀ {lT : Vec LType (length (fst R))} {Γ : Context R} {Δ : SyncContext}
            → ◂ lT ∈ Γ → (f : Fin (length (fst R)) → Fin (length (fst R)))
              ------------
            → Γ , Δ ⊢ ◂ (gsync lT f)
            
      abs : ∀ {T T′ : Type n R} {Γ : Context R} {Δ : SyncContext}
          → T ∷ Γ , Δ ⊢ T′
            -----------------
          → Γ , Δ ⊢ T ⇒ T′
  
      app : ∀ {T T′ : Type n R} {Γ : Context R} {Δ Δ′ : SyncContext}
          → Γ , Δ ⊢ T ⇒ T′ → Γ , Δ′ ⊢ T
            ---------------------------------
          → Γ , (Δ ⋆ Δ′) ⊢ T′

      comm : ∀ {Δ R′} {Γ′ : Context R′} {C : Type n R′} {Γ : Context R}
             → (p : Γ′ ⊩ C) → (R⊆R′ : fst R ⊆ fst R′)
               -----------------
             → Γ ++ π⋆ R R⊆R′ Γ′ , p ∷ Δ ⊢ (π R R⊆R′ C)




  roles0and1 : Roles {3}
  roles0and1 = ( 𝟘 ∷ [ 𝕤 𝟘 ] , z<n ∷ [-])

  role2 : Roles {3}
  role2 = ([ 𝕤 𝟘 ] , [-])

  ⟦1n⟧ : Type 3 roles0and1
  ⟦1n⟧ = ◂ (ℕ ∷ ⟦ tt ⟧)
  
  ⟦n1⟧ : Type 3 roles0and1
  ⟦n1⟧ = ◂ (tt ∷ ⟦ ℕ ⟧)
  
  ⟦nn⟧ : Type 3 roles0and1
  ⟦nn⟧ = ◂ (ℕ ∷ ⟦ ℕ ⟧)

  syncn : Type 3 roles0and1
  syncn = ⟦1n⟧ ⇒ ⟦nn⟧

  syncnt : [] , [] ⊢ syncn
  syncnt = abs (sync here (λ { 𝟘 → 𝟘 ; (𝕤 𝟘) → 𝟘})) 
  
  recvn : Type 3 role2
  recvn = ◂ ⟦ tt ⟧ ⇒ ◂ ⟦ ℕ ⟧
  
  t : Type 3 role2
  t = ◂ ⟦ tt ⟧
  
  n : Type 3 role2
  n = ◂ ⟦ ℕ ⟧
  
  recvnt : [] , syncnt ∷ [] ⊢ (t ⇒ n)
  recvnt =  (comm syncnt (grow refl⊆))


 -- role 𝟙 sends an ℕ to role 𝟘, "global" version
  f : Fin 2 → Fin 2
  f = (λ { 𝟘 → 𝟘 ; (𝕤 𝟘) → 𝟘})

  -- role 𝟘 sends a ℕ to role 𝟙, "global" version
  rf : Fin 2 → Fin 2
  rf = (λ { 𝟘 → 𝕤 𝟘 ; (𝕤 𝟘) → 𝕤 𝟘})
 
  -- role 1 applies its function to the ℕ received from role 1 and sends the result back, global version
  gctx : List (Type 3 roles0and1)
  gctx = ⟦n1⟧ ∷ [ ⟦nn⟧ ⇒ ⟦1n⟧ ] -- role 0 has an ℕ, role 1 has a map from ℕ -> ℕ

  globappf : gctx , [] ⊢ ⟦nn⟧
  globappf = app {Δ = []} (abs (sync here f)) -- send result from 1 to 0
             (app {Δ = []} (var (there here)) -- apply f
             (app {Δ = []} (abs (sync here rf)) (var here))) -- send input ℕ from 0 to 1
