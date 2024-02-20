
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.LinearFSM.Definition where

open import Agora.Conventions
open import KamiTheory.Basics
open import Data.Fin using (Fin ; zero ; suc)



-- A is the input alphabet
-- B is the type of immediate output
-- S is the type of the current state
data LinearFSM {𝑘} (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : (S : 𝒰 𝑘) -> (n : ℕ) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
  [] : ∀ {S} -> LinearFSM A B S 0
  _∷_ : ∀{S T : 𝒰 𝑘} -> (ψ : S -> (a : A) -> Maybe (T ×-𝒰 B a)) -> LinearFSM A B T n -> LinearFSM A B S (suc n)

record LFSMState 𝑘 (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) (n : ℕ) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
  constructor _,_
  field {State} : 𝒰 𝑘
  field state : State
  field fsm : LinearFSM A B State n

open LFSMState public

module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where

  stepLFSM : LFSMState 𝑘 A B (suc n) -> (a : A) -> Maybe (LFSMState 𝑘 A B n ×-𝒰 B a)
  stepLFSM (σ , (ψ ∷ Ψ)) a = map-Maybe (λ (τ , b) -> (τ , Ψ) , b) (ψ σ a)

  data LFSMHistory {𝑘} : (Σ : LFSMState 𝑘 A B n) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
    [] : ∀{S} {σ : S} -> LFSMHistory (σ , [])
    success : (Σ : LFSMState 𝑘 A B (suc n)) -> (a : A) -> (b : B a) -> (Σ' : LFSMState 𝑘 A B n) -> stepLFSM Σ a ≡ just (Σ' , b)
            -> LFSMHistory Σ'
            -> LFSMHistory Σ


  getEntry : ∀{Σ : LFSMState 𝑘 A B n} -> Fin n -> LFSMHistory Σ -> (∑ B)
  getEntry zero (success _ a b Σ' x H) = (a , b)
  getEntry (suc i) (success _ a b Σ' x H) = getEntry i H



