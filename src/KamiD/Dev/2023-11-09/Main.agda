
module KamiD.Dev.2023-11-09.Main where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat

data Ctx : 𝒰₀
data _⊢Shape (Γ : Ctx) : 𝒰₀
data _⊢Type! : (Γ : Ctx) -> 𝒰₀
data _⊇_ : (Γ : Ctx) (Δ : Ctx) -> 𝒰₀

data Ctx where
  [] : Ctx
  _,[_⊢_] : (Γ : Ctx) -> (Δ : Ctx) -> {{_ : Γ ⊇ Δ}} -> (A : Δ ⊢Type!) -> Ctx

infixl 50 _,[_⊢_]

-- instance
--   postulate _ : ∀{Γ Δ Ε} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> Γ ⊇ Ε

data _⊇_ where
  instance empty : [] ⊇ []
  instance take : ∀{Γ Δ Ε} -> {A : Ε ⊢Type!} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ Ε ⊢ A ] ⊇ Δ ,[ Ε ⊢ A ]
  instance skip : ∀{Γ Δ Ε} -> {A : Ε ⊢Type!} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ Ε ⊢ A ] ⊇ Δ

data _⊢Type! where
  Shape : [] ⊢Type!

data _⊢Shape Γ where
  -- 𝒮 : 








