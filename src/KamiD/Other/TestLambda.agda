
{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2023-11-27.TestLambda where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import KamiD.Dev.2023-11-27.Core


data Type : 𝒰₀ where
  NN : Type
  _⇒_ : Type -> Type -> Type

infixr 50 _⇒_

data Ctx : 𝒰₀ where
  [] : Ctx
  _,,_ : Ctx -> Type -> Ctx

infixl 40 _,,_

private variable
  Γ : Ctx
  A B : Type

data _⊢Var_ : Ctx -> Type -> 𝒰₀ where
  zero : Γ ,, A ⊢Var A
  suc : Γ ⊢Var B -> Γ ,, A ⊢Var B

data _⊢_ : Ctx -> Type -> 𝒰₀ where
  app : Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
  lam : Γ ,, A ⊢ B -> Γ ⊢ A ⇒ B
  var : Γ ⊢Var A -> Γ ⊢ A

⟦_⟧-Type : Type -> 𝒰₀
⟦ NN ⟧-Type = ℕ
⟦ A ⇒ B ⟧-Type = ⟦ A ⟧-Type -> ⟦ B ⟧-Type

⟦_⟧-Ctx : Ctx -> 𝒰₀
⟦ [] ⟧-Ctx = 𝟙-𝒰
⟦ Γ ,, A  ⟧-Ctx = ⟦ Γ ⟧-Ctx ×-𝒰 ⟦ A ⟧-Type

⟦_⟧-Var : Γ ⊢Var A -> ⟦ Γ ⟧-Ctx -> ⟦ A ⟧-Type
⟦ zero ⟧-Var (Γ , A) = A
⟦ suc v ⟧-Var (Γ , A) = ⟦ v ⟧-Var Γ

⟦_⟧ : Γ ⊢ A -> ⟦ Γ ⟧-Ctx -> ⟦ A ⟧-Type
⟦ app t s ⟧ Γ = (⟦ t ⟧ Γ) (⟦ s ⟧ Γ)
⟦ lam t ⟧ Γ = λ a -> ⟦ t ⟧ (Γ , a)
⟦ var x ⟧ Γ = ⟦ x ⟧-Var Γ

normalize : Γ ⊢ A -> Γ ⊢ A
normalize = {!!}

good-normalize : ∀ (t : Γ ⊢ A) -> ⟦ t ⟧ ≣ ⟦ normalize t ⟧
good-normalize = {!!}


