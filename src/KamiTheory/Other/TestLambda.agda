
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Other.TestLambda where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import KamiTheory.Dev.2023-11-27.Core


data Type : 𝒰₀ where
  BB : Type
  _⇒_ : Type -> Type -> Type

infixr 50 _⇒_

data Ctx : 𝒰₀ where
  [] : Ctx
  _,,_ : Ctx -> Type -> Ctx

infixl 40 _,,_

private variable
  Γ : Ctx
  A B X Y : Type

data _⊢Var_ : Ctx -> Type -> 𝒰₀ where
  zero : Γ ,, A ⊢Var A
  suc : Γ ⊢Var B -> Γ ,, A ⊢Var B

data _⊢_ : Ctx -> Type -> 𝒰₀ where
  app : Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
  lam : Γ ,, A ⊢ B -> Γ ⊢ A ⇒ B
  var : Γ ⊢Var A -> Γ ⊢ A
  true : Γ ⊢ BB
  false : Γ ⊢ BB
  elim-BB : Γ ⊢ A -> Γ ⊢ A -> Γ ,, BB ⊢ A

elim-Bool : ∀{A : 𝒰₀} -> A -> A -> Bool -> A
elim-Bool x y false = x
elim-Bool x y true = y

⟦_⟧-Type : Type -> 𝒰₀
⟦ BB ⟧-Type = Bool
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
⟦ true ⟧ x = true
⟦ false ⟧ x = false
⟦ elim-BB t s ⟧ (Γ , b) = elim-Bool (⟦ t ⟧ Γ) (⟦ s ⟧ Γ) b

letin : Γ ⊢ A -> Γ ,, A ⊢ B -> Γ ⊢ B
letin x y = app (lam y) x

merge-Arr : (Γ ⊢ A -> Γ ⊢ B) -> Γ ,, A ⊢ B
merge-Arr {A = BB} = {!!}
merge-Arr {A = A ⇒ A₁} = {!!}

elim-Arr : (Γ ⊢ X ⇒ Y -> Γ ⊢ A) -> Γ ,, X ⇒ Y ⊢ A
elim-Arr {Γ = Γ} {Y = BB} f = {!!}
elim-Arr {Γ = Γ} {Y = Y ⇒ Y₁} f = {!!}

rei-Bool : Bool -> [] ⊢ BB
rei-Bool false = false
rei-Bool true = true

rei : ∀{Γ A} -> (⟦ Γ ⟧-Ctx -> ⟦ A ⟧-Type) -> Γ ⊢ A

rei-Type : ⟦ A ⟧-Type -> [] ⊢ A
rei-Type {A = BB} x = rei-Bool x
rei-Type {A = A ⇒ A₁} x = {!rei (x , tt)!}

rei {Γ = []} f = rei-Type (f tt)
rei {Γ = Γ ,, BB} f = elim-BB (rei (λ Γ -> f (Γ , false))) (rei (λ Γ -> f (Γ , true)))
rei {Γ = Γ ,, X ⇒ Y} f = {!letin ? ?!}
-- elim-Arr λ t -> rei (λ Γ -> f (Γ , ⟦ t ⟧ Γ))

-- rei {A = NN} f = {!!}
-- rei {A = A ⇒ A₁} f = {!!}

-- normalize : Γ ⊢ A -> Γ ⊢ A
-- normalize = {!!}

-- good-normalize : ∀ (t : Γ ⊢ A) -> ⟦ t ⟧ ≣ ⟦ normalize t ⟧
-- good-normalize = {!!}



