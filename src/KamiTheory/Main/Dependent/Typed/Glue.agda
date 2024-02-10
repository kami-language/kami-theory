
module KamiTheory.Main.Dependent.Typed.Glue where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.RestrictionRelation



module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasFiniteJoins ′ P ′}} {{_ : hasFiniteMeets ′ P ′}}
       {{_ : isDecidablePreorder ′ P ′}}
       {{_ : hasDecidableEquality P}} where

  private variable
    bs : List ℕ
    p q : Term P n
    Γ₀ Γ₁ Γ  : Con (Term P) n
    A₀ A₁ A  : Term P n
    a b : Term P n
    X Y : Term P n
    t s : Term P n
    U V R W W₀ W₁ : P

  glue-GenTs : ∀{t₀ t₁ u : GenTs (Term P) n bs}
            -> t₀ [ W ]⤇s u -> t₁ [ W ]⤇s u -> GenTs (Term P) n bs
  glue : ∀{t₀ t₁ u : Term P n}
            -> t₀ [ W ]⤇ u -> t₁ [ W ]⤇ u -> Term P n

  glue-GenTs [] [] = []
  glue-GenTs (t ∷ ts) (u ∷ us) = glue t u ∷ glue-GenTs ts us

  glue (var v) (var .v) = var v
  glue (constₜ c) (constₜ .c) = constₜ c
  glue (gen k kp ts) (gen .k kp' us) = gen k (glue-GenTs ts us)
  glue (gen k kp ts) (gen-loc-keep U t ϕ α) = ⊥-elim (↯-isNot-𝓀-loc kp)
  glue (gen k kp ts) (gen-loc-remove U t x₂) = loc U t
  glue (gen-loc-keep U t ϕ α) (gen k kp x₂) = ⊥-elim (↯-isNot-𝓀-loc kp)
  glue (gen-loc-keep U t ϕ α) (gen-loc-keep .U s ψ β) = loc U (glue α β)
  glue (gen-loc-remove U t ¬ϕ) (gen k kp x₂) = loc U t
  glue (gen-loc-remove U t ¬ϕ) (gen-loc-remove V s ¬ψ) = loc U t -- This case should be impossible for well-typed terms... Here we just take the term of one side


  glue-Con : ∀{Γ₀ Γ₁ Γ : Con (Term P) n}
            -> Γ₀ [ W ]⤇Ctx Γ -> Γ₁ [ W ]⤇Ctx Γ -> Con (Term P) n
  glue-Con ε ε = ε
  glue-Con (α ∙ A) (β ∙ B) = glue-Con α β ∙ glue A B


  glue-Ctx : W₀ ⊢Ctx Γ₀ -> W₁ ⊢Ctx Γ₁ -> (α : Γ₀ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (β : Γ₁ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (W₀ ∨ W₁) ⊢Ctx (glue-Con α β)
  glue-Ctx ε ε ε ε = ε
  glue-Ctx (Γ₀P ∙ x) (Γ₁P ∙ x₁) (α ∙ x₂) (β ∙ x₃) = glue-Ctx Γ₀P Γ₁P α β ∙ {!!}



