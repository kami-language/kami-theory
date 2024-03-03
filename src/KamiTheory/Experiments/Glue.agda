
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



-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasFiniteJoins ′ P ′}} {{_ : hasFiniteMeets ′ P ′}}
--        {{_ : isDecidablePreorder ′ P ′}}
--        {{_ : hasDecidableEquality P}} where

module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} (_∧_ : P -> P -> P) (_∨_ : P -> P -> P)
-- {{_ : hasFiniteJoins ′ P ′}} {{_ : hasFiniteMeets ′ P ′}}
       -- {{_ : isDecidablePreorder ′ P ′}}
       -- {{_ : hasDecidableEquality P}} where
       where

  private variable
    bs : List ℕ
    p q : Term P n
    p₀ p₁ A₀ A₁ A : Term P n
    Γ₀ Γ₁ Γ  : Con (Term P) n
    E₀ E₁ E  : Term P n
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
  glue (gen k ts) (gen .k us) = gen (main k) (glue-GenTs ts us)
  glue (gen k ts) (gen-loc-remove U t x₂) = loc U t
  glue (gen-loc-keep U t ϕ α) (gen-loc-keep .U s ψ β) = loc U (glue α β)
  glue (gen-loc-remove U t ¬ϕ) (gen k x₂) = loc U t
  glue (gen-loc-remove U t ¬ϕ) (gen-loc-remove V s ¬ψ) = loc U t -- This case should be impossible for well-typed terms... Here we just take the term of one side


  glue-Con : ∀{Γ₀ Γ₁ Γ : Con (Term P) n}
            -> Γ₀ [ W ]⤇Ctx Γ -> Γ₁ [ W ]⤇Ctx Γ -> Con (Term P) n
  glue-Con ε ε = ε
  glue-Con (α ∙ (αA , αp)) (β ∙ (βA , βp)) = glue-Con α β ∙ (glue αA βA / glue αp βp)


  glue-Ctx : W₀ ⊢Ctx Γ₀ -> W₁ ⊢Ctx Γ₁ -> (α : Γ₀ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (β : Γ₁ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (W₀ ∨ W₁) ⊢Ctx (glue-Con α β)

  glue-Entry : {A₀ A₁ A p₀ p₁ p : Term P n}
             -> W₀ ∣ Γ₀ ⊢Entry (A₀ / p₀) -> W₁ ∣ Γ₁ ⊢Entry (A₁ / p₁)
             -> (αΓ : Γ₀ [ W₀ ∧ W₁ ]⤇Ctx Γ)
             -> (βΓ : Γ₁ [ W₀ ∧ W₁ ]⤇Ctx Γ)
             -> (αA : A₀ [ W₀ ∧ W₁ ]⤇ A)
             -> (βA : A₁ [ W₀ ∧ W₁ ]⤇ A)
             -> (αp : p₀ [ W₀ ∧ W₁ ]⤇ p)
             -> (βp : p₁ [ W₀ ∧ W₁ ]⤇ p)
             -> (W₀ ∨ W₁) ∣ glue-Con αΓ βΓ ⊢Entry (glue αA βA / glue αp βp)

  glue-Ctx ε ε ε ε = ε
  glue-Ctx (Γ₀P ∙ E₀P) (Γ₁P ∙ E₁P) (α ∙ (αA , αp)) (β ∙ (βA , βp)) = glue-Ctx Γ₀P Γ₁P α β ∙ glue-Entry E₀P E₁P α β αA βA αp βp

  glue-Entry (UUⱼ {{ΓP = because ΓP₀}}) (UUⱼ {{ΓP = because ΓP₁}}) α β (gen .Ukind []) (gen .Ukind []) (constₜ .(mlmod (Local _))) (constₜ .(mlmod (Local _))) = UUⱼ {{ΓP = because (glue-Ctx ΓP₀ ΓP₁ α β)}}
  glue-Entry NNⱼ E₁P α β αA βA αp βp = {!!}
  glue-Entry (Vecⱼ E₀P x) E₁P α β αA βA αp βp = {!!}
  glue-Entry Emptyⱼ E₁P α β αA βA αp βp = {!!}
  glue-Entry Unitⱼ E₁P α β αA βA αp βp = {!!}
  glue-Entry (Πⱼ E₀P ▹ E₀P₁) (Πⱼ E₁P ▹ E₁P₁) α β (gen .Pikind (gen .𝓀-/ (x ∷ (constₜ .(mlmod _) ∷ [])) ∷ (x₂ ∷ []))) (gen .Pikind (gen .𝓀-/ (y ∷ (constₜ .(mlmod _) ∷ [])) ∷ (x₃ ∷ []))) (constₜ .(mlmod _)) (constₜ .(mlmod _)) = Πⱼ glue-Entry E₀P E₁P α β x y (constₜ (mlmod _)) ((constₜ (mlmod _))) ▹ glue-Entry E₀P₁ E₁P₁ (α ∙ (x , _)) (β ∙ ({!!} , {!!})) {!!} {!!} {!!} {!!}
  glue-Entry (Σⱼ E₀P ▹ E₀P₁) E₁P α β αA βA αp βp = {!!}
  glue-Entry (Univ-Comⱼ x) E₁P α β αA βA αp βp = {!!}
  glue-Entry (Locⱼ U E₀P) E₁P α β αA βA αp βp = {!!}
  glue-Entry (Comⱼ E₀P) E₁P α β αA βA αp βp = {!!}
  glue-Entry (Endⱼ E₀P) E₁P α β αA βA αp βp = {!!}
  glue-Entry (E₀P ≫ⱼ E₀P₁) E₁P α β αA βA αp βp = {!!}
  glue-Entry (Shareⱼ U V ϕ E₀P) E₁P α β αA βA αp βp = {!!}

  -- glue-Entry UUⱼ UUⱼ α β (gen .𝓀-/ x) βE = {!!}
  -- glue-Entry UUⱼ NNⱼ α β (gen .𝓀-/ (gen .Ukind x ∷ (x₁ ∷ x₂))) (gen .𝓀-/ (() ∷ x₄))
  -- glue-Entry UUⱼ (Vecⱼ E₁P x) α β αE βE = {!!}
  -- glue-Entry UUⱼ Emptyⱼ α β αE βE = {!!}
  -- glue-Entry UUⱼ Unitⱼ α β αE βE = {!!}
  -- glue-Entry UUⱼ (Πⱼ E₁P ▹ E₁P₁) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Σⱼ E₁P ▹ E₁P₁) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Univ-Comⱼ x) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Locⱼ U E₁P) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Comⱼ E₁P) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Endⱼ E₁P) α β αE βE = {!!}
  -- glue-Entry UUⱼ (E₁P ≫ⱼ E₁P₁) α β αE βE = {!!}
  -- glue-Entry UUⱼ (Shareⱼ U V ϕ E₁P) α β αE βE = {!!}
  -- glue-Entry NNⱼ E₁P α β αE βE = {!!}
  -- glue-Entry (Vecⱼ E₀P x) E₁P α β αE βE = {!!}
  -- glue-Entry Emptyⱼ E₁P α β αE βE = {!!}
  -- glue-Entry Unitⱼ E₁P α β αE βE = {!!}
  -- glue-Entry (Πⱼ E₀P ▹ E₀P₁) E₁P α β αE βE = {!!}
  -- glue-Entry (Σⱼ E₀P ▹ E₀P₁) E₁P α β αE βE = {!!}
  -- glue-Entry (Univ-Comⱼ x) E₁P α β αE βE = {!!}
  -- glue-Entry (Locⱼ U E₀P) E₁P α β αE βE = {!!}
  -- glue-Entry (Comⱼ E₀P) E₁P α β αE βE = {!!}
  -- glue-Entry (Endⱼ E₀P) E₁P α β αE βE = {!!}
  -- glue-Entry (E₀P ≫ⱼ E₀P₁) E₁P α β αE βE = {!!}
  -- glue-Entry (Shareⱼ U V ϕ E₀P) E₁P α β αE βE = {!!}




