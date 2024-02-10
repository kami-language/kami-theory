
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Dependent.Untyped.Instances where

open import Agora.Conventions hiding (_≟-ℕ_)

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition

open import Prelude.Equality using (Eq)
open import Prelude.Decidable using () renaming (Dec to Dec-Prelude)
open import Prelude.Empty using () renaming (⊥-elim to ⊥-elim-Prelude)
open import Tactic.Deriving.Eq

-- open import Relation.Binary.Definitions using () renaming (Decidable to Dec-Std)
open import Relation.Nullary.Decidable.Core using () renaming (Dec to Dec-Std ; yes to yes-Std ; no to no-Std)

---------------------------------------------
-- Converting between the Prelude Dec and the Agora Dec

cast-Dec-Prelude : ∀{A : 𝒰 𝑖} -> Dec-Prelude A -> isDecidable A
cast-Dec-Prelude (Dec-Prelude.yes x) = yes x
cast-Dec-Prelude (Dec-Prelude.no x) = no λ x₁ → ⊥-elim-Prelude (x x₁)

cast⁻¹-Dec-Prelude : ∀{A : 𝒰 𝑖} -> isDecidable A -> Dec-Prelude A
cast⁻¹-Dec-Prelude (yes x) = Dec-Prelude.yes x
cast⁻¹-Dec-Prelude (no x) = Dec-Prelude.no λ x₁ → ⊥-elim (x x₁)

cast-Dec-Std : ∀{A : 𝒰 𝑖} -> Dec-Std A -> isDecidable A
cast-Dec-Std (yes-Std a) = yes a
cast-Dec-Std (no-Std a) = no a

cast⁻¹-Dec-Std : ∀{A : 𝒰 𝑖} -> isDecidable A -> Dec-Std A
cast⁻¹-Dec-Std (yes a) = (yes-Std a)
cast⁻¹-Dec-Std (no a)  = (no-Std a)

---------------------------------------------
-- Deriving eq for Kind using Prelude

eqKind : {l : List ℕ} (k k₁ : Kind l) → Dec-Prelude (StrId k k₁)
unquoteDef eqKind = deriveEqDef eqKind (quote Kind)

_≟-Kind_ : ∀{ns} -> (k l : Kind ns) -> isDecidable (k ≡ l)
_≟-Kind_ = λ k l -> cast-Dec-Prelude (eqKind k l)

instance
  hasDecidableEquality:Kind : ∀{ns} -> hasDecidableEquality (Kind ns)
  hasDecidableEquality:Kind = record { _≟_ = _≟-Kind_ }

---------------------------------------------
-- Deriving eq for MLMod using Prelude

-- eqConstTerm : {l : List ℕ} (k k₁ : ConstTerm l) → Dec-Prelude (StrId k k₁)
eqMLMod : deriveEqType MLMod
unquoteDef eqMLMod = deriveEqDef eqMLMod (quote MLMod)

_≟-MLMod_ : ∀{P} -> {{_ : hasDecidableEquality P}} -> (k l : MLMod P) -> isDecidable (k ≡ l)
_≟-MLMod_ {P} = λ k l -> cast-Dec-Prelude (eqMLMod k l)
  where
    instance
      _ : Eq P
      _ = record { _==_ = λ x y -> cast⁻¹-Dec-Prelude (x ≟ y) }

instance
  hasDecidableEquality:MLMod : ∀{P} {{_ : hasDecidableEquality P}} -> hasDecidableEquality (MLMod P)
  hasDecidableEquality:MLMod = record { _≟_ = _≟-MLMod_ }

instance
  Eq:MLMod : ∀{P} -> {{_ : Eq P}} -> Eq (MLMod P)
  Eq:MLMod = record { _==_ = eqMLMod }


---------------------------------------------
-- Deriving eq for Kind using Prelude

-- eqConstTerm : {l : List ℕ} (k k₁ : ConstTerm l) → Dec-Prelude (StrId k k₁)
eqConstTerm : deriveEqType ConstTerm
unquoteDef eqConstTerm = deriveEqDef eqConstTerm (quote ConstTerm)

module _ {P} {{_  : hasDecidableEquality P}} where
  _≟-ConstTerm_ : (k l : ConstTerm P) -> isDecidable (k ≡ l)
  _≟-ConstTerm_ = λ k l -> cast-Dec-Prelude (eqConstTerm k l)
    where
      instance
        _ : Eq P
        _ = record { _==_ = λ x y -> cast⁻¹-Dec-Prelude (x ≟ y) }

  instance
    hasDecidableEquality:ConstTerm : hasDecidableEquality (ConstTerm P)
    hasDecidableEquality:ConstTerm = record { _≟_ = _≟-ConstTerm_ }




---------------------------------------------
-- Stating eq for Fin

open import Data.Fin using (Fin) renaming (_≟_ to _≟-Fin-Std_)

_≟-Fin_ : ∀{ns} -> (k l : Fin ns) -> isDecidable (k ≡ l)
_≟-Fin_ k l = cast-Dec-Std (k ≟-Fin-Std l)

instance
  hasDecidableEquality:Fin : ∀{ns} -> hasDecidableEquality (Fin ns)
  hasDecidableEquality:Fin = record { _≟_ = _≟-Fin_ }

---------------------------------------------
-- Stating eq for Nat

open import Data.Nat using () renaming (_≟_ to _≟-Nat-Std_)

_≟-ℕ_ : (k l : ℕ) -> isDecidable (k ≡ l)
_≟-ℕ_ k l = cast-Dec-Std (k ≟-Nat-Std l)

instance
  hasDecidableEquality:ℕ : hasDecidableEquality ℕ
  hasDecidableEquality:ℕ = record { _≟_ = _≟-ℕ_ }

---------------------------------------------
-- Stating eq for List

open import Data.List using (List)
open import Data.List.Properties using () renaming (≡-dec to ≡-dec-List-Std)

module _ {A : 𝒰 𝑖} {{_ : hasDecidableEquality A}} where
  _≟-List_ : (k l : List A) -> isDecidable (k ≡ l)
  _≟-List_ k l = cast-Dec-Std (≡-dec-List-Std (λ a b -> cast⁻¹-Dec-Std (a ≟ b)) k l)

  instance
    hasDecidableEquality:List : hasDecidableEquality (List A)
    hasDecidableEquality:List = record { _≟_ = _≟-List_ }

---------------------------------------------
-- Stating eq for Kind

module _ {P : 𝒰₀} {{_ : hasDecidableEquality P}} where

  _≟-GenTs_ : ∀{n bs} -> (k l : GenTs (Term P) n bs) -> isDecidable (k ≡ l)
  _≟-Term_ : ∀{n} -> (k l : Term P n) -> isDecidable (k ≡ l)

  [] ≟-GenTs [] = yes refl
  (t ∷ k) ≟-GenTs (t₁ ∷ k₁) with t ≟-Term t₁ | k ≟-GenTs k₁
  ... | no t≠t₁ | Y = no λ {refl → t≠t₁ refl}
  ... | yes x | no k≠k₁ = no λ {refl → k≠k₁ refl}
  ... | yes refl | yes refl = yes refl

  var x ≟-Term var y with x ≟ y
  ... | no x≠y = no λ {refl → x≠y refl}
  ... | yes refl = yes refl
  var x ≟-Term gen k c = no (λ ())
  var x ≟-Term constₜ x₁ = no (λ ())
  gen k c ≟-Term var x = no (λ ())
  gen {bs = bs} k c ≟-Term gen {bs = bs₁} k₁ c₁ with bs ≟ bs₁
  ... | no bs≠bs₁ = no λ {refl → bs≠bs₁ refl}
  ... | yes refl with k ≟ k₁
  ... | no k≠k₁ = no λ {refl → k≠k₁ refl}
  ... | yes refl with c ≟-GenTs c₁
  ... | no c≠c₁ = no λ {refl → c≠c₁ refl}
  ... | yes refl = yes refl
  gen k c ≟-Term constₜ x = no (λ ())
  constₜ x ≟-Term var x₁ = no (λ ())
  constₜ x ≟-Term gen k c = no (λ ())
  constₜ x ≟-Term constₜ y with x ≟ y
  ... | no x≠y = no λ {refl -> x≠y refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Term : ∀{n} -> hasDecidableEquality (Term P n)
    hasDecidableEquality:Term = record { _≟_ = _≟-Term_ }



