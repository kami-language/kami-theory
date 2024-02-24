
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Untyped.Instances where

open import Agora.Conventions

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition

open import Prelude.Equality using (Eq)
open import Prelude.Decidable using () renaming (Dec to Dec-Prelude)
open import Prelude.Empty using () renaming (⊥-elim to ⊥-elim-Prelude)
open import Tactic.Deriving.Eq

-- open import Relation.Binary.Definitions using () renaming (Decidable to Dec-Std)
open import Relation.Nullary.Decidable.Core using () renaming (Dec to Dec-Std ; yes to yes-Std ; no to no-Std)
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

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
-- Deriving eq for Metakind using Prelude

eqMetakind : deriveEqType Metakind -- {l : List (Metakind ×-𝒰 ℕ)} (k k₁ : Metakind l) → Dec-Prelude (StrId k k₁)
unquoteDef eqMetakind = deriveEqDef eqMetakind (quote Metakind)

_≟-Metakind_ : (k l : Metakind) -> isDecidable (k ≡ l)
_≟-Metakind_ = λ k l -> cast-Dec-Prelude (eqMetakind k l)

instance
  hasDecidableEquality:Metakind : hasDecidableEquality Metakind
  hasDecidableEquality:Metakind = record { _≟_ = _≟-Metakind_ }

---------------------------------------------
-- Deriving eq for MainKind using Prelude


eqMainKind : {l : List (Metakind ×-𝒰 ℕ)} (k k₁ : MainKind l) → Dec-Prelude (StrId k k₁)
unquoteDef eqMainKind = deriveEqDef eqMainKind (quote MainKind)

_≟-MainKind_ : ∀{ns} -> (k l : MainKind ns) -> isDecidable (k ≡ l)
_≟-MainKind_ = λ k l -> cast-Dec-Prelude (eqMainKind k l)

instance
  hasDecidableEquality:MainKind : ∀{ns} -> hasDecidableEquality (MainKind ns)
  hasDecidableEquality:MainKind = record { _≟_ = _≟-MainKind_ }

---------------------------------------------
-- Deriving eq for Mode using Prelude

{-
eqMode : deriveEqType Mode -- {l : List (Metakind ×-𝒰 ℕ)} (k k₁ : Mode l) → Dec-Prelude (StrId k k₁)
unquoteDef eqMode = deriveEqDef eqMode (quote Mode)

_≟-Mode_ : (k l : Mode) -> isDecidable (k ≡ l)
_≟-Mode_ = λ k l -> cast-Dec-Prelude (eqMode k l)

instance
  hasDecidableEquality:Mode : hasDecidableEquality Mode
  hasDecidableEquality:Mode = record { _≟_ = _≟-Mode_ }
  -}

---------------------------------------------
-- Deriving eq for LeafKind using Prelude

eqLeafKind : deriveEqType LeafKind -- {l : List (Metakind ×-𝒰 ℕ)} (k k₁ : LeafKind l) → Dec-Prelude (StrId k k₁)
unquoteDef eqLeafKind = deriveEqDef eqLeafKind (quote LeafKind)

_≟-LeafKind_ : (k l : LeafKind) -> isDecidable (k ≡ l)
_≟-LeafKind_ = λ k l -> cast-Dec-Prelude (eqLeafKind k l)

instance
  hasDecidableEquality:LeafKind : hasDecidableEquality LeafKind
  hasDecidableEquality:LeafKind = record { _≟_ = _≟-LeafKind_ }

---------------------------------------------
-- Deriving eq for Kind using Prelude

-- eqKind : {l : List (Metakind ×-𝒰 ℕ)} (k k₁ : Kind l) → Dec-Prelude (StrId k k₁)
-- unquoteDef eqKind = deriveEqDef eqKind (quote Kind)

_≟-Kind_ : ∀{ns} -> (k l : Kind ns) -> isDecidable (k ≡ l)
main x ≟-Kind main y with x ≟ y
... | no y = no λ {refl -> y refl}
... | yes refl = yes refl
main x ≟-Kind leaf y = no λ ()
leaf x ≟-Kind main y = no λ ()
leaf x ≟-Kind leaf y with x ≟ y
... | no y = no λ {refl -> y refl}
... | yes refl = yes refl
𝓀-transform ≟-Kind 𝓀-transform = yes refl-≡

instance
  hasDecidableEquality:Kind : ∀{ns} -> hasDecidableEquality (Kind ns)
  hasDecidableEquality:Kind = record { _≟_ = _≟-Kind_ }

---------------------------------------------
-- Deriving eq for BaseModeHom using Prelude

{-
-- eqConstTerm : {l : List ℕ} (k k₁ : ConstTerm l) → Dec-Prelude (StrId k k₁)
eqBaseModeHom : deriveEqType BaseModeHom
unquoteDef eqBaseModeHom = deriveEqDef eqBaseModeHom (quote BaseModeHom)

_≟-BaseModeHom_ : ∀{P m n} -> {{_ : hasDecidableEquality P}} -> (k l : BaseModeHom P m n) -> isDecidable (k ≡ l)
_≟-BaseModeHom_ {P} = λ k l -> cast-Dec-Prelude (eqBaseModeHom k l)
  where
    instance
      _ : Eq P
      _ = record { _==_ = λ x y -> cast⁻¹-Dec-Prelude (x ≟ y) }

instance
  hasDecidableEquality:BaseModeHom : ∀{P m n} {{_ : hasDecidableEquality P}} -> hasDecidableEquality (BaseModeHom P m n)
  hasDecidableEquality:BaseModeHom = record { _≟_ = _≟-BaseModeHom_ }

instance
  Eq:BaseModeHom : ∀{P m n} -> {{_ : Eq P}} -> Eq (BaseModeHom P m n)
  Eq:BaseModeHom = record { _==_ = eqBaseModeHom }

---------------------------------------------
-- Deriving eq for ModeHom using Prelude

-- eqConstTerm : {l : List ℕ} (k k₁ : ConstTerm l) → Dec-Prelude (StrId k k₁)
_≟-ModeHom_ : ∀{P m n} -> {{_ : hasDecidableEquality P}} -> (k l : ModeHom P m n) -> isDecidable (k ≡ l)
_≟-ModeHom_ {P} id id = yes refl-≡
_≟-ModeHom_ {P} id (x ⨾ l) = no (λ ())
_≟-ModeHom_ {P} (x ⨾ k) id = no (λ ())
_≟-ModeHom_ {P} (_⨾_ {n = n} x k) (_⨾_ {n = n₁} y l) with n ≟ n₁
... | no p = no λ {refl -> p refl}
... | yes refl with x ≟ y
... | no p = no λ {refl -> p refl}
... | yes refl with k ≟-ModeHom l
... | no p = no λ {refl -> p refl}
... | yes refl = yes refl

instance
  hasDecidableEquality:ModeHom : ∀{P m n} {{_ : hasDecidableEquality P}} -> hasDecidableEquality (ModeHom P m n)
  hasDecidableEquality:ModeHom = record { _≟_ = _≟-ModeHom_ }


---------------------------------------------
-- Deriving eq for Modality using Prelude

-- eqConstTerm : {l : List ℕ} (k k₁ : ConstTerm l) → Dec-Prelude (StrId k k₁)
_≟-Modality_ : ∀{P} -> {{_ : hasDecidableEquality P}} -> (k l : Modality P) -> isDecidable (k ≡ l)
(k₁ ↝ l₁ ∋ hom₁) ≟-Modality (k₂ ↝ l₂ ∋ hom₂) with k₁ ≟ k₂
... | no p = no λ {refl -> p refl}
... | yes refl with l₁ ≟ l₂
... | no p = no λ {refl -> p refl }
... | yes refl with hom₁ ≟ hom₂
... | no p = no λ {refl -> p refl }
... | yes refl = yes refl-≡


instance
  hasDecidableEquality:Modality : ∀{P} {{_ : hasDecidableEquality P}} -> hasDecidableEquality (Modality P)
  hasDecidableEquality:Modality = record { _≟_ = _≟-Modality_ }

-}
---------------------------------------------
-- Deriving eq for Kind using Prelude

-- eqKindedTerm : {l : List ℕ} (k k₁ : KindedTerm l) → Dec-Prelude (StrId k k₁)

-- mutual
--   instance
--     eqGenTs : deriveEqType GenTs
--     unquoteDef eqGenTs = deriveEqDef eqGenTs (quote GenTs)

--   instance
--     eqKindedTerm : deriveEqType KindedTerm
--     unquoteDef eqKindedTerm = deriveEqDef eqKindedTerm (quote KindedTerm)

--   instance
--     eqTerm : deriveEqType Term
--     unquoteDef eqTerm = deriveEqDef eqTerm (quote Term)


{-
module _ {P} {{_  : hasDecidableEquality P}} where
  _≟-KindedTerm_ : (k l : KindedTerm P) -> isDecidable (k ≡ l)
  _≟-KindedTerm_ = λ k l -> cast-Dec-Prelude (eqKindedTerm k l)
    where
      instance
        _ : Eq P
        _ = record { _==_ = λ x y -> cast⁻¹-Dec-Prelude (x ≟ y) }

  instance
    hasDecidableEquality:KindedTerm : hasDecidableEquality (KindedTerm P)
    hasDecidableEquality:KindedTerm = record { _≟_ = _≟-KindedTerm_ }

-}


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

-- open import Data.Nat using () renaming (_≟_ to _≟-Nat-Std_)

-- _≟-ℕ_ : (k l : ℕ) -> isDecidable (k ≡ l)
-- _≟-ℕ_ k l = cast-Dec-Std (k ≟-Nat-Std l)

-- instance
--   hasDecidableEquality:ℕ : hasDecidableEquality ℕ
--   hasDecidableEquality:ℕ = record { _≟_ = _≟-ℕ_ }

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
-- Stating eq for products


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasDecidableEquality A}} {{_ : hasDecidableEquality B}} where

  _≟-×-𝒰_ : (k l : A ×-𝒰 B) -> isDecidable (k ≡ l)
  _≟-×-𝒰_ (a0 , b0) (a1 , b1) with a0 ≟ a1
  ... | no p = no λ {refl → p refl}
  ... | yes refl with b0 ≟ b1
  ... | no p = no λ {refl → p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:× : hasDecidableEquality (A ×-𝒰 B)
    hasDecidableEquality:× = record { _≟_ = _≟-×-𝒰_ }


---------------------------------------------
-- Stating eq for Kind

module _ {P : ModeSystem 𝑖} where

  _≟-GenTs_ : ∀{n bs} -> (k l : GenTs (StdVec (Modality P)) (KindedTerm P) n bs) -> isDecidable (k ≡ l)
  _≟-Term_ : ∀{n} -> (k l : Term P n) -> isDecidable (k ≡ l)
  _≟-KindedTerm_ : ∀{n mk} -> (k l : KindedTerm P n mk) -> isDecidable (k ≡ l)


  [] ≟-GenTs [] = yes refl
  (μ ⦊ t ∷ k) ≟-GenTs (η ⦊ t₁ ∷ k₁) with μ ≟ η | t ≟-KindedTerm t₁ | k ≟-GenTs k₁
  ... | no μ≠η | Y | Z = no λ {refl → μ≠η refl}
  ... | yes refl | no t≠t₁ | Y = no λ {refl → t≠t₁ refl}
  ... | yes refl | yes x | no k≠k₁ = no λ {refl → k≠k₁ refl}
  ... | yes refl | yes refl | yes refl = yes refl

  gen {bs = bs} k c ≟-Term gen {bs = bs₁} k₁ c₁ with bs ≟ bs₁
  ... | no bs≠bs₁ = no λ {refl → bs≠bs₁ refl}
  ... | yes refl with k ≟ k₁
  ... | no k≠k₁ = no λ {refl → k≠k₁ refl}
  ... | yes refl with c ≟-GenTs c₁
  ... | no c≠c₁ = no λ {refl → c≠c₁ refl}
  ... | yes refl = yes refl
  gen k c ≟-Term var x _ = no (λ ())
  var x _ ≟-Term gen k c = no (λ ())
  var x ξ ≟-Term var y ζ with ξ ≟ ζ | x ≟ y
  ... | X | Y = ?
  -- ... | no x≠y = no λ {refl → x≠y refl}
  -- ... | yes refl = yes refl

{-
  term x ≟-KindedTerm term y with x ≟-Term y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  location U ≟-KindedTerm location V with U ≟ V
  ... | no x = no λ {refl -> x refl}
  ... | yes refl = yes refl
  basemod {k} {l} x ≟-KindedTerm basemod {k₁} {l₁} y with k ≟-Mode k₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with l ≟ l₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with x ≟ y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  (x // p) ≟-KindedTerm (y // q) with x ≟-Term y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with p ≟ q
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  modehom y ≟-KindedTerm modehom x with (_ ↝ _ ∋ x) ≟ (_ ↝ _ ∋ y)
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

-}

  instance
    hasDecidableEquality:Term : ∀{n} -> hasDecidableEquality (Term P n)
    hasDecidableEquality:Term = record { _≟_ = _≟-Term_ }

  instance
    hasDecidableEquality:KindedTerm : ∀{n k} -> hasDecidableEquality (KindedTerm P n k)
    hasDecidableEquality:KindedTerm = record { _≟_ = _≟-KindedTerm_ }


