
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.Preorder.Instances where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (_+_)


open import Agora.Conventions hiding (_∷_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition
-- open import Agora.Data.Universe.Definition
-- open import Agora.Data.Product.Definition

open import KamiTheory.Basics


-------------------
-- We show that Bool is a preorder with false ≤ true.

macro
  𝟚 = #structureOn Bool

data _≤-𝟚_ : Bool -> Bool -> 𝒰₀ where
  refl-≤-𝟚 : ∀{b} -> b ≤-𝟚 b
  step : false ≤-𝟚 true


_⟡-≤-𝟚_ : ∀{a b c : Bool} -> a ≤-𝟚 b -> b ≤-𝟚 c -> a ≤-𝟚 c
refl-≤-𝟚 ⟡-≤-𝟚 q = q
step ⟡-≤-𝟚 refl-≤-𝟚 = step

instance
  isPreorderData:≤-𝟚 : isPreorderData 𝟚 _≤-𝟚_
  isPreorderData:≤-𝟚 = record
    { refl-≤ = refl-≤-𝟚
    ; _⟡_ = _⟡-≤-𝟚_
    ; transp-≤ = λ {refl refl p -> p}
    }

instance
  isPreorder:𝟚 : isPreorder _ 𝟚
  isPreorder:𝟚 = record { _≤_ = _≤-𝟚_ }

decide-≤-𝟚 : ∀(a b : 𝟚) -> isDecidable (a ≤ b)
decide-≤-𝟚 false false = yes refl-≤
decide-≤-𝟚 false true = yes step
decide-≤-𝟚 true false = no λ ()
decide-≤-𝟚 true true = yes refl-≤

instance
  isDecidablePreorder:𝟚 : isDecidablePreorder 𝟚
  isDecidablePreorder:𝟚 = record { decide-≤ = decide-≤-𝟚 }

decide-≡-Bool : (a b : Bool) -> isDecidable (a ≡ b)
decide-≡-Bool false false = yes refl
decide-≡-Bool false true = no (λ ())
decide-≡-Bool true false = no (λ ())
decide-≡-Bool true true = yes refl

instance
  hasDecidableEquality:𝟚 : hasDecidableEquality Bool
  hasDecidableEquality:𝟚 = record { _≟_ = decide-≡-Bool }

force-≡-≤-𝟚 : ∀{a b} (p q : a ≤-𝟚 b) -> p ≡ q
force-≡-≤-𝟚 refl-≤-𝟚 refl-≤-𝟚 = refl
force-≡-≤-𝟚 step step = refl

instance
  isProp:≤-𝟚 : ∀{a b} -> isProp (a ≤-𝟚 b)
  isProp:≤-𝟚 = record { force-≡ = force-≡-≤-𝟚 }


-------------------
-- This means that all families I -> 𝟚 are also preorders.
--
-- What we show here is that the families (𝔽 n) -> 𝟚 are
-- decidable preorders.
--

decide-≤-𝔽→𝟚 : {n : ℕ} -> ∀(f g : 𝔽 n -> 𝟚) -> isDecidable (f ≤ g)
decide-≤-𝔽→𝟚 {n = zero} f g = yes λ ()
decide-≤-𝔽→𝟚 {n = suc n} f g with decide-≤ (f zero) (g zero)
... | no p = no λ q -> p (q zero)
... | yes p1 with decide-≤-𝔽→𝟚 (λ i -> f (suc i)) (λ i -> g (suc i))
... | no p = no λ q -> p (λ i -> q (suc i))
... | yes p2 = yes λ {zero -> p1 ; (suc i) -> p2 i}

instance
  isDecidablePreorder:𝔽→𝟚 : isDecidablePreorder (𝔽 n →# 𝟚)
  isDecidablePreorder:𝔽→𝟚 = record { decide-≤ = decide-≤-𝔽→𝟚 }




decide-≡-𝔽→𝟚 : {n : ℕ} -> ∀(f g : 𝔽 n -> 𝟚) -> isDecidable (f ≡ g)
decide-≡-𝔽→𝟚 {n = zero} f g = yes {!!}
decide-≡-𝔽→𝟚 {n = suc n} f g with (f zero) ≟ (g zero)
... | no p = no λ q -> {!!} -- p (q zero)
... | yes p1 with decide-≡-𝔽→𝟚 (λ i -> f (suc i)) (λ i -> g (suc i))
... | no p = no λ q -> {!!} -- p (λ i -> q (suc i))
... | yes p2 = yes {!!} -- λ {zero -> p1 ; (suc i) -> p2 i}

instance
  hasDecidableEquality:𝔽→𝟚 : hasDecidableEquality (𝔽 n →# 𝟚)
  hasDecidableEquality:𝔽→𝟚 = record { _≟_ = decide-≡-𝔽→𝟚 }

-- module _ {A : 𝒰 𝑘} {{_ : isSetoid {𝑖} A}} {{_ : isPreorder 𝑗 ′ A ′}} {I : 𝒰 𝑙} where
--   module _ {{_ : ∀{a b : A} -> isProp (a ≤ b)}} where
--
--     force-≡-≤-Family : ∀{f g : I -> A} -> (p q : f ≤ g) -> p ≡ q
--     force-≡-≤-Family p q = {!!}
--
--     instance
--       isProp:≤-Family : ∀{f g : I -> A} -> isProp (f ≤ g)
--       isProp:≤-Family = {!!}


---------------------------------------------
-- We build a better behaved family on vectors

open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)



-- record Valuation (n : ℕ) : 𝒰 𝑖 where
--   constructor incl
--   field ⟨_⟩ : StdVec Bool n

-- open Valuation public

data PointWise {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) : StdVec A n -> StdVec A n -> 𝒰 (𝑖 ､ 𝑗) where
  [] : PointWise R [] []
  _∷_  : ∀{a b} {as bs : StdVec A n} -> R a b -> PointWise R as bs -> PointWise R (a ∷ as) (b ∷ bs)

module _ {A : 𝒰 𝑖} where
  constVec : A -> ∀ n -> StdVec A n
  constVec a zero = []
  constVec a (suc n) = a ∷ constVec a n

  singletonVec : A -> A -> Fin n -> StdVec A n
  singletonVec a b zero = b ∷ constVec a _
  singletonVec a b (suc i) = a ∷ singletonVec a b i

-- module _ {A : 𝒰 𝑖} {{_ : hasDecidableEquality A}} where
--   instance
--     hasDecidableEquality:Vec : hasDecidableEquality (StdVec A)
--     hasDecidableEquality:Vec = ?

module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where

  _∼-Vec_ : ∀(as bs : StdVec A n) -> 𝒰 _
  _∼-Vec_ = PointWise _∼_

  refl-∼-Vec : {x : StdVec A n} → x ∼-Vec x
  refl-∼-Vec {x = []} = []
  refl-∼-Vec {x = x ∷ x₁} = refl-∼ ∷ refl-∼-Vec

  sym-∼-Vec : {x y : StdVec A n} → x ∼-Vec y → y ∼-Vec x
  sym-∼-Vec p = {!!}

  _∙-∼-Vec_ : {x y z : StdVec A n} → x ∼-Vec y → y ∼-Vec z → x ∼-Vec z
  _∙-∼-Vec_ = {!!}

  instance
    isEquivRel:∼-Vec : ∀{n} -> isEquivRel (_∼-Vec_ {n = n})
    isEquivRel:∼-Vec = record { refl-∼ = refl-∼-Vec ; sym = sym-∼-Vec ; _∙_ = _∙-∼-Vec_ }

  instance
    isSetoid:Vec : isSetoid (StdVec A n)
    isSetoid:Vec = record { _∼_ = _∼-Vec_ }

module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} {{_ : isPreorder 𝑘 ′ A ′}} where

  _≤-Vec_ : ∀(as bs : StdVec A n) -> 𝒰 _
  _≤-Vec_ = PointWise _≤_

  refl-≤-Vec : {a : StdVec A n} → a ≤-Vec a
  refl-≤-Vec {a = []} = []
  refl-≤-Vec {a = x ∷ a} = refl-≤ ∷ refl-≤-Vec

  instance
    isPreorderData:Vec : isPreorderData ′ (StdVec A n) ′ _≤-Vec_
    isPreorderData:Vec = record { refl-≤ = refl-≤-Vec ; _⟡_ = {!!} ; transp-≤ = {!!} }

  instance
    isPreorder:Vec : isPreorder _ ′ (StdVec A n) ′
    isPreorder:Vec = record { _≤_ = _≤-Vec_ }

