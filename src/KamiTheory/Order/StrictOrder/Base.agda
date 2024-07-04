-- SPDX-FileCopyrightText: 2024 Olivia Röhrig
-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.StrictOrder.Base where

open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
-- open import Data.Sum.Base using (_+-𝒰_; left; right; [_,_]′)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; cong)
open import KamiTheory.Basics
open import Data.Fin.Base using (Fin ; zero ; suc)

open import Agora.Conventions using (isProp ; ⊤-𝒰 ; tt ; _+-𝒰_ ; left ; right ; yes ; no)


--------------------------------------------------
-- strict order

data Tri {𝑖} (A : Set 𝑖) (B : Set 𝑖) (C : Set 𝑖) : Set 𝑖 where
  tri< : (a<b :   A) (a≢b : ¬ B) (a≯b : ¬ C) → Tri A B C
  tri≡ : (a≮b : ¬ A) (a≡b :   B) (a≯b : ¬ C) → Tri A B C
  tri> : (a≮b : ¬ A) (a≢b : ¬ B) (a>b :   C) → Tri A B C

Tri< : ∀ {𝑖} {A : Set 𝑖} → (_<_ : A → A → Set 𝑖) → (a b : A) -> Set 𝑖
Tri< _<_ a b = Tri (a < b) (a ≡ b) (b < a)

map-Tri< : ∀ {𝑖 𝑗} {A : Set 𝑖} {B : Set 𝑗} {R : A → A → Set 𝑖} {S : B → B → Set 𝑗} {a b : A}
           → (f : A -> B) → (f a ≡ f b → a ≡ b)
           → (∀ (a0 a1 : A) → R a0 a1 -> (S (f a0) (f a1)))
           → (∀ (a0 a1 : A) → S (f a0) (f a1) -> R a0 a1)
           → Tri< R a b → Tri< S (f a) (f b)
map-Tri< {a = a} {b = b} f f-inj x y (tri< a<b a≢b a≯b) = tri< (x a b a<b) (λ refl → f-inj refl ↯ a≢b) λ x₁ → y b a x₁ ↯ a≯b
map-Tri< {a = a} {b = b} f f-inj x y (tri≡ a≮b a≡b a≯b) = tri≡ (λ x₁ → y a b x₁ ↯ a≮b) (cong f a≡b) λ x₁ → y b a x₁ ↯ a≯b
map-Tri< {a = a} {b = b} f f-inj x y (tri> a≮b a≢b a>b) = tri> (λ x₁ → y a b x₁ ↯ a≮b) (λ refl → f-inj refl ↯ a≢b) (x b a a>b)


record isStrictOrder {𝑖} {A : Set 𝑖} (_<_ : A -> A -> Set 𝑖) : Set (lsuc 𝑖) where
  field
    irrefl-< : ∀ {a : A} → ¬ (a < a)
    -- asym< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    trans-< : ∀ {a b c : A} → a < b → b < c → a < c
    conn-< : ∀ (a b : A) → Tri (a < b) (a ≡ b) (b < a)
    {{isProp:<}} : ∀{a b : A} -> isProp (a < b)

  asym-< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
  asym-< p q = irrefl-< (trans-< p q)

open isStrictOrder {{...}} public

record hasStrictOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _<_ : A → A → Set 𝑖
    {{isStrictOrder:<}} : isStrictOrder _<_

open hasStrictOrder {{...}} public
{-# DISPLAY hasStrictOrder._<_ M a b = a < b #-}

--------------------------------------------------
-- instances

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤)

-- Fin n has a strict order

module _ where

  ≡suc : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
  ≡suc refl = refl

  data _<-ℕ_ : Nat → Nat → Set where
    z<n : ∀ {n} → zero <-ℕ suc n
    s<s : ∀ {m n} → (m<n : m <-ℕ n) → suc m <-ℕ suc n

  irrefl-<-ℕ : ∀ {a : Nat} → ¬ (a <-ℕ a)
  irrefl-<-ℕ {zero} = λ ()
  irrefl-<-ℕ {suc a} = λ { (s<s x) → x ↯ irrefl-<-ℕ}
  
  trans-<-ℕ : ∀ {a b c : Nat} → a <-ℕ b → b <-ℕ c → a <-ℕ c
  trans-<-ℕ z<n (s<s b) = z<n
  trans-<-ℕ (s<s a) (s<s b) = s<s (trans-<-ℕ a b)
  
  conn-<-ℕ : ∀ (a b : Nat) → Tri (a <-ℕ b) (a ≡ b) (b <-ℕ a)
  conn-<-ℕ zero zero = tri≡ (λ ()) refl (λ ())
  conn-<-ℕ zero (suc b) = tri< z<n (λ ()) λ ()
  conn-<-ℕ (suc a) zero = tri> (λ ()) (λ ()) z<n
  conn-<-ℕ (suc a) (suc b) with conn-<-ℕ a b
  ... | tri< a<b a≢b a≯b = tri< (s<s a<b) (λ { x → ≡suc x ↯ a≢b}) λ { (s<s x) → x ↯ a≯b}
  ... | tri≡ a≮b refl a≯b = tri≡ irrefl-<-ℕ refl irrefl-<-ℕ
  ... | tri> a≮b a≢b a>b = tri> (λ { (s<s x) → x ↯ a≮b}) (λ x → ≡suc x ↯ a≢b) (s<s a>b)

  force-≡-<-ℕ : ∀{x y} -> (p q : x <-ℕ y) → p ≡ q
  force-≡-<-ℕ z<n z<n = refl
  force-≡-<-ℕ (s<s p) (s<s q) = cong s<s (force-≡-<-ℕ p q)

  instance
    isProp:<-ℕ : ∀{x y : Nat} -> isProp (x <-ℕ y)
    isProp:<-ℕ = record { force-≡ = force-≡-<-ℕ }

  instance
    isStrictOrder:<-ℕ : isStrictOrder _<-ℕ_
    isStrictOrder:<-ℕ = record { irrefl-< = irrefl-<-ℕ ; trans-< = trans-<-ℕ ; conn-< = conn-<-ℕ }

  instance
    hasStrictOrder:ℕ : hasStrictOrder Nat
    hasStrictOrder:ℕ = record { _<_ = _<-ℕ_ }

  -- data Fin : Nat → Set where
  --   zero : ∀ {n} → Fin (suc n)
  --   suc  : ∀ {n} →  (i : Fin n) → Fin (suc n)

  toℕ : ∀ {n} → Fin n → Nat
  toℕ zero    = 0
  toℕ (suc i) = suc (toℕ i)
  
  fromℕ : (n : Nat) → Fin (suc n)
  fromℕ zero    = zero
  fromℕ (suc i) = suc (fromℕ i)

  _<-𝔽_ : ∀ {m n : Nat} → Fin m → Fin n → Set
  a <-𝔽 b = toℕ a <-ℕ toℕ b

  ≡𝔽 : ∀ {a} → {m n : Fin a} → toℕ m ≡ toℕ n → m ≡ n
  ≡𝔽 {m = zero} {zero} x = refl
  ≡𝔽 {m = suc m} {suc n} x = cong suc (≡𝔽 (≡suc x))

  conn-<-𝔽 : ∀ {n} (a b : Fin n) → Tri (a <-𝔽 b) (a ≡ b) (b <-𝔽 a)
  conn-<-𝔽 a b with conn-<-ℕ (toℕ a) (toℕ b)
  ... | tri< a<b a≢b a≯b = tri< a<b (λ x → (cong toℕ x) ↯ a≢b) a≯b
  ... | tri≡ a≮b a≡b a≯b = tri≡ a≮b (≡𝔽 a≡b) a≯b
  ... | tri> a≮b a≢b a>b = tri> a≮b ((λ x → (cong toℕ x) ↯ a≢b)) a>b

  instance
    isProp:<-𝔽 : ∀{n} -> ∀{x y : Fin n} -> isProp (toℕ x <-ℕ toℕ y)
    isProp:<-𝔽 = record { force-≡ = force-≡-<-ℕ }
  
  instance
    isStrictOrder:<-𝔽 : ∀{n} -> isStrictOrder (_<-𝔽_ {n = n})
    isStrictOrder:<-𝔽 = record { irrefl-< = irrefl-<-ℕ ; trans-< = trans-<-ℕ ; conn-< = conn-<-𝔽 }

  instance
    hasStrictOrder:𝔽 : ∀{n} -> hasStrictOrder (Fin n)
    hasStrictOrder:𝔽 = record { _<_ = _<-𝔽_ }



--------------------------------------------------
-- The sum of two types has a strict order by "concatenating" them


module _ {𝑖 𝑗 : Level} {A : Set 𝑖} {B : Set 𝑗} {{_ : hasStrictOrder A}} {{_ : hasStrictOrder B}}  where

  data _<-+-𝒰_ : A +-𝒰 B → A +-𝒰 B → Set (𝑖 ⊔ 𝑗) where
    left : {a a₁ : A} → a < a₁ → left a <-+-𝒰 left a₁
    right : {b b₁ : B} → b < b₁ → right b <-+-𝒰 right b₁
    conc : {a : A} → {b : B} → left a <-+-𝒰 right b

  instance
    isStrictOrder:<-+-𝒰 : isStrictOrder (_<-+-𝒰_)
    isStrictOrder:<-+-𝒰 = record {
                                irrefl-< = λ { (left x) → x ↯ irrefl-< {𝑖} ; (right x) → x ↯ irrefl-< {𝑗}} ;
                                trans-< = λ { (left x) (left x₁) → left (trans-< {𝑖} x x₁) ; 
                                            (right x) (right x₁) → right (trans-< {𝑗} x x₁) ;
                                                  (left x) conc → conc ;
                                                  conc (right x) → conc} ;
                                conn-< = λ { (left x) (left x₁) → map-Tri< {R = _<_} {S = _<-+-𝒰_} left (λ { refl → refl})
                                                                                                (λ {a0 a1 x₂ → left x₂})
                                                                                                (λ {a0 a1 (left x₂) → x₂})
                                                                                                (conn-< x x₁) ;
                                            (left x) (right y) → tri< conc (λ ()) λ () ;
                                            (right y) (left x) → tri> (λ ()) (λ ()) conc;
                                            (right y) (right y₁) → map-Tri< {R = _<_} {S = _<-+-𝒰_} right (λ { refl → refl})
                                                                                                (λ {a0 a1 y₂ → right y₂})
                                                                                                (λ {a0 a1 (right y₂) → y₂})
                                                                                                (conn-< y y₁)  } ;
                                isProp:< = {!!}
                                                                                                }

  instance
    hasStrictOrder:+-𝒰 : hasStrictOrder (A +-𝒰 B)
    hasStrictOrder:+-𝒰 = record { _<_ = _<-+-𝒰_ }


-- The unit type has a strict order

module _ {𝑖} where
  data _<-⊤_ : (a b : ⊤-𝒰 {𝑖}) -> Set 𝑖 where

  instance
    isStrictOrder:<-⊤ : isStrictOrder _<-⊤_
    isStrictOrder:<-⊤ = record {
                                  irrefl-< = λ ();
                                  trans-< = λ {() ()} ;
                                  conn-< = λ { tt tt → tri≡ (λ ()) refl (λ ()) } ;
                                  isProp:< = {!!}
                                  }

  instance
    hasStrictOrder:Unit : hasStrictOrder (⊤-𝒰 {𝑖})
    hasStrictOrder:Unit = record { _<_ = _<-⊤_ }


