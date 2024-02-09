
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.StrictOrder.Base where

open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; cong)
open import KamiTheory.Dev.2024-01-20.Basics
open import Data.Fin.Base using (Fin ; zero ; suc)


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


record isStrictOrder {𝑖} {A : Set 𝑖} (_<_ : A -> A -> Set 𝑖) : Set 𝑖 where
  field
    irrefl-< : ∀ {a : A} → ¬ (a < a)
    -- asym< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    trans-< : ∀ {a b c : A} → a < b → b < c → a < c
    conn-< : ∀ (a b : A) → Tri (a < b) (a ≡ b) (b < a)

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
    isStrictOrder:<-𝔽 : ∀{n} -> isStrictOrder (_<-𝔽_ {n = n})
    isStrictOrder:<-𝔽 = record { irrefl-< = irrefl-<-ℕ ; trans-< = trans-<-ℕ ; conn-< = conn-<-𝔽 }

  instance
    hasStrictOrder:𝔽 : ∀{n} -> hasStrictOrder (Fin n)
    hasStrictOrder:𝔽 = record { _<_ = _<-𝔽_ }

--------------------------------------------------
-- The sum of two types has a strict order by "concatenating" them


module _ {𝑖 𝑗 : Level} {A : Set 𝑖} {B : Set 𝑗} {{_ : hasStrictOrder A}} {{_ : hasStrictOrder B}}  where

  data _<-⊎_ : A ⊎ B → A ⊎ B → Set (𝑖 ⊔ 𝑗) where
    inj₁ : {a a₁ : A} → a < a₁ → inj₁ a <-⊎ inj₁ a₁
    inj₂ : {b b₁ : B} → b < b₁ → inj₂ b <-⊎ inj₂ b₁
    conc : {a : A} → {b : B} → inj₁ a <-⊎ inj₂ b

  instance
    isStrictOrder:<-⊎ : isStrictOrder (_<-⊎_)
    isStrictOrder:<-⊎ = record {
                                irrefl-< = λ { (inj₁ x) → x ↯ irrefl-< {𝑖} ; (inj₂ x) → x ↯ irrefl-< {𝑗}} ;
                                trans-< = λ { (inj₁ x) (inj₁ x₁) → inj₁ (trans-< {𝑖} x x₁) ; 
                                            (inj₂ x) (inj₂ x₁) → inj₂ (trans-< {𝑗} x x₁) ;
                                                  (inj₁ x) conc → conc ;
                                                  conc (inj₂ x) → conc} ;
                                conn-< = λ { (inj₁ x) (inj₁ x₁) → map-Tri< {R = _<_} {S = _<-⊎_} inj₁ (λ { refl → refl})
                                                                                                (λ {a0 a1 x₂ → inj₁ x₂})
                                                                                                (λ {a0 a1 (inj₁ x₂) → x₂})
                                                                                                (conn-< x x₁) ;
                                            (inj₁ x) (inj₂ y) → tri< conc (λ ()) λ () ;
                                            (inj₂ y) (inj₁ x) → tri> (λ ()) (λ ()) conc;
                                            (inj₂ y) (inj₂ y₁) → map-Tri< {R = _<_} {S = _<-⊎_} inj₂ (λ { refl → refl})
                                                                                                (λ {a0 a1 y₂ → inj₂ y₂})
                                                                                                (λ {a0 a1 (inj₂ y₂) → y₂})
                                                                                                (conn-< y y₁)  } }

  instance
    hasStrictOrder:⊎ : hasStrictOrder (A ⊎ B)
    hasStrictOrder:⊎ = record { _<_ = _<-⊎_ }


-- The unit type has a strict order

data _<-⊤_ : (a b : ⊤) -> Set where

instance
  isStrictOrder:<-⊤ : isStrictOrder _<-⊤_
  isStrictOrder:<-⊤ = record {
                                irrefl-< = λ ();
                                trans-< = λ {() ()} ;
                                conn-< = λ { tt tt → tri≡ (λ ()) refl (λ ()) } }

instance
  hasStrictOrder:Unit : hasStrictOrder ⊤
  hasStrictOrder:Unit = record { _<_ = _<-⊤_ }


