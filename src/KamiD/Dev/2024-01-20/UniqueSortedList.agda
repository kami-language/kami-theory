
{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-20.UniqueSortedList where

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

_↯_ : ∀ {𝒶 ℓ : Level} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A
  
--------------------------------------------------
-- decidable equality

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → Dec (x ≡ y)

open hasDecidableEquality {{...}} public

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


record hasStrictOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _<_ : A → A → Set 𝑖
    irrefl-< : ∀ {a : A} → ¬ (a < a)
    -- asym< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    trans-< : ∀ {a b c : A} → a < b → b < c → a < c
    conn-< : ∀ (a b : A) → Tri (a < b) (a ≡ b) (b < a)

open hasStrictOrder {{...}} public
{-# DISPLAY hasStrictOrder._<_ M a b = a < b #-}

--------------------------------------------------
-- instances

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤)

-- Fin n has a strict order

module _ where

  ≡suc : ∀ {m n} → suc m ≡ suc n → m ≡ n
  ≡suc refl = refl


  data _<ℕ_ : Nat → Nat → Set where
    z<n : ∀ {n} → zero <ℕ suc n
    s<s : ∀ {m n} → (m<n : m <ℕ n) → suc m <ℕ suc n

  irrefl-<-ℕ : ∀ {a : Nat} → ¬ (a <ℕ a)
  irrefl-<-ℕ {zero} = λ ()
  irrefl-<-ℕ {suc a} = λ { (s<s x) → x ↯ irrefl-<-ℕ}
  
  trans-<-ℕ : ∀ {a b c : Nat} → a <ℕ b → b <ℕ c → a <ℕ c
  trans-<-ℕ z<n (s<s b) = z<n
  trans-<-ℕ (s<s a) (s<s b) = s<s (trans-<-ℕ a b)
  
  conn-<-ℕ : ∀ (a b : Nat) → Tri (a <ℕ b) (a ≡ b) (b <ℕ a)
  conn-<-ℕ zero zero = tri≡ (λ ()) refl (λ ())
  conn-<-ℕ zero (suc b) = tri< z<n (λ ()) λ ()
  conn-<-ℕ (suc a) zero = tri> (λ ()) (λ ()) z<n
  conn-<-ℕ (suc a) (suc b) with conn-<-ℕ a b
  ... | tri< a<b a≢b a≯b = tri< (s<s a<b) (λ { x → ≡suc x ↯ a≢b}) λ { (s<s x) → x ↯ a≯b}
  ... | tri≡ a≮b refl a≯b = tri≡ irrefl-<-ℕ refl irrefl-<-ℕ
  ... | tri> a≮b a≢b a>b = tri> (λ { (s<s x) → x ↯ a≮b}) (λ x → ≡suc x ↯ a≢b) (s<s a>b)

  instance
    hasStrictOrder:ℕ : hasStrictOrder Nat
    hasStrictOrder:ℕ = record { _<_ = _<ℕ_ ;
                                irrefl-< = irrefl-<-ℕ ; trans-< = trans-<-ℕ ; conn-< = conn-<-ℕ }


  data Fin : Nat → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} →  (i : Fin n) → Fin (suc n)

  toℕ : ∀ {n} → Fin n → Nat
  toℕ zero    = 0
  toℕ (suc i) = suc (toℕ i)
  
  fromℕ : (n : Nat) → Fin (suc n)
  fromℕ zero    = zero
  fromℕ (suc i) = suc (fromℕ i)

  _<𝔽_ : ∀ {m n : Nat} → Fin m → Fin n → Set
  a <𝔽 b = toℕ a <ℕ toℕ b

  ≡𝔽 : ∀ {a} → {m n : Fin a} → toℕ m ≡ toℕ n → m ≡ n
  ≡𝔽 {m = zero} {zero} x = refl
  ≡𝔽 {m = suc m} {suc n} x = cong suc (≡𝔽 (≡suc x))

  conn-<𝔽 : ∀ {n} (a b : Fin n) → Tri (a <𝔽 b) (a ≡ b) (b <𝔽 a)
  conn-<𝔽 a b with conn-<-ℕ (toℕ a) (toℕ b)
  ... | tri< a<b a≢b a≯b = tri< a<b (λ x → (cong toℕ x) ↯ a≢b) a≯b
  ... | tri≡ a≮b a≡b a≯b = tri≡ a≮b (≡𝔽 a≡b) a≯b
  ... | tri> a≮b a≢b a>b = tri> a≮b ((λ x → (cong toℕ x) ↯ a≢b)) a>b
  

  instance
    hasStrictOrder:𝔽 : ∀{n} -> hasStrictOrder (Fin n)
    hasStrictOrder:𝔽 = record { _<_ = _<𝔽_ ;
                                irrefl-< = irrefl-<-ℕ ; trans-< = trans-<-ℕ ; conn-< = conn-<𝔽 }
                                
--------------------------------------------------
-- The sum of two types has a strict order by "concatenating" them

module _ {𝑖 𝑗 : Level} {A : Set 𝑖} {B : Set 𝑗} {{_ : hasStrictOrder A}} {{_ : hasStrictOrder B}}  where

  data _<⊎_ : A ⊎ B → A ⊎ B → Set (𝑖 ⊔ 𝑗) where
    inj₁ : {a a₁ : A} → a < a₁ → inj₁ a <⊎ inj₁ a₁
    inj₂ : {b b₁ : B} → b < b₁ → inj₂ b <⊎ inj₂ b₁
    conc : {a : A} → {b : B} → inj₁ a <⊎ inj₂ b

  
  instance
    hasStrictOrder:⊎ : hasStrictOrder (A ⊎ B)
    hasStrictOrder:⊎ = record { _<_ = _<⊎_ ;
                                irrefl-< = λ { (inj₁ x) → x ↯ irrefl-< {𝑖} ; (inj₂ x) → x ↯ irrefl-< {𝑗}} ;
                                trans-< = λ { (inj₁ x) (inj₁ x₁) → inj₁ (trans-< {𝑖} x x₁) ; 
                                             (inj₂ x) (inj₂ x₁) → inj₂ (trans-< {𝑗} x x₁) ;
                                                  (inj₁ x) conc → conc ;
                                                  conc (inj₂ x) → conc} ;
                                conn-< = λ { (inj₁ x) (inj₁ x₁) → map-Tri< {R = _<_} {S = _<⊎_} inj₁ (λ { refl → refl})
                                                                                                (λ {a0 a1 x₂ → inj₁ x₂})
                                                                                                (λ {a0 a1 (inj₁ x₂) → x₂})
                                                                                                (conn-< x x₁) ;
                                            (inj₁ x) (inj₂ y) → tri< conc (λ ()) λ () ;
                                            (inj₂ y) (inj₁ x) → tri> (λ ()) (λ ()) conc;
                                            (inj₂ y) (inj₂ y₁) → map-Tri< {R = _<_} {S = _<⊎_} inj₂ (λ { refl → refl})
                                                                                                (λ {a0 a1 y₂ → inj₂ y₂})
                                                                                                (λ {a0 a1 (inj₂ y₂) → y₂})
                                                                                                (conn-< y y₁)  } }


-- The unit type has a strict order

instance
  hasStrictOrder:Unit : hasStrictOrder ⊤
  hasStrictOrder:Unit = record { _<_ = λ _ _ → ⊥ ;
                                 irrefl-< = λ ();
                                 trans-< = λ {() ()} ;
                                 conn-< = λ { tt tt → tri≡ (λ ()) refl (λ ()) } }


--------------------------------------------------
-- elements and subsets

module _ {𝑖 : Level} {A : Set 𝑖} where

  infix 4 _∈_

  data _∈_ : (a : A) → (as : List A) → Set (lsuc 𝑖) where
    here : ∀ {a : A} {as : List A} → a ∈ (a ∷ as)
    there : ∀ {a b : A} {as : List A} → a ∈ as → a ∈ (b ∷ as)

  ∉[] : ∀ {a : A} → ¬ (a ∈ [])
  ∉[] {a} ()

  infix 4 _⊆_
  _⊆_ : List A → List A → Set (lsuc 𝑖)
  as ⊆ bs = ∀ x → x ∈ as → x ∈ bs

  ⊈[] : ∀ {as : List A} → ¬ (as ≡ []) → ¬ (as ⊆ [])
  ⊈[] {[]} as≢[] x = refl ↯ as≢[]
  ⊈[] {x₁ ∷ as} as≢[] x = x x₁ here ↯ λ ()

  ⊆∷ : ∀ {a : A} {as bs : List A} → (a ∷ as) ⊆ bs → as ⊆ bs
  ⊆∷ sf = λ x x₁ → sf x (there x₁)

--------------------------------------------------
-- sortedness

module _ {𝑖 : Level} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  data UniqueSorted : List A → Set 𝑖 where
    []  : UniqueSorted []
    [-] : ∀ {x} → UniqueSorted (x ∷ [])
    _∷_ : ∀ {x y xs} → x < y → UniqueSorted (y ∷ xs) → UniqueSorted (x ∷ y ∷ xs)

  popSort : {a : A} → {as : List A} → UniqueSorted (a ∷ as) → UniqueSorted as
  popSort [-] = []
  popSort (x ∷ x₁) = x₁



  _∈?_ : {{_ : hasDecidableEquality A}} → (a : A) → (as : List A) → Dec (a ∈ as)
  a ∈? [] = no λ ()
  a ∈? (b ∷ as) with (a ≟ b) | a ∈? as
  ...               | yes refl | _ = yes here
  ...               | no _ | yes a∈as = yes (there a∈as)
  ...               | no a≠b | no a∉as = no λ { here → refl ↯ a≠b; (there a∈as) → a∈as ↯ a∉as}

  _⊆?_ : {{_ : hasDecidableEquality A}} → (as bs : List A) → Dec (as ⊆ bs)
  [] ⊆? bs = yes (λ c ())
  (a ∷ as) ⊆? [] = no λ { all → all a here ↯ ∉[]}
  (a ∷ as) ⊆? bs with a ∈? bs | as ⊆? bs
  ... | yes a∈bs | yes all = yes (λ { c here → a∈bs ; c (there x) → all c x})
  ... | yes a∈bs | no as⊈bs = no (λ { all → (λ c c∈as → all c (there c∈as)) ↯ as⊈bs})
  ... | no a∉bs | _ = no λ { all → all a here ↯ a∉bs}
  
--------------------------------------------------
-- insertion

  insert : (a : A) → (as : List A) → List A
  insert a [] = a ∷ []
  insert a (b ∷ as) with conn-< a b
  ... | tri< a<b a≢b a≯b = a ∷ b ∷ as
  ... | tri≡ a≮b a≡b a≯b = b ∷ as
  ... | tri> a≮b a≢b a>b = b ∷ (insert a as)

  data _<*_ (a : A) : List A → Set 𝑖 where
    []  : a <* []
    _∷_ : ∀ {b bs} → (a < b) → a <* bs → a <* (b ∷ bs)

  all∷ : {a b : A} → {bs : List A} → a < b → a <* bs → a <* (b ∷ bs)
  all∷ a<b [] = a<b ∷ []
  all∷ a<b (a<b₁ ∷ a<*bs) = a<b ∷ a<b₁ ∷ a<*bs

  allSort : {a : A} → {as : List A} → UniqueSorted (a ∷ as) → a <* as
  allSort [-] = []
  allSort (x ∷ [-]) = all∷ x []
  allSort (a<z ∷ (z<y ∷ usyxs)) = all∷ a<z (allSort (trans-< {𝑖} {A} a<z z<y ∷ usyxs))
  
  sortAll : {a : A} → {as : List A} → a <* as → UniqueSorted as → UniqueSorted (a ∷ as)
  sortAll {a} [] x₁ = [-]
  sortAll (x ∷ x₂) x₁ = x ∷ x₁
  
  insertAll : {a c : A} → {as : List A} → c < a → c <* as → UniqueSorted as → c <* (insert a as)
  insertAll {as = []} x x₁ usas = x ∷ x₁
  insertAll {a} {c} {b ∷ as} c<a (c<b ∷ c<*as) usas with conn-< a b
  ... | tri< _ _ _ = c<a ∷ (c<b ∷ c<*as)
  ... | tri≡ _ _ _ = (c<b ∷ c<*as)
  ... | tri> a≮b a≢b a>b = let
      c<*aas = insertAll c<a c<*as (popSort usas)
    in all∷ c<b c<*aas

  insertSorted : {a : A} → {as : List A} → UniqueSorted as → UniqueSorted (insert a as)
  insertSorted {a} {[]} usas = [-]
  insertSorted {a} {(b ∷ as)} ([-]) with conn-< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ [-]
  ... | tri≡ a≮b a≡b a≯b = [-]
  ... | tri> a≮b a≢b a>b = a>b ∷ [-]
  insertSorted {a} {(b ∷ as)} (b<y ∷ usas) with conn-< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ (b<y ∷ usas)
  ... | tri≡ a≮b a≡b a≯b = (b<y ∷ usas)
  ... | tri> a≮b a≢b a>b = let
      b<*yas = allSort (b<y ∷ usas)
      b<*y∷xs = insertAll a>b b<*yas usas
      ins = insertSorted usas
    in sortAll b<*y∷xs ins


  insertInserts : ∀ (a : A) → (as : List A) → a ∈ insert a as
  insertInserts a [] = here
  insertInserts a (b ∷ as) with conn-< a b
  ... | tri< _ _ _ = here
  ... | tri≡ _ refl _ = here
  ... | tri> _ _ _ = there (insertInserts a as)

  insertKeeps : ∀ {a b : A} → {as : List A} → a ∈ as → a ∈ insert b as
  insertKeeps {b = b} {as = x₁ ∷ as} x with conn-< b x₁
  ... | tri< _ _ _ = there x
  ... | tri≡ _ refl _ = x
  insertKeeps {b = b} {x₁ ∷ as} here | tri> _ _ _ = here
  insertKeeps {b = b} {x₁ ∷ as} (there a∈as) | tri> _ _ _ = there (insertKeeps a∈as)
  
  insertPreserves : ∀ {c a : A} → {as : List A} → c ∈ insert a as → (c ≡ a ⊎ c ∈ as)
  insertPreserves {c} {.c} {[]} here = inj₁ refl
  insertPreserves {c} {a} {b ∷ as} x with conn-< a b
  insertPreserves {.a} {a} {b ∷ as} here | tri< a<b a≢b a≯b = inj₁ refl
  insertPreserves {c} {a} {b ∷ as} (there x) | tri< a<b a≢b a≯b = inj₂ x
  ... | tri≡ a≮b a≡b a≯b = inj₂ x
  insertPreserves {.b} {a} {b ∷ as} here | tri> a≮b a≢b a>b = inj₂ here
  insertPreserves {c} {a} {b ∷ as} (there x) | tri> a≮b a≢b a>b with insertPreserves {c} {as = as} x
  ... | inj₁ x₁ = inj₁ x₁
  ... | inj₂ y = inj₂ (there y)



--------------------------------------------------
-- unions


  _∪_ : List A → List A → List A
  [] ∪ bs = bs
  as@(_ ∷ _) ∪ [] = as
  (a ∷ as) ∪ bs@(_ ∷ _) = as ∪ insert a bs

  ∪-idₗ : ∀ {as : List A} → as ≡ [] ∪ as
  ∪-idₗ {as} = refl

  ∪-idᵣ : ∀ {as : List A} → as ≡ as ∪ []
  ∪-idᵣ {[]} = refl
  ∪-idᵣ {a ∷ as} = refl

  ∪-sorted : ∀ {as bs} → UniqueSorted as → UniqueSorted bs → UniqueSorted (as ∪ bs)
  ∪-sorted {[]} _ pbs = pbs
  ∪-sorted {_ ∷ _} {[]} pas _ = subst UniqueSorted ∪-idᵣ pas
  ∪-sorted {_ ∷ _} {_ ∷ _} pas pbs = ∪-sorted (popSort pas) (insertSorted pbs)


  mutual
    ∪-∈ᵣ : ∀ (a : A) → (as bs : List A) → a ∈ as → a ∈ (as ∪ bs)
    ∪-∈ᵣ a (x₁ ∷ as) [] x = x
    ∪-∈ᵣ a (.a ∷ as) (x₂ ∷ bs) here = ∪-∈ₗ a as (insert a (x₂ ∷ bs)) (insertInserts a (x₂ ∷ bs))
    ∪-∈ᵣ a (x₁ ∷ as) (x₂ ∷ bs) (there x) = ∪-∈ᵣ a as _ x

    ∪-∈ₗ : ∀ (a : A) → (as bs : List A) → a ∈ bs → a ∈ (as ∪ bs)
    ∪-∈ₗ a [] (x₁ ∷ bs) x = x
    ∪-∈ₗ a (x₂ ∷ as) (x₁ ∷ bs) a∈bs = ∪-∈ₗ a as (insert x₂ (x₁ ∷ bs)) (insertKeeps a∈bs)

  ∈-∪ : ∀ {c : A} → {as bs : List A} → c ∈ (as ∪ bs) → c ∈ as ⊎ c ∈ bs
  ∈-∪ {c} {[]} {bs} x = inj₂ x
  ∈-∪ {c} {x₁ ∷ as} {[]} x = inj₁ x
  ∈-∪ {c} {a ∷ as} {b ∷ bs} x with ∈-∪ x
  ... | inj₁ p = inj₁ (there p)
  ... | inj₂ y with insertPreserves y
  ... | inj₁ refl = inj₁ here
  ... | inj₂ y₁ = inj₂ y₁

  
  ι₀-∪ : ∀ {as bs : List A} → as ⊆ (as ∪ bs)
  ι₀-∪ {[]} = λ c ()
  ι₀-∪ {a ∷ as} {[]} = λ c z → z
  ι₀-∪ {a ∷ as} {b ∷ bs} with conn-< a b
  ... | tri< _ _ _ = λ { x here → ∪-∈ₗ a as (a ∷ b ∷ bs) here ;
                         x (there x₁) → ∪-∈ᵣ x as (a ∷ b ∷ bs) x₁}
  ... | tri≡ _ refl _ = λ { x here → ∪-∈ₗ a as (a ∷ bs) here ;
                             x (there x₁) → ∪-∈ᵣ x as (a ∷ bs) x₁}
  ... | tri> _ _ _ = λ { x here →  ∪-∈ₗ a as (b ∷ insert a bs) (there (insertInserts a bs)) ;
                         x (there x₁) → ∪-∈ᵣ x as (b ∷ insert a bs) x₁}

  
  ι₁-∪ : ∀ {as bs : List A} → bs ⊆ (as ∪ bs)
  ι₁-∪ {[]} = λ x z → z
  ι₁-∪ {a ∷ as} {[]} = λ x ()
  ι₁-∪ {a ∷ as} {b ∷ bs} with conn-< a b
  ... | tri< _ _ _ = λ { x here → ∪-∈ₗ b as (a ∷ b ∷ bs) (there here) ;
                         x (there x₁) → ∪-∈ₗ x as (a ∷ b ∷ bs) (there (there x₁))}
  ... | tri≡ _ refl _ = λ { x here → ∪-∈ₗ a as (a ∷ bs) here ;
                             x (there x₁) → ∪-∈ₗ x as (a ∷ bs) (there x₁)}
  ... | tri> _ _ _ = λ { x here →  ∪-∈ₗ b as (b ∷ insert a bs) here ;
                         x (there x₁) → ∪-∈ₗ x as (b ∷ insert a bs) (there (insertKeeps x₁))}

  [_,_]-∪ : ∀ {as bs cs : List A} → as ⊆ cs -> bs ⊆ cs -> (as ∪ bs) ⊆ cs
  [_,_]-∪ {as} {bs} x y = λ a a∈as∪bs → [ x a , y a ]′ (∈-∪ a∈as∪bs)


--------------------------------------------------
-- now here comes the weird stuff

open import Agora.Conventions using (
  _:&_; ⟨_⟩; _since_; ′_′; _on_;
  #structureOn; isSetoid; isSetoid:byId; _isUniverseOf[_]_;  _isUniverseOf[_]_:byBase;
  𝑖 ; 𝑗
  )
open import Agora.Order.Preorder using
  (isPreorderData; isPreorder; isPreorder:byDef;
  _≤_
  )
open import Agora.Order.Lattice using (hasFiniteJoins)


instance
  _isUniverseOf[_]_:List : ∀ {𝑖} {A : Set 𝑖} -> (List A) isUniverseOf[ _ ] (List A)
  _isUniverseOf[_]_:List = _isUniverseOf[_]_:byBase

StrictOrder : ∀ 𝑖 -> Set (lsuc 𝑖)
StrictOrder 𝑖 = (Set 𝑖) :& hasStrictOrder

UniqueSortedList : (A : StrictOrder 𝑖) -> Set 𝑖
UniqueSortedList A = List ⟨ A ⟩ :& UniqueSorted

-- The fancy name for UniqueSortedList: finite power set over A
macro
  𝒫ᶠⁱⁿ : StrictOrder 𝑖 -> _
  𝒫ᶠⁱⁿ A = #structureOn (UniqueSortedList A)

module _ {A : StrictOrder 𝑖} where

  -- `𝒫ᶠⁱⁿ A` forms a setoid with strict equality
  instance
    isSetoid:𝒫ᶠⁱⁿ : isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = isSetoid:byId

  -- `𝒫ᶠⁱⁿ A` forms a preorder with _⊆_ as relation
  record _≤-𝒫ᶠⁱⁿ_ (U V : 𝒫ᶠⁱⁿ A) : Set (lsuc 𝑖) where
    constructor incl
    field ⟨_⟩ : ⟨ U ⟩ ⊆ ⟨ V ⟩

  reflexive-≤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤-𝒫ᶠⁱⁿ U
  reflexive-≤-𝒫ᶠⁱⁿ = incl (λ c x → x)

  _⟡-𝒫ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫ᶠⁱⁿ V -> V ≤-𝒫ᶠⁱⁿ W -> U ≤-𝒫ᶠⁱⁿ W
  incl p ⟡-𝒫ᶠⁱⁿ incl q = incl (λ c x → q c (p c x))

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : isPreorderData (𝒫ᶠⁱⁿ A) _≤-𝒫ᶠⁱⁿ_
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { reflexive = reflexive-≤-𝒫ᶠⁱⁿ
      ; _⟡_ = _⟡-𝒫ᶠⁱⁿ_
      ; transp-≤ = λ {refl refl r -> r}
      }

  -- `𝒫ᶠⁱⁿ A` has finite joins (least upper bounds / maximum / or)
  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = isPreorder:byDef _≤-𝒫ᶠⁱⁿ_

  _∨-𝒫ᶠⁱⁿ_ : (U V : 𝒫ᶠⁱⁿ A) -> 𝒫ᶠⁱⁿ A
  (U since Us) ∨-𝒫ᶠⁱⁿ (V since Vs) = let a = (U ∪ V) in a since ∪-sorted Us Vs 

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = incl (λ {_ ()})
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = incl ι₀-∪
                           ; ι₁-∨ = λ {as} → incl (ι₁-∪ {as = ⟨ as ⟩} )
                           ; [_,_]-∨ = λ { (incl u) (incl v) → incl [ u , v ]-∪}
                           }



_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ ⊎ ⟨ B ⟩ ′

𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ ⊤ ′

record isStrictOrderHom {𝑖 𝑗} {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} (hom : ⟨ A ⟩ -> ⟨ B ⟩) : Set (𝑖 ⊔ 𝑗) where
  field
    homPreserves : ∀ {a b : ⟨ A ⟩} → a < b → hom a < hom b

open isStrictOrderHom public

module _ (A : StrictOrder 𝑖) (B : StrictOrder 𝑗) where

  StrictOrderHom = (⟨ A ⟩ → ⟨ B ⟩) :& isStrictOrderHom {A = A} {B}


-- TODO Naming
module _ {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} where

  img : ∀ {𝑖 𝑗} {A : Set 𝑖} {B : Set 𝑗} → (f : A → B) → List A → List B
  img f [] = []
  img f (x ∷ x₁) = f x ∷ img f x₁

  img-soh : (f : StrictOrderHom A B) -> (as : List ⟨ A ⟩) → UniqueSorted as → UniqueSorted (img ⟨ f ⟩ as)
  img-soh (f since pf) [] x = []
  img-soh ff@(f since pf) (a ∷ .[]) [-] = [-]
  img-soh ff@(f since pf) (a ∷ (a₁ ∷ as)) (x ∷ x₁) = homPreserves pf x ∷ (img-soh ff (a₁ ∷ as) (popSort (x ∷ x₁)))
  
  Img-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
  Img-𝒫ᶠⁱⁿ f (as since pas) = let pimg = img-soh f as pas in (img ⟨ f ⟩ as) since pimg

  ∈img : ∀ {𝑖 𝑗} {A : Set 𝑖} {B : Set 𝑗} {a : A} {as : List A} → (f : A → B) → a ∈ as → f a ∈ img f as
  ∈img f here = here
  ∈img f (there x) = there (∈img f x)

  map-img : ∀ {f : StrictOrderHom A B} {U V : List ⟨ A ⟩} -> U ⊆ V → img ⟨ f ⟩ U ⊆ img ⟨ f ⟩ V
  map-img {f} {x₃ ∷ U} {[]} x x₁ x₂ = x ↯ ⊈[] {as = x₃ ∷ U} λ ()
  map-img {f} {x₃ ∷ U} {x₄ ∷ V} x .(⟨ f ⟩ x₃) here with x x₃ here
  ... | here = here
  ... | there x₃∈V = ∈img ⟨ f ⟩ (there x₃∈V)
  map-img {f} {x₃ ∷ U} {x₄ ∷ V} x x₁ (there x₂) = (map-img {f} (⊆∷ x)) x₁ x₂
  
  map-Img-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V
  map-Img-𝒫ᶠⁱⁿ {f} (incl a) = incl (map-img {f} a)

  instance
    hasStrictOrderHom:inj₁ : isStrictOrderHom {A = A} {A ⋆-StrictOrder B} inj₁
    hasStrictOrderHom:inj₁ = record { homPreserves = λ x → inj₁ x }
    
    hasStrictOrderHom:inj₂ : isStrictOrderHom {A = B} {A ⋆-StrictOrder B} inj₂
    hasStrictOrderHom:inj₂ = record { homPreserves = λ x → inj₂ x }


  postulate
    PreImg-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ B -> 𝒫ᶠⁱⁿ A
    map-PreImg-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V



