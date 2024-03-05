-- SPDX-FileCopyrightText: 2024 Olivia Röhrig
-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.List.Definition where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Basics


[_] : ∀ {𝑖} {A : Set 𝑖} → A → List A
[ a ] = a ∷ []

module _ {A : Set 𝑖} where

  infix 4 _∈_

  data _∈_ : (a : A) → (as : List A) → Set 𝑖 where
    here : ∀ {a : A} {as : List A} → a ∈ (a ∷ as)
    there : ∀ {a b : A} {as : List A} → a ∈ as → a ∈ (b ∷ as)

  ∉[] : ∀ {a : A} → ¬ (a ∈ [])
  ∉[] {a} ()

  infix 4 _⊆_
  _⊆_ : List A → List A → Set 𝑖
  as ⊆ bs = ∀ x → x ∈ as → x ∈ bs

  ⊈[] : ∀ {as : List A} → ¬ (as ≡ []) → ¬ (as ⊆ [])
  ⊈[] {[]} as≢[] x = refl ↯ as≢[]
  ⊈[] {x₁ ∷ as} as≢[] x = x x₁ here ↯ λ ()

  ⊆∷ : ∀ {a : A} {as bs : List A} → (a ∷ as) ⊆ bs → as ⊆ bs
  ⊆∷ sf = λ x x₁ → sf x (there x₁)

  _∈?_ : {{_ : hasDecidableEquality A}} → (a : A) → (as : List A) → isDecidable (a ∈ as)
  a ∈? [] = no λ ()
  a ∈? (b ∷ as) with (a ≟ b) | a ∈? as
  ...               | yes refl | _ = yes here
  ...               | no _ | yes a∈as = yes (there a∈as)
  ...               | no a≠b | no a∉as = no λ { here → refl ↯ a≠b; (there a∈as) → a∈as ↯ a∉as}


  _⊆?_ : {{_ : hasDecidableEquality A}} → (as bs : List A) → isDecidable (as ⊆ bs)
  [] ⊆? bs = yes (λ c ())
  (a ∷ as) ⊆? [] = no λ { all → all a here ↯ ∉[]}
  (a ∷ as) ⊆? bs with a ∈? bs | as ⊆? bs
  ... | yes a∈bs | yes all = yes (λ { c here → a∈bs ; c (there x) → all c x})
  ... | yes a∈bs | no as⊈bs = no (λ { all → (λ c c∈as → all c (there c∈as)) ↯ as⊈bs})
  ... | no a∉bs | _ = no λ { all → all a here ↯ a∉bs}

  open import Data.List.Base

  instance
    hasDecidableEquality:List : {{_ : hasDecidableEquality A}} -> hasDecidableEquality (List A)
    hasDecidableEquality:List = {!it!}



{-
  data _⊆_ : List A → List A → Set 𝑖  where
    stop : [] ⊆ []
    drop : ∀ {a as bs} → as ⊆ bs → as ⊆ (a ∷ bs)
    keep : ∀ {a as bs} → as ⊆ bs → (a ∷ as) ⊆ (a ∷ bs)

  []⊆ : ∀ {bs} → [] ⊆ bs
  []⊆ {[]} = stop
  []⊆ {x ∷ bs} = drop ([]⊆)
    
  refl⊆ : ∀ {as : List A} → as ⊆ as
  refl⊆ {[]} = stop
  refl⊆ {x ∷ as} = keep refl⊆
  
  ∷⊆ : ∀ {a : A} {as bs : List A} → (a ∷ as) ⊆ bs → as ⊆ bs
  ∷⊆ (keep p) = drop p
  ∷⊆ (drop p) = drop (∷⊆ p)
  
  ⊆∈ : ∀ {a : A} {as bs : List A} → a ∈ as → as ⊆ bs → a ∈ bs
  ⊆∈ here (drop x₁) = there (⊆∈ here x₁)
  ⊆∈ (there x) (drop x₁) = there (⊆∈ x (∷⊆ x₁))
  ⊆∈ here (keep x₁) = here
  ⊆∈ (there x) (keep x₁) = there (⊆∈ x x₁)
  
  trans⊆ : ∀ {as bs cs : List A} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
  trans⊆ stop _ = []⊆
  trans⊆ (keep x) (drop x₁) = drop (trans⊆ (keep x) x₁)
  trans⊆ (keep x) (keep x₁) = keep (trans⊆ x x₁)
  trans⊆ (drop x) x₁ = trans⊆ x (∷⊆ x₁)
  
  ⊈[] : ∀ {as : List A} → ¬ (as ≡ []) → ¬ (as ⊆ [])
  ⊈[] {[]} as≢[] x = refl ↯ as≢[]
  ⊈[] {x₁ ∷ as} as≢[] ()
  
 
  ⊆∷ : ∀ {a : A} {as bs : List A} → as ⊆ bs → as ⊆ (a ∷ bs)
  ⊆∷ stop = drop stop
  ⊆∷ (drop a) = drop (drop a)
  ⊆∷ (keep a) = (drop (keep a))
-}

{-
  _⊆?_ : {{_ : hasDecidableEquality A}} → (as bs : List A) → isDecidable (as ⊆ bs)
  [] ⊆? bs = yes []⊆
  (a ∷ as) ⊆? [] = no (⊈[] (λ ()))
  (a ∷ as) ⊆? (b ∷ bs) with a ≟ b
  aas@(a ∷ as) ⊆? (b ∷ bs) | no x with aas ⊆? bs
  (a ∷ as) ⊆? (b ∷ bs)     | no x | no y = no (λ { (drop x₁) → x₁ ↯ y ; (keep x₁) → refl ↯ x})
  (a ∷ as) ⊆? (b ∷ bs)     | no x | yes y = yes (drop y)
  (a ∷ as) ⊆? (b ∷ bs)     | yes refl with as ⊆? bs
  ... | no x₁ = no λ { (drop x) → ∷⊆ x ↯ x₁ ; (keep x) → x ↯ x₁}
  ... | yes x₁ = yes (keep x₁)
-}




module _ {X : 𝒰 𝑖} where
  open import Data.Fin using (Fin ; suc ; zero)
  open import Data.Fin.Properties renaming (suc-injective to isInjective:suc)

  data _∈_at_ : (x : X) -> (xs : List X) -> Fin (length xs) -> 𝒰 𝑖 where
    take : ∀{x} {xs} -> x ∈ (x ∷ xs) at zero
    skip : ∀{x y} {xs i} -> y ∈ xs at i -> y ∈ x ∷ xs at suc i

  indexOf : ∀{x : X} -> {xs : List X} -> x ∈ xs -> Fin (length xs)
  indexOf here = zero
  indexOf (there p) = suc (indexOf p)

  indexed : ∀{x : X} -> {xs : List X} -> (p : x ∈ xs) -> x ∈ xs at indexOf p
  indexed here = take
  indexed (there p) = skip (indexed p)

  unindexed : ∀{x : X} -> {xs : List X} -> ∀{i} -> (p : x ∈ xs at i) -> x ∈ xs
  unindexed take = here
  unindexed (skip p) = there (unindexed p)

  β-indexed : ∀{xs : List X} -> ∀{x i} -> {p : x ∈ xs at i} -> indexOf (unindexed p) ≡ i
  β-indexed {p = take} = refl-≡
  β-indexed {p = skip p} = cong-≡ suc (β-indexed)

  transport-indexed : ∀{xs ys : List X} -> (ϕ : xs ⊆ ys) -> ∀{x i} -> (p : x ∈ xs at i) -> x ∈ ys at indexOf (ϕ x (unindexed p))
  transport-indexed ϕ p = indexed (ϕ _ (unindexed p))

  isUnique : List X -> 𝒰 _
  isUnique xs = ∀{x} -> (p q : x ∈ xs) -> indexOf p ≡ indexOf q

  isInjective₊:indexOf : ∀{xs : List X} -> ∀{x y} -> {p : x ∈ xs} -> {q : y ∈ xs} -> indexOf p ≡ indexOf q -> x ≡ y
  isInjective₊:indexOf {p = here} {q = here} ip≡iq = refl-≡
  isInjective₊:indexOf {p = (there p)} {q = (there q)} ip≡iq = isInjective₊:indexOf (isInjective:suc ip≡iq)

  isInjective:indexOf : ∀{xs : List X} -> ∀{x} -> {p q : x ∈ xs} -> indexOf p ≡ indexOf q -> p ≡ q
  isInjective:indexOf {p = here} {here} P = refl
  isInjective:indexOf {p = there p} {there q} P with isInjective:indexOf (isInjective:suc P)
  ... | refl-≡ = refl-≡

  -- transport-∈,index : ∀{xs ys : List X} -> xs ⊆ ys -> ∀{x i} -> x ∈ xs at i -> Fin (length ys)
  -- transport-∈,index = {!!}

  -- transport-∈at : ∀{xs ys : List X} -> xs ⊆ ys -> ∀{x i} -> x ∈ xs at i -> ∑ λ j -> x ∈ ys at j
  -- transport-∈at p = {!!}

  -- isInjective:transport-∈at : 

  -- data _⊆ⁱⁿᵈ_ : (u : List X) -> (v : List X) -> 𝒰 𝑖 where
  --   [] : ∀{vs} -> [] ⊆ⁱⁿᵈ vs
  --   _∷_ : ∀{u us vs} -> u ∈ vs -> us ⊆ⁱⁿᵈ vs -> (u ∷ us) ⊆ⁱⁿᵈ vs





