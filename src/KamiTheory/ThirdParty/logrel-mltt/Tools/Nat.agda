-- SPDX-FileCopyrightText: 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--
-- SPDX-License-Identifier: MIT

-- The natural numbers.

{-# OPTIONS --without-K --safe #-}

module KamiTheory.ThirdParty.logrel-mltt.Tools.Nat where

open import KamiTheory.ThirdParty.logrel-mltt.Tools.PropositionalEquality
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nullary
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Bool

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat using (_≤?_; _+_; _∸_) renaming (ℕ to Nat) public
open import Data.Nat.Show using (show) public

pattern 1+ n = suc n

-- Predecessor, cutting off at 0.

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- Decision of number equality.

infix 4 _≟_

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (subst (λ y → m ≡ pred y) x refl))
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

infix 4 _==_

_==_ : Nat → Nat → Bool
m == n with m ≟ n
... | yes _ = true
... | no _  = false
