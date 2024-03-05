-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Decidability where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition


import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as D


module 2CellDecidability (G : 2Graph 𝑖) where
  open D.2CellDefinition G

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    μ₀ : 1Cell G c d
    μ₁ : 1Cell G e f
    η : 1Cell G b c
    ω : 1Cell G c d
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f
    v : Visibility

  decide-≡-FreeParts : (x y : FreeParts a b) → isDecidable (x ≡ y)
  decide-≡-FreeParts [ ϕ ] [ ϕ₁ ] with ϕ ≟ ϕ₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl
  decide-≡-FreeParts [ ϕ ] (ϕ₁ ∷ y) = no λ ()
  decide-≡-FreeParts (ϕ ∷ x) [ ϕ₁ ] = no λ ()
  decide-≡-FreeParts (_∷_ {b = b} {c = c} ϕ x) (_∷_ {b = b₁} {c = c₁} ϕ₁ y) with b ≟ b₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with c ≟ c₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with ϕ ≟ ϕ₁
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with decide-≡-FreeParts x y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:FreeParts : hasDecidableEquality (FreeParts a b)
    hasDecidableEquality:FreeParts = record { _≟_ = decide-≡-FreeParts }

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  abstract-Partition : ∀{ϕs} -> Partition n ϕs μ -> ∑ λ η -> Partition n ϕs η ×-𝒰 (η ≡ μ)
  abstract-Partition μp = _ , μp , refl

  decide-≡-Partition : ∀{ϕs} -> (x y : Partition n ϕs μ) → isDecidable (x ≡ y)
  decide-≡-Partition (_ ⌟) (_ ⌟) = yes refl
  decide-≡-Partition (_⌟[_]⌞_ μ τ {η = η} x) y with inspect (abstract-Partition y)
  ... | (_ , _⌟[_]⌞_ μ τ₁ {η = η₁} y' , z) with≡ p with τ ≟ τ₁
  ... | no x₁ with qq <- (cancelₗ-◆ (μ) (cong-≡ fst p))
        = no λ {refl -> {!!}}
  ... | yes refl
    with refl <- (cancelₗ-◆ (μ ◆ τ) (cong-≡ fst p))
    with decide-≡-Partition y' x
  decide-≡-Partition (_⌟[_]⌞_ μ τ {η = η} x) .(_ ⌟[ τ ]⌞ y') | (.(μ ◆ τ ◆ η) , _⌟[_]⌞_ _ τ {η = η} y' , .refl-≡) with≡ refl-≡ | yes refl-≡ | no q = no λ {refl -> q refl}
  decide-≡-Partition (_⌟[_]⌞_ μ τ {η = η} .y') .(_ ⌟[ τ ]⌞ y') | (.(μ ◆ τ ◆ η) , _⌟[_]⌞_ _ τ {η = η} y' , .refl-≡) with≡ refl-≡ | yes refl-≡ | yes refl-≡ = yes refl

  instance
    hasDecidableEquality:Partition : ∀{ϕs} -> hasDecidableEquality (Partition n ϕs μ)
    hasDecidableEquality:Partition = record { _≟_ = decide-≡-Partition }

  decide-≡-2CellGen : {v : Visibility}
                   ->{a b : 0Cell G} {ϕs : FreeParts a b} {μ η : 1Cell G a b}
                   -> {μp : Partition n ϕs μ}
                   -> {ηp : Partition n ϕs η}
                   -> (ξ ζ : 2CellGen v ϕs μp ηp) -> isDecidable (ξ ≡ ζ)
  decide-≡-2CellGen (_ ⌟) (_ ⌟) = yes refl
  decide-≡-2CellGen (ϕ ⌟[ ξ ]⌞ ξ₁) (.ϕ ⌟[ ξ₂ ]⌞ ζ) with ξ ≟ ξ₂
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with decide-≡-2CellGen ξ₁ ζ
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl


  decide-≡-Some2CellGen : (x y : Some2CellGen v μ η) → isDecidable (x ≡ y)
  decide-≡-Some2CellGen x y with size x ≟ size y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with freeParts x ≟ freeParts y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with domPartition x ≟ domPartition y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with codPartition x ≟ codPartition y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with decide-≡-2CellGen (get x) (get y)
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:Some2CellGen : hasDecidableEquality (Some2CellGen v μ η)
    hasDecidableEquality:Some2CellGen = record { _≟_ = decide-≡-Some2CellGen }

  decide-≡-2Cell : (x y : 2Cell v μ η) → isDecidable (x ≡ y)
  decide-≡-2Cell [] [] = yes refl
  decide-≡-2Cell [] (x ∷ y) = no λ ()
  decide-≡-2Cell (x ∷ x₁) [] = no λ ()
  decide-≡-2Cell (_∷_ {η = η} x xs) (_∷_ {η = η₁} y ys) with η₁ ≟ η
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with x ≟ y
  ... | no p = no λ {refl -> p refl}
  ... | yes refl with decide-≡-2Cell xs ys
  ... | no p = no λ {refl -> p refl}
  ... | yes refl = yes refl

  instance
    hasDecidableEquality:2Cell : hasDecidableEquality (2Cell v μ η)
    hasDecidableEquality:2Cell = record { _≟_ = decide-≡-2Cell }




