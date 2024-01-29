
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Open where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.StrictOrder.Base
open import KamiD.Dev.2024-01-20.UniqueSortedList
open import KamiD.Dev.2024-01-20.StrictOrder.Instances.List
open import KamiD.Dev.2024-01-20.Basics

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Sum.Definition

open import Data.List using (_++_)


-- we define lists of preorder elements which represent open subsets
-- in the alexandrov topology



module _ {X : 𝒰 _} {{_ : DecidablePreorder 𝑗 on X}} where
  data isIndependent : X -> List X  -> 𝒰 𝑗 where
    [] : ∀{x} -> isIndependent x []
    _∷_ : ∀{x a as} -> ¬ (x ≤ a) ×-𝒰 ¬ (a ≤ x) -> isIndependent x as -> isIndependent x (a ∷ as)

  data isIndependentBase : List X -> 𝒰 𝑗 where
    [] : isIndependentBase []
    [_by_]∷_ : ∀ x {xs} -> isIndependent x xs -> isIndependentBase xs -> isIndependentBase (x ∷ xs)


  private
    clearIB : X -> List X -> List X
    clearIB x [] = []
    clearIB x (y ∷ ys) with decide-≤ x y
    ... | just x≤y = clearIB x ys
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = clearIB x ys
    ... | left y≰x = y ∷ clearIB x ys

    insertIB : X -> List X -> List X
    insertIB x [] = x ∷ []
    insertIB x (y ∷ ys) with decide-≤ x y
    ... | just x≤y = x ∷ clearIB x ys
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = y ∷ ys
    ... | left y≰x = y ∷ insertIB x ys

    isIndependent:clearIB : ∀ z x ys -> isIndependent z ys -> isIndependent z (clearIB x ys)
    isIndependent:clearIB z x [] p = p
    isIndependent:clearIB z x (y ∷ ys) (p ∷ ps) with decide-≤ x y
    ... | just x≤y = isIndependent:clearIB z x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = isIndependent:clearIB z x ys ps
    ... | left y≰x = p ∷ (isIndependent:clearIB z x ys ps)

    isIndependent₂:clearIB : ∀ x ys -> isIndependent x (clearIB x ys)
    isIndependent₂:clearIB x [] = []
    isIndependent₂:clearIB x (y ∷ ys) with decide-≤ x y
    ... | just x≤y = isIndependent₂:clearIB x ys
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = isIndependent₂:clearIB x ys
    ... | left y≰x = x≰y , y≰x ∷ isIndependent₂:clearIB x ys

    isIndependentBase:clearIB : ∀ x ys -> isIndependentBase ys -> isIndependentBase (clearIB x ys)
    isIndependentBase:clearIB x [] p = []
    isIndependentBase:clearIB x (y ∷ ys) ([ _ by p ]∷ ps) with decide-≤ x y
    ... | just x≤y = isIndependentBase:clearIB x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = isIndependentBase:clearIB x ys ps
    ... | left y≰x = [ _ by isIndependent:clearIB y x ys p ]∷ isIndependentBase:clearIB x ys ps

    isIndependent:insertIB : ∀ z x ys -> ¬ (z ≤ x) ×-𝒰 ¬ (x ≤ z) -> isIndependent z ys -> isIndependent z (insertIB x ys)
    isIndependent:insertIB z x [] q p = q ∷ []
    isIndependent:insertIB z x (y ∷ ys) q (p ∷ ps) with decide-≤ x y
    ... | just x≤y = q ∷ isIndependent:clearIB z x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = p ∷ ps
    ... | left y≰x = p ∷ (isIndependent:insertIB _ _ _ q ps)

    isIndependentBase:insertIB : ∀ x xs -> isIndependentBase xs -> isIndependentBase (insertIB x xs)
    isIndependentBase:insertIB x [] p = [ x by [] ]∷ []
    isIndependentBase:insertIB x (y ∷ ys) q@([ _ by p ]∷ ps) with decide-≤ x y
    ... | just x≤y = [ x by isIndependent₂:clearIB x ys ]∷ isIndependentBase:clearIB x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = q
    ... | left y≰x = [ y by isIndependent:insertIB y x ys (y≰x , x≰y) p ]∷ isIndependentBase:insertIB x ys ps

  mergeIB : List X -> List X -> List X
  mergeIB [] ys = ys
  mergeIB (x ∷ xs) ys = mergeIB xs (insertIB x ys)

  data _∈-IndependentBase_ : (x : X) -> (u : List X) -> 𝒰 𝑗 where
    take : ∀{x y ys} -> x ≤ y -> x ∈-IndependentBase (y ∷ ys)
    next : ∀{x y ys} -> x ∈-IndependentBase ys -> x ∈-IndependentBase (y ∷ ys)

  private
    _∈-IB_ = _∈-IndependentBase_

  data _≤-IndependentBase_ : (u : List X) -> (v : List X) -> 𝒰 𝑗 where
    [] : ∀{vs} -> [] ≤-IndependentBase vs
    _∷_ : ∀{u us vs} -> u ∈-IndependentBase vs -> us ≤-IndependentBase vs -> (u ∷ us) ≤-IndependentBase vs

  -- _≤-IndependentBase_ : (u : List X) -> (v : List X) -> 𝒰 _
  -- _≤-IndependentBase_ u v = ∀ x -> x ∈ u -> x ∈-IndependentBase v

  private
    _≤-IB_ = _≤-IndependentBase_

  map-∈-IndependentBase : ∀{x u} -> x ∈ u -> x ∈-IndependentBase u
  map-∈-IndependentBase here = take reflexive
  map-∈-IndependentBase (there p) = next (map-∈-IndependentBase p)

  lift-∈-IB : ∀{x y u} -> x ∈-IB u -> x ∈-IB (y ∷ u)
  lift-∈-IB (take x) = next (take x)
  lift-∈-IB (next p) = next (lift-∈-IB p)

  lift-≤-IB : ∀{u v x} -> u ≤-IB v -> u ≤-IB (x ∷ v)
  lift-≤-IB [] = []
  lift-≤-IB (x ∷ p) = lift-∈-IB x ∷ (lift-≤-IB p)

  reflexive-≤-IndependentBase : ∀{v : List X} -> v ≤-IB v
  reflexive-≤-IndependentBase {[]} = []
  reflexive-≤-IndependentBase {x ∷ v} = take reflexive ∷ lift-≤-IB reflexive-≤-IndependentBase

  trans-∈-IB : ∀{x y v} -> x ≤ y -> y ∈-IB v -> x ∈-IB v
  trans-∈-IB x≤y (take y≤z) = take (x≤y ⟡ y≤z)
  trans-∈-IB x≤y (next p) = next (trans-∈-IB x≤y p)

  trans-≤-IB : ∀{x v w} -> x ∈-IB v -> v ≤-IB w -> x ∈-IB w
  trans-≤-IB (take x) (q ∷ qs) = trans-∈-IB x q
  trans-≤-IB (next p) (q ∷ qs) = trans-≤-IB p qs

  _⟡-≤-IndependentBase_ : ∀{u v w} -> u ≤-IB v -> v ≤-IB w -> u ≤-IB w
  [] ⟡-≤-IndependentBase q = []
  (x ∷ p) ⟡-≤-IndependentBase q = (trans-≤-IB x q) ∷ (p ⟡-≤-IndependentBase q)


IndependentBase : (X : DecidablePreorder 𝑖) -> 𝒰 _
IndependentBase X = List ⟨ X ⟩ :& isIndependentBase

macro
  𝒪ᶠⁱⁿ⁻ʷᵏ : DecidablePreorder 𝑖 -> _
  𝒪ᶠⁱⁿ⁻ʷᵏ X = #structureOn (IndependentBase X)

module _ {X : DecidablePreorder 𝑖} where

  record _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ (u v : 𝒪ᶠⁱⁿ⁻ʷᵏ X) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ u ⟩ ≤-IndependentBase ⟨ v ⟩

  open _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ {{...}} public

  reflexive-≤-𝒪ᶠⁱⁿ⁻ʷᵏ : ∀{u : 𝒪ᶠⁱⁿ⁻ʷᵏ X} -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ u
  reflexive-≤-𝒪ᶠⁱⁿ⁻ʷᵏ = incl reflexive-≤-IndependentBase

  _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ : ∀{u v w : 𝒪ᶠⁱⁿ⁻ʷᵏ X} -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ v -> v ≤-𝒪ᶠⁱⁿ⁻ʷᵏ w -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ w
  _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ = λ p q -> incl (⟨ p ⟩ ⟡-≤-IndependentBase ⟨ q ⟩)

  _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ : (u v : 𝒪ᶠⁱⁿ⁻ʷᵏ X) -> 𝒰 𝑖
  _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ u v = (u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ v) ×-𝒰 (v ≤-𝒪ᶠⁱⁿ⁻ʷᵏ u)

  instance
    isEquivRel:_∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ : isEquivRel _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_
    isEquivRel:_∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ = isEquivRel:byPreorder _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ reflexive-≤-𝒪ᶠⁱⁿ⁻ʷᵏ _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_

  instance
    isSetoid:𝒪ᶠⁱⁿ⁻ʷᵏ : isSetoid (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    isSetoid:𝒪ᶠⁱⁿ⁻ʷᵏ = record { _∼_ = _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ }

  instance
    isPreorderData:≤-𝒪ᶠⁱⁿ⁻ʷᵏ : isPreorderData (𝒪ᶠⁱⁿ⁻ʷᵏ X) _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_
    isPreorderData:≤-𝒪ᶠⁱⁿ⁻ʷᵏ = record
      { reflexive = reflexive-≤-𝒪ᶠⁱⁿ⁻ʷᵏ
      ; _⟡_ = _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_
      ; transp-≤ = λ (p , q) (r , s) t -> (q ⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ t) ⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ r
      }

  instance
    isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ : isPreorder _ (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ = isPreorder:byDef _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_


{-
open import Data.Fin.Base

module _ where

  open import KamiD.Dev.2024-01-20.StrictOrder.Base
  open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
  open import Data.Nat hiding (_! ; _+_ ; _≤_)

  l01 : List (𝒫ᶠⁱⁿ (𝔽 3))
  l01 = (⦗ # 0 ⦘ ∨ ⦗ # 1 ⦘ ∨ ⦗ # 2 ⦘) ∷ []

  l0 : List (𝒫ᶠⁱⁿ (𝔽 3))
  l0 = ⦗ # 0 ⦘ ∷ ⦗ # 1 ⦘ ∨ ⦗ # 2 ⦘ ∷ ⦗ # 1 ⦘ ∷ []

  res = mergeIB l0 l01

  u v : List (𝒫ᶠⁱⁿ (𝔽 3))
  u = ⦗ # 0 ⦘ ∨ ⦗ # 2 ⦘ ∷ ⦗ # 1 ⦘ ∷ []

  v = ⦗ # 2 ⦘ ∷ []

  res2 = mergeIB v u
-}

