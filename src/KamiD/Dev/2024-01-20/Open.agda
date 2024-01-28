
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


