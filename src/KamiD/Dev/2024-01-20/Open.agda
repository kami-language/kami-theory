
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
    _∷_ : ∀{x a as} -> ¬ (x ≤ a) -> isIndependent x as -> isIndependent x (a ∷ as)

  data isIndependentBase : List X -> 𝒰 𝑗 where
    [] : isIndependentBase []
    [_by_]∷_ : ∀ x {xs} -> isIndependent x xs -> isIndependentBase xs -> isIndependentBase (x ∷ xs)


  private
    clearIB : X -> List X -> List X
    clearIB x [] = []
    clearIB x (y ∷ ys) with decide-≤ y x
    ... | just y≤x = clearIB x ys
    ... | left y≰x = y ∷ clearIB x ys

    insertIB : X -> List X -> List X
    insertIB x [] = x ∷ []
    insertIB x (y ∷ ys) with decide-≤ x y
    ... | just x≤y = x ∷ clearIB x ys
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = y ∷ ys
    ... | left y≰x = y ∷ insertIB x ys

    isIndependent:insertIB : ∀ z x ys -> ¬ (z ≤ x) -> isIndependent z ys -> isIndependent z (insertIB x ys)
    isIndependent:insertIB z x [] y≰x p = y≰x ∷ []
    isIndependent:insertIB z x (y ∷ ys) z≰x (p ∷ ps) with decide-≤ x y
    ... | just x≤y = {!!}
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = p ∷ ps -- isIndependent:insertIB _ _ _ {!!} {!ps!}
    ... | left y≰x = p ∷ (isIndependent:insertIB _ _ _ z≰x ps)

    isIndependentBase:insertIB : ∀ x xs -> isIndependentBase xs -> isIndependentBase (insertIB x xs)
    isIndependentBase:insertIB x [] p = [ x by [] ]∷ []
    isIndependentBase:insertIB x (y ∷ ys) q@([ _ by p ]∷ ps) with decide-≤ x y
    ... | just x≤y = [ {!!} by {!!} ]∷ {!!}
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = q
    ... | left y≰x = [ y by {!!} ]∷ {!!}

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


