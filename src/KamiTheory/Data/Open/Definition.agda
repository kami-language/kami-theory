
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.Open.Definition where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Order.StrictOrder.Instances.List
open import KamiTheory.Data.UniqueSortedList.Definition

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Sum.Definition

open import Data.List using (_++_ ; concatMap)

open Structure


-- we define lists of preorder elements which represent open subsets
-- in the alexandrov topology



-- module _ {X : 𝒰 _} {{_ : DecidablePreorder 𝑗 on X}} where
module IB {X : 𝒰 𝑖} (independent : X -> X -> 𝒰 𝑗) where

  -- independent a b = (a ≰ b) ×-𝒰 (b ≰ a)

  data isIndependent : X -> List X  -> 𝒰 (𝑖 , 𝑗) where
    [] : ∀{x} -> isIndependent x []
    _∷_ : ∀{x a as} -> independent x a -> isIndependent x as -> isIndependent x (a ∷ as)

  data isIndependentBase : List X -> 𝒰 (𝑖 , 𝑗) where
    [] : isIndependentBase []
    _∷_ : ∀ {x xs} -> isIndependent x xs -> isIndependentBase xs -> isIndependentBase (x ∷ xs)


module _ {X : 𝒰 𝑖} {{_ : isSetoid {𝑗} X}} {{_ : isPreorder 𝑘 ′ X ′}} {{_ : isDecidablePreorder ′ X ′}} where
  -- {{_ : DecidablePreorder 𝑗 on X}} where

  private
    _≰_ : X -> X -> 𝒰 _
    _≰_ a b = ¬(a ≤ b)

    impossible-≤ : ∀{a b} -> a ≰ b -> a ≤ b -> 𝟘-𝒰
    impossible-≤ p q = p q

  independent : X -> X -> 𝒰 _
  independent a b = (¬(a ≤ b)) ×-𝒰 (¬(b ≤ a))

  open IB independent public

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
    isIndependentBase:clearIB x (y ∷ ys) (p ∷ ps) with decide-≤ x y
    ... | just x≤y = isIndependentBase:clearIB x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = isIndependentBase:clearIB x ys ps
    ... | left y≰x =  isIndependent:clearIB y x ys p ∷ isIndependentBase:clearIB x ys ps

    isIndependent:insertIB : ∀ z x ys -> independent z x -> isIndependent z ys -> isIndependent z (insertIB x ys)
    isIndependent:insertIB z x [] q p = q ∷ []
    isIndependent:insertIB z x (y ∷ ys) q (p ∷ ps) with decide-≤ x y
    ... | just x≤y = q ∷ isIndependent:clearIB z x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = p ∷ ps
    ... | left y≰x = p ∷ (isIndependent:insertIB _ _ _ q ps)

    isIndependentBase:insertIB : ∀ x xs -> isIndependentBase xs -> isIndependentBase (insertIB x xs)
    isIndependentBase:insertIB x [] p =  [] ∷ []
    isIndependentBase:insertIB x (y ∷ ys) q@(p ∷ ps) with decide-≤ x y
    ... | just x≤y = isIndependent₂:clearIB x ys ∷ isIndependentBase:clearIB x ys ps
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = q
    ... | left y≰x =  isIndependent:insertIB y x ys (y≰x , x≰y) p ∷ isIndependentBase:insertIB x ys ps

  mergeIB : List X -> List X -> List X
  mergeIB [] ys = ys
  mergeIB (x ∷ xs) ys = mergeIB xs (insertIB x ys)

  isIndependentBase:mergeIB : ∀ xs -> ∀{ys} -> isIndependentBase ys -> isIndependentBase (mergeIB xs ys)
  isIndependentBase:mergeIB [] ysp = ysp
  isIndependentBase:mergeIB (x ∷ xs) ysp = isIndependentBase:mergeIB xs (isIndependentBase:insertIB _ _ ysp)

  --------------------------------------------------------------
  -- Preorder structure

  data _∈-IndependentBase_ : (x : X) -> (u : List X) -> 𝒰 (𝑘 , 𝑖) where
    take : ∀ {x y ys} -> y ≤ x -> x ∈-IndependentBase (y ∷ ys)
    next : ∀{x y ys} -> x ∈-IndependentBase ys -> x ∈-IndependentBase (y ∷ ys)

  private
    _∈-IB_ = _∈-IndependentBase_

  data _≤-IndependentBase_ : (u : List X) -> (v : List X) -> 𝒰 (𝑘 , 𝑖) where
    [] : ∀{vs} -> [] ≤-IndependentBase vs
    _∷_ : ∀{u us vs} -> u ∈-IndependentBase vs -> us ≤-IndependentBase vs -> (u ∷ us) ≤-IndependentBase vs

  private
    _≤-IB_ = _≤-IndependentBase_

  map-∈-IndependentBase : ∀{x u} -> x ∈ u -> x ∈-IndependentBase u
  map-∈-IndependentBase here = take refl-≤
  map-∈-IndependentBase (there p) = next (map-∈-IndependentBase p)

  lift-∈-IB : ∀{x y u} -> x ∈-IB u -> x ∈-IB (y ∷ u)
  lift-∈-IB (take x) = next (take x)
  lift-∈-IB (next p) = next (lift-∈-IB p)

  lift-≤-IB : ∀{u v x} -> u ≤-IB v -> u ≤-IB (x ∷ v)
  lift-≤-IB [] = []
  lift-≤-IB (x ∷ p) = lift-∈-IB x ∷ (lift-≤-IB p)

  refl-≤-IndependentBase : ∀{v : List X} -> v ≤-IB v
  refl-≤-IndependentBase {[]} = []
  refl-≤-IndependentBase {x ∷ v} = take refl-≤ ∷ lift-≤-IB refl-≤-IndependentBase

  trans-∈-IB : ∀{x y v} -> y ≤ x -> y ∈-IB v -> x ∈-IB v
  trans-∈-IB y≤x (take z≤y) = take (z≤y ⟡ y≤x)
  trans-∈-IB y≤x (next p) = next (trans-∈-IB y≤x p)

  trans-≤-IB : ∀{x v w} -> x ∈-IB v -> v ≤-IB w -> x ∈-IB w
  trans-≤-IB (take x) (q ∷ qs) = trans-∈-IB x q
  trans-≤-IB (next p) (q ∷ qs) = trans-≤-IB p qs

  _⟡-≤-IndependentBase_ : ∀{u v w} -> u ≤-IB v -> v ≤-IB w -> u ≤-IB w
  [] ⟡-≤-IndependentBase q = []
  (x ∷ p) ⟡-≤-IndependentBase q = (trans-≤-IB x q) ∷ (p ⟡-≤-IndependentBase q)

  --------------------------------------------------------------
  -- merge is join
  private
    ≤:byAllElements : ∀{u v} -> (∀{x} -> x ∈ u -> x ∈-IB v) -> u ≤-IB v
    ≤:byAllElements {u = []} F = []
    ≤:byAllElements {u = x ∷ u} F = F here ∷ (≤:byAllElements (λ p -> F (there p)))


  _∨-IndependentBase_ = mergeIB

  private
    insert-∈ : ∀ x u -> x ∈-IB insertIB x u
    insert-∈ x [] = take refl-≤
    insert-∈ x (y ∷ ys) with decide-≤ x y
    ... | just x≤y = take refl-≤
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = take y≤x
    ... | left y≰x = next (insert-∈ x ys)

    preserves-∈:clear : ∀ z x ys -> z ∈-IB ys -> (x ≰ z) -> ∀ x' -> x ≤ x' -> isIndependent x' ys -> z ∈-IB (clearIB x ys)
    preserves-∈:clear z x (y ∷ ys) (take y≤z) x≰z x' x≤x' (yp ∷ ysp) with decide-≤ x y
    ... | just x≤y = ⊥-elim (impossible-≤ x≰z (x≤y ⟡ y≤z))
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = ⊥-elim (impossible-≤ (snd yp) (y≤x ⟡ x≤x'))
    ... | left y≰x = take y≤z
    preserves-∈:clear z x (y ∷ ys) (next p) x≰z x' x≤x' (yp ∷ ysp) with decide-≤ x y
    ... | just x≤y = preserves-∈:clear z x ys p x≰z _ x≤x' ysp
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = preserves-∈:clear z x ys p x≰z _ x≤x' ysp
    ... | left y≰x = next (preserves-∈:clear z x ys p x≰z _ x≤x' ysp)

    preserves-∈:insert : ∀ z x ys -> z ∈-IB ys -> isIndependentBase ys -> z ∈-IB insertIB x ys
    preserves-∈:insert z x (y ∷ ys) p (yp ∷ ysp) with decide-≤ x y
    ... | just x≤y with decide-≤ x z
    ... | just x≤z = take x≤z
    ... | left x≰z with p
    ... | take y≤z = ⊥-elim (impossible-≤ x≰z (x≤y ⟡ y≤z))
    ... | next p = next (preserves-∈:clear z x ys p x≰z y x≤y yp)
    preserves-∈:insert z x (y ∷ ys) p (yp ∷ ysp)| left x≰y with decide-≤ y x
    ... | just y≤x = p
    ... | left y≰x with p
    ... | take p = take p
    ... | next p = next (preserves-∈:insert z x ys p ysp)

  preserves-∈-r:merge : ∀ x u v -> x ∈-IB v -> isIndependentBase v -> x ∈-IB (mergeIB u v)
  preserves-∈-r:merge x [] v p vp = p
  preserves-∈-r:merge x (u ∷ us) v p vp = preserves-∈-r:merge x us (insertIB u v) (preserves-∈:insert x u v p vp ) (isIndependentBase:insertIB u v vp)

  preserves-∈-l:merge : ∀ x u v -> x ∈-IB u -> isIndependentBase v -> x ∈-IB (mergeIB u v)
  preserves-∈-l:merge x (u ∷ us) vs (take u≤x) vp = preserves-∈-r:merge x us _ (trans-∈-IB u≤x (insert-∈ u vs)) (isIndependentBase:insertIB u vs vp)
  preserves-∈-l:merge x (u ∷ us) vs (next p) vp = preserves-∈-l:merge x us _ p (isIndependentBase:insertIB u vs vp)

  merge-ι₀ : ∀ v -> isIndependentBase v -> ∀ x u -> x ∈ u -> x ∈-IB mergeIB u v
  merge-ι₀ vs vp x (.x ∷ us) here = preserves-∈-r:merge x us ((insertIB x vs)) (insert-∈ x vs) (isIndependentBase:insertIB x vs vp)
  merge-ι₀ vs vp x (u ∷ us) (there p) = preserves-∈-l:merge x us (insertIB u vs) (map-∈-IndependentBase p) (isIndependentBase:insertIB u vs vp)

  merge-ι₁ : ∀ v -> isIndependentBase v -> ∀ x u -> x ∈-IB v -> x ∈-IB mergeIB u v
  merge-ι₁ v vp x [] p = p
  merge-ι₁ v vp x (u ∷ us) p = merge-ι₁ (insertIB u v) (isIndependentBase:insertIB u v vp) x us (preserves-∈:insert x u v p vp)

  ι₀-IndependentBase : ∀{u v : List X} -> isIndependentBase v -> u ≤-IB mergeIB u v
  ι₀-IndependentBase vp = ≤:byAllElements (λ p -> merge-ι₀ _ vp _ _ p)

  ι₁-IndependentBase : ∀{u v : List X} -> isIndependentBase v -> v ≤-IB mergeIB u v
  ι₁-IndependentBase {u = u} vp = ≤:byAllElements (λ p -> merge-ι₁ _ vp _ u (map-∈-IndependentBase p))

  intoIB : (u : List X) -> List X :& isIndependentBase -- (𝒪ᶠⁱⁿ⁻ʷᵏ X)
  intoIB u = mergeIB u [] since isIndependentBase:mergeIB u IB.[]


  private
    clear-≤ : ∀ x ys w -> x ∈-IB w -> ys ≤-IB w -> clearIB x ys ≤-IB w
    clear-≤ x [] w p q = []
    clear-≤ x (y ∷ ys) w x∈w yys≤w@(y∈w ∷ ys≤w) with decide-≤ x y
    ... | just x≤y = clear-≤ x ys w x∈w ys≤w
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = clear-≤ x ys w x∈w ys≤w
    ... | left y≰x = y∈w ∷ (clear-≤ x ys w x∈w ys≤w)

    insert-≤ : ∀ x v w -> x ∈-IB w -> v ≤-IB w -> insertIB x v ≤-IB w
    insert-≤ x [] w x∈w v≤w = x∈w ∷ []
    insert-≤ x (y ∷ ys) w x∈w yys≤w@(y∈w ∷ ys≤w) with decide-≤ x y
    ... | just x≤y = x∈w ∷ clear-≤ x ys w x∈w ys≤w
    ... | left x≰y with decide-≤ y x
    ... | just y≤x = yys≤w
    ... | left y≰x = y∈w ∷ insert-≤ x ys w x∈w ys≤w

  [_,_]-∨-IndependentBase : ∀{u v w : List X} -> u ≤-IB w -> v ≤-IB w -> mergeIB u v ≤-IB w
  [_,_]-∨-IndependentBase {u = []} p q = q
  [_,_]-∨-IndependentBase {u = x ∷ u} (x∈w ∷ p) q = [ p , insert-≤ x _ _ x∈w q ]-∨-IndependentBase


  decide-∈-IB : ∀ x as -> isDecidable (x ∈-IB as)
  decide-∈-IB x [] = no λ {()}
  decide-∈-IB x (a ∷ as) with decide-≤ a x
  ... | yes a≤x = yes (take a≤x)
  ... | no a≰x with decide-∈-IB x as
  ... | no x∉as = no λ { (take a≤x) → a≰x a≤x ; (next x∈as) → x∉as x∈as}
  ... | yes x∈as = yes (next x∈as)

  decide-≤-IB : ∀ as bs -> isDecidable (as ≤-IB bs)
  decide-≤-IB [] bs = yes []
  decide-≤-IB (x ∷ as) bs with decide-∈-IB x bs
  ... | no x∉bs = no λ { (x∈bs ∷ _) → x∉bs x∈bs}
  ... | yes x∈bs with decide-≤-IB as bs
  ... | no as≰bs = no λ { (_ ∷ as≤bs) → as≰bs as≤bs}
  ... | yes as≤bs = yes (x∈bs ∷ as≤bs)



IndependentBase : (X : DecidablePreorder 𝑖) -> 𝒰 _
IndependentBase X = List ⟨ X ⟩ :& isIndependentBase

macro
  𝒪ᶠⁱⁿ⁻ʷᵏ : DecidablePreorder 𝑖 -> _
  𝒪ᶠⁱⁿ⁻ʷᵏ X = #structureOn (IndependentBase X)

-- module _ {X' : 𝒰 _} {{_ : DecidablePreorder 𝑖 on X'}} where

module _ {X' : 𝒰 𝑖} {{_ : isSetoid {𝑗} X'}} {{_ : isPreorder 𝑘 ′ X' ′}} {{_ : isDecidablePreorder ′ X' ′}} where

  private
    X : DecidablePreorder _
    X = ′ X' ′

  record _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ (u v : 𝒪ᶠⁱⁿ⁻ʷᵏ X) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    constructor incl
    field ⟨_⟩ : ⟨ u ⟩ ≤-IndependentBase ⟨ v ⟩

  open _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ {{...}} public

  refl-≤-𝒪ᶠⁱⁿ⁻ʷᵏ : ∀{u : 𝒪ᶠⁱⁿ⁻ʷᵏ X} -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ u
  refl-≤-𝒪ᶠⁱⁿ⁻ʷᵏ = incl refl-≤-IndependentBase

  _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ : ∀{u v w : 𝒪ᶠⁱⁿ⁻ʷᵏ X} -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ v -> v ≤-𝒪ᶠⁱⁿ⁻ʷᵏ w -> u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ w
  _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ = λ p q -> incl (⟨ p ⟩ ⟡-≤-IndependentBase ⟨ q ⟩)

  _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ : (u v : 𝒪ᶠⁱⁿ⁻ʷᵏ X) -> 𝒰 _
  _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ u v = (u ≤-𝒪ᶠⁱⁿ⁻ʷᵏ v) ×-𝒰 (v ≤-𝒪ᶠⁱⁿ⁻ʷᵏ u)

  instance
    isEquivRel:_∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ : isEquivRel _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_
    isEquivRel:_∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ = isEquivRel:byPreorder _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ refl-≤-𝒪ᶠⁱⁿ⁻ʷᵏ _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_

  instance
    isSetoid:𝒪ᶠⁱⁿ⁻ʷᵏ : isSetoid (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    isSetoid:𝒪ᶠⁱⁿ⁻ʷᵏ = record { _∼_ = _∼-𝒪ᶠⁱⁿ⁻ʷᵏ_ }

  instance
    isPreorderData:≤-𝒪ᶠⁱⁿ⁻ʷᵏ : isPreorderData (𝒪ᶠⁱⁿ⁻ʷᵏ X) _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_
    isPreorderData:≤-𝒪ᶠⁱⁿ⁻ʷᵏ = record
      { refl-≤ = refl-≤-𝒪ᶠⁱⁿ⁻ʷᵏ
      ; _⟡_ = _⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ_
      ; transp-≤ = λ (p , q) (r , s) t -> (q ⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ t) ⟡-≤-𝒪ᶠⁱⁿ⁻ʷᵏ r
      }

  instance
    isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ : isPreorder _ (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ = record { _≤_ = _≤-𝒪ᶠⁱⁿ⁻ʷᵏ_ }

  decide-≤-𝒪ᶠⁱⁿ⁻ʷᵏ : ∀(a b : 𝒪ᶠⁱⁿ⁻ʷᵏ X) -> isDecidable (a ≤ b)
  decide-≤-𝒪ᶠⁱⁿ⁻ʷᵏ a b with decide-≤-IB ⟨ a ⟩ ⟨ b ⟩
  ... | no a≰b = no (λ p -> a≰b ⟨ p ⟩)
  ... | yes a≤b = yes (incl a≤b)

  instance
    isDecidablePreorder:𝒪ᶠⁱⁿ⁻ʷᵏ : isDecidablePreorder (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    isDecidablePreorder:𝒪ᶠⁱⁿ⁻ʷᵏ = record { decide-≤ = decide-≤-𝒪ᶠⁱⁿ⁻ʷᵏ }

  instance
    hasFiniteJoins:𝒪ᶠⁱⁿ⁻ʷᵏ : hasFiniteJoins (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    hasFiniteJoins:𝒪ᶠⁱⁿ⁻ʷᵏ = record
                              { ⊥ = [] since []
                              ; initial-⊥ = incl []
                              ; _∨_ = λ u v -> (mergeIB ⟨ u ⟩ ⟨ v ⟩ since isIndependentBase:mergeIB ⟨ u ⟩ (of v))
                              ; ι₀-∨ = incl (ι₀-IndependentBase it)
                              ; ι₁-∨ = λ {u} {v} -> incl (ι₁-IndependentBase {u = ⟨ u ⟩} it)
                              ; [_,_]-∨ = λ ϕ ψ -> incl [ ⟨ ϕ ⟩ , ⟨ ψ ⟩ ]-∨-IndependentBase
                              }

  instance
    hasDecidableEquality:𝒪ᶠⁱⁿ⁻ʷᵏ : hasDecidableEquality (𝒪ᶠⁱⁿ⁻ʷᵏ X)
    hasDecidableEquality:𝒪ᶠⁱⁿ⁻ʷᵏ = {!!}




---------------------------------------------
-- Building meets for 𝒪ᶠⁱⁿ⁻ʷᵏ
--
-- Idea: if we have (a ∨ b) ∧ (c ∨ d), this evaluates
-- to ((a ∨ b) ∧ c) ∨ ((a ∨ b) ∧ d)
-- to (a ∧ c) ∨ (b ∧ c) ∨ (a ∧ d) ∨ (b ∧ d)
--
-- this means that we require our underlying preorder to be
-- closed under unions

module _ {X : 𝒰 _} {{_ : DecidablePreorder 𝑖 on X}} {{_ : hasFiniteJoins ′ X ′}} where

  private
    restrictIB : X -> List X -> List X
    restrictIB a as = map-List (a ∨_) as

    _≤-IB_ = _≤-IndependentBase_
    _∈-IB_ = _∈-IndependentBase_

    π₀-∈,IB : ∀{x} -> ∀ a bs -> x ∈-IB restrictIB a bs -> (a ≤ x)
    π₀-∈,IB a (x ∷ bs) (take p) = (ι₀-∨ ⟡ p)
    π₀-∈,IB a (x ∷ bs) (next p) = π₀-∈,IB a bs p

    π₁-≤,IB : ∀ a bs -> restrictIB a bs ≤-IB bs
    π₁-≤,IB a [] = []
    π₁-≤,IB a (x ∷ bs) = (take ι₁-∨) ∷ lift-≤-IB (π₁-≤,IB a bs)

  intersectIB : List X -> List X -> List X
  intersectIB [] bs = []
  intersectIB (a ∷ as) bs = mergeIB (restrictIB a bs) (intersectIB as bs)

  isIndependentBase:intersectIB : ∀ as bs -> isIndependentBase (intersectIB as bs)
  isIndependentBase:intersectIB [] bs = IB.[]
  isIndependentBase:intersectIB (x ∷ as) bs = isIndependentBase:mergeIB (restrictIB x bs) (isIndependentBase:intersectIB as bs)

  head-≤ : ∀{x : X} {v xs : List X} -> (p : ∀{a} -> a ∈-IB v -> x ≤ a) -> v ≤-IB (x ∷ xs)
  head-≤ {v = []} p = []
  head-≤ {v = x ∷ v} p = (take (p (take refl-≤))) ∷ (head-≤ (λ q -> p (next q)))

  π₀-IB : ∀ as bs -> intersectIB as bs ≤-IB as
  π₀-IB [] bs = []
  π₀-IB (x ∷ as) bs =
    let p : restrictIB x bs ≤-IB (x ∷ as)
        p = head-≤ λ a∈as -> π₀-∈,IB x _ a∈as
        q : intersectIB as bs ≤-IB (x ∷ as)
        q = lift-≤-IB (π₀-IB as bs)
    in [ p , q ]-∨-IndependentBase

  π₁-IB : ∀ as bs -> intersectIB as bs ≤-IB bs
  π₁-IB [] bs = []
  π₁-IB (x ∷ as) bs =
    let p : restrictIB x bs ≤-IB (bs)
        p = π₁-≤,IB x bs
        q : intersectIB as bs ≤-IB bs
        q = π₁-IB as bs
    in [ p , q ]-∨-IndependentBase

  terminal-IB : ∀ (v : List X) -> v ≤-IB (⊥ ∷ [])
  terminal-IB [] = []
  terminal-IB (x ∷ v) = (take initial-⊥) ∷ (terminal-IB v)

  isIndependentBase:terminal-IB : isIndependentBase {X = X} (⊥ ∷ [])
  isIndependentBase:terminal-IB = IB.[] IB.∷ IB.[]

  preserves-∈:restrictIB : ∀{a x bs} -> x ∈-IB bs -> a ≤ x -> x ∈-IB restrictIB a bs
  preserves-∈:restrictIB (take b≤x) a≤x = take [ a≤x , b≤x ]-∨
  preserves-∈:restrictIB (next p) q = next (preserves-∈:restrictIB p q)

  preserves-∈:intersectIB : ∀{x : X} -> ∀{as bs : List X} -> x ∈-IB as -> x ∈-IB bs -> x ∈-IB intersectIB as bs
  preserves-∈:intersectIB {x = x} {as = a ∷ as} {bs} (take a≤x) x∈bs = preserves-∈-l:merge x (restrictIB a bs) (intersectIB as bs) (preserves-∈:restrictIB x∈bs a≤x) (isIndependentBase:intersectIB as bs)
  preserves-∈:intersectIB {x = x} {as = a ∷ as} {bs} (next x∈as) x∈bs = preserves-∈-r:merge x (restrictIB a bs) (intersectIB as bs) (preserves-∈:intersectIB x∈as x∈bs) ((isIndependentBase:intersectIB as bs))

  ⟨_,_⟩-∧-IndependentBase : ∀{u v w : List X} -> u ≤-IB v -> u ≤-IB w -> u ≤-IB intersectIB v w
  ⟨_,_⟩-∧-IndependentBase {u = []} {v = v} p q = []
  ⟨_,_⟩-∧-IndependentBase {u = u ∷ us} {v = v} (u∈v ∷ us≤v) (u∈w ∷ us≤w) = preserves-∈:intersectIB u∈v u∈w ∷ ⟨_,_⟩-∧-IndependentBase us≤v us≤w

  instance
    hasFiniteMeets:𝒪ᶠⁱⁿ⁻ʷᵏ : hasFiniteMeets (𝒪ᶠⁱⁿ⁻ʷᵏ ′ X ′)
    hasFiniteMeets:𝒪ᶠⁱⁿ⁻ʷᵏ = record
      { ⊤ = ⊥ ∷ [] since isIndependentBase:terminal-IB
      ; terminal-⊤ = incl (terminal-IB _)
      ; _∧_ = λ u v -> intersectIB ⟨ u ⟩ ⟨ v ⟩ since isIndependentBase:intersectIB ⟨ u ⟩ ⟨ v ⟩
      ; π₀-∧ = incl (π₀-IB _ _)
      ; π₁-∧ = λ {a b} -> incl (π₁-IB ⟨ a ⟩ ⟨ b ⟩)
      ; ⟨_,_⟩-∧ = λ ϕ ψ -> incl ⟨ ⟨ ϕ ⟩ , ⟨ ψ ⟩ ⟩-∧-IndependentBase
      }




{-
module TestExample where

  open import Data.Fin using (#_ ; zero ; suc)
  P : 𝒰 _
  P = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 3))

  uu : P
  uu = (⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  vv : P
  vv = (⦗ # 1 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  ww : P
  ww = (⦗ # 2 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])

  all = uu ∨ vv ∨ ww

  res = intersectIB (⟨ uu ⟩) (⟨ vv ⟩)

-}


module _ {X' : 𝒰 _} {{_ : DecidablePreorder 𝑖 on X'}}
          {Y' : 𝒰 _} {{_ : DecidablePreorder 𝑗 on Y'}} where

  private
    X : DecidablePreorder 𝑖
    X = ′ X' ′

  private
    Y : DecidablePreorder 𝑗
    Y = ′ Y' ′

  bind-𝒪ᶠⁱⁿ⁻ʷᵏ : (⟨ X ⟩ -> 𝒪ᶠⁱⁿ⁻ʷᵏ Y) -> 𝒪ᶠⁱⁿ⁻ʷᵏ X -> 𝒪ᶠⁱⁿ⁻ʷᵏ Y
  bind-𝒪ᶠⁱⁿ⁻ʷᵏ f x = intoIB (concatMap (λ x -> ⟨ f x ⟩) ⟨ x ⟩)


{-
open import Data.Fin.Base

module _ where

  open import KamiTheory.Dev.2024-01-20.StrictOrder.Base
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
