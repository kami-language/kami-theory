
module KamiTheory.Data.UniqueSortedList.Instance.Preorder where

open import Agora.Conventions
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics
open import KamiTheory.Data.List.Definition

open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Properties





{-
module _ {A : StrictOrder 𝑖} where

  _∼-𝒫ᶠⁱⁿ_ : 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ A -> Set _
  _∼-𝒫ᶠⁱⁿ_ xs ys = xs ≡ ys

  instance
    isEquivRel:∼-𝒫ᶠⁱⁿ : isEquivRel _∼-𝒫ᶠⁱⁿ_
    isEquivRel:∼-𝒫ᶠⁱⁿ = isEquivRel:≡

  -- `𝒫ᶠⁱⁿ A` forms a setoid with strict equality
  instance
    isSetoid:𝒫ᶠⁱⁿ : isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = record { _∼_ = _∼-𝒫ᶠⁱⁿ_ }

  -- `𝒫ᶠⁱⁿ A` forms a preorder with _⊆_ as relation
  record _≤-𝒫ᶠⁱⁿ_ (U V : 𝒫ᶠⁱⁿ A) : Set 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ U ⟩ ⊆ ⟨ V ⟩
  open _≤-𝒫ᶠⁱⁿ_ {{...}} public

  refl-≤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤-𝒫ᶠⁱⁿ U
  refl-≤-𝒫ᶠⁱⁿ = incl (λ c x → x)

  _⟡-𝒫ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫ᶠⁱⁿ V -> V ≤-𝒫ᶠⁱⁿ W -> U ≤-𝒫ᶠⁱⁿ W
  incl p ⟡-𝒫ᶠⁱⁿ incl q = incl (λ c x → q c (p c x))

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : isPreorderData (𝒫ᶠⁱⁿ A) _≤-𝒫ᶠⁱⁿ_
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { refl-≤ = refl-≤-𝒫ᶠⁱⁿ
      ; _⟡_ = _⟡-𝒫ᶠⁱⁿ_
      ; transp-≤ = λ {refl refl x₂ → x₂}
      }

  -- `𝒫ᶠⁱⁿ A` has finite joins (least upper bounds / maximum / or)
  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = record { _≤_ = _≤-𝒫ᶠⁱⁿ_ }

  _∨-𝒫ᶠⁱⁿ_ : (U V : 𝒫ᶠⁱⁿ A) -> 𝒫ᶠⁱⁿ A
  (U since Us) ∨-𝒫ᶠⁱⁿ (V since Vs) = let a = (U ∪ V) in a since ∪-sorted Us Vs 

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = incl λ _ x₁ → x₁ ↯ ∉[]
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = incl ι₀-∪
                           ; ι₁-∨ = λ {as} → incl (ι₁-∪ {as = ⟨ as ⟩} )
                           ; [_,_]-∨ = λ { (incl u) (incl v) → incl [ u , v ]-∪}
                           }

-}

module _ {A : StrictOrder 𝑖} where

  _∼-𝒫ᶠⁱⁿ_ : 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ A -> Set _
  _∼-𝒫ᶠⁱⁿ_ xs ys = xs ≡ ys

  instance
    isEquivRel:∼-𝒫ᶠⁱⁿ : isEquivRel _∼-𝒫ᶠⁱⁿ_
    isEquivRel:∼-𝒫ᶠⁱⁿ = isEquivRel:≡

  -- `𝒫ᶠⁱⁿ A` forms a setoid with strict equality
  instance
    isSetoid:𝒫ᶠⁱⁿ : isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = record { _∼_ = _∼-𝒫ᶠⁱⁿ_ }

  -- `𝒫ᶠⁱⁿ A` forms a preorder with _⊆_ as relation
  record _≤-𝒫ᶠⁱⁿ_ (U V : 𝒫ᶠⁱⁿ A) : Set 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ U ⟩ ≼ ⟨ V ⟩
  open _≤-𝒫ᶠⁱⁿ_ {{...}} public

  refl-≤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤-𝒫ᶠⁱⁿ U
  refl-≤-𝒫ᶠⁱⁿ = incl refl-≼ --  incl (λ c x → x)

  _⟡-𝒫ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫ᶠⁱⁿ V -> V ≤-𝒫ᶠⁱⁿ W -> U ≤-𝒫ᶠⁱⁿ W
  incl p ⟡-𝒫ᶠⁱⁿ incl q = incl (p ◆-≼ q)
  -- (λ c x → q c (p c x))

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : isPreorderData (𝒫ᶠⁱⁿ A) _≤-𝒫ᶠⁱⁿ_
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { refl-≤ = refl-≤-𝒫ᶠⁱⁿ
      ; _⟡_ = _⟡-𝒫ᶠⁱⁿ_
      ; transp-≤ = λ {refl refl x₂ → x₂}
      }

  -- `𝒫ᶠⁱⁿ A` has finite joins (least upper bounds / maximum / or)
  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = record { _≤_ = _≤-𝒫ᶠⁱⁿ_ }

  _∨-𝒫ᶠⁱⁿ_ : (U V : 𝒫ᶠⁱⁿ A) -> 𝒫ᶠⁱⁿ A
  (U since Us) ∨-𝒫ᶠⁱⁿ (V since Vs) = let a = (U ∪ V) in a since ∪-sorted Us Vs 

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = incl []≼ -- λ _ x₁ → x₁ ↯ ∉[]
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = λ {as bs} -> incl (ι₀-∪-≼ {as = as} {bs = bs})
                           ; ι₁-∨ = λ {as bs} → incl (ι₁-∪-≼ {as = as} {bs = bs} )
                           ; [_,_]-∨ = λ {as bs cs} -> λ { (incl u) (incl v) → incl ([_,_]-∪-≼ {as = as} {bs} {cs} u v)}
                           }



_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ +-𝒰 ⟨ B ⟩ ′

𝟙-StrictOrder : ∀ {𝑖} -> StrictOrder _
𝟙-StrictOrder {𝑖} = ′ ⊤-𝒰 {𝑖} ′

-- nonempty finite power sets over A
-- module _ (A : StrictOrder 𝑖) where
--   NonEmptyUniqueSortedList : Set 𝑖
--   NonEmptyUniqueSortedList = ∑ λ (x : 𝒫ᶠⁱⁿ A) -> ¬ x ≡ ⊥

--   macro 𝒫₊ᶠⁱⁿ = #structureOn NonEmptyUniqueSortedList

-- module _ {A : StrictOrder 𝑖} where

--   record _∼-𝒫₊ᶠⁱⁿ_ (a b : 𝒫₊ᶠⁱⁿ A) : Set 𝑖 where
--     -- incl : fst a ∼ fst b

{-
  -- `𝒫₊ᶠⁱⁿ A` forms a setoid with strict equality
  instance
    isSetoid:𝒫ᶠⁱⁿ : isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = isSetoid:byId

  -- `𝒫₊ᶠⁱⁿ A` forms a preorder with _⊆_ as relation
  record _≤-𝒫ᶠⁱⁿ_ (U V : 𝒫ᶠⁱⁿ A) : Set 𝑖 where
    constructor incl
    field ⟨_⟩ : ⟨ U ⟩ ⊆ ⟨ V ⟩
  open _≤-𝒫ᶠⁱⁿ_ {{...}} public

  refl-≤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤-𝒫ᶠⁱⁿ U
  refl-≤-𝒫ᶠⁱⁿ = incl (λ c x → x)

  _⟡-𝒫ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫ᶠⁱⁿ V -> V ≤-𝒫ᶠⁱⁿ W -> U ≤-𝒫ᶠⁱⁿ W
  incl p ⟡-𝒫ᶠⁱⁿ incl q = incl (λ c x → q c (p c x))

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : isPreorderData (𝒫ᶠⁱⁿ A) _≤-𝒫ᶠⁱⁿ_
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { refl-≤ = refl-≤-𝒫ᶠⁱⁿ
      ; _⟡_ = _⟡-𝒫ᶠⁱⁿ_
      ; transp-≤ = λ {refl refl x₂ → x₂}
      }

  -- `𝒫ᶠⁱⁿ A` has finite joins (least upper bounds / maximum / or)
  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = record { _≤_ = _≤-𝒫ᶠⁱⁿ_ }
-}


----------------------------------------------------------
-- Morphisms in the category of strict orders
record isStrictOrderHom {𝑖 𝑗} {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} (hom : ⟨ A ⟩ -> ⟨ B ⟩) : Set (𝑖 ⊔ 𝑗) where
  field
    homPreserves : ∀ {a b : ⟨ A ⟩} → a < b → hom a < hom b

open isStrictOrderHom public

module _ (A : StrictOrder 𝑖) (B : StrictOrder 𝑗) where

  StrictOrderHom = (⟨ A ⟩ → ⟨ B ⟩) :& isStrictOrderHom {A = A} {B}



module _ {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} where
  map-isUniqueSorted : ∀{xs} -> (f : StrictOrderHom A B)
                       -> isUniqueSorted xs
                       -> isUniqueSorted (map-List ⟨ f ⟩ xs)
  map-isUniqueSorted f [] = []
  map-isUniqueSorted f [-] = [-]
  map-isUniqueSorted f (x ∷ us) = homPreserves (of f) x ∷ map-isUniqueSorted f us



  module _ (f : StrictOrderHom A B) where
    mapᵘ-𝒫ᶠⁱⁿ : 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
    mapᵘ-𝒫ᶠⁱⁿ (U since Up) = map-List ⟨ f ⟩ U since map-isUniqueSorted f Up

    mapᵘ-𝒫ᶠⁱⁿ-∈ : ∀{x} {U : 𝒫ᶠⁱⁿ A} -> x ∈ ⟨ U ⟩ -> ⟨ f ⟩ x ∈ ⟨ mapᵘ-𝒫ᶠⁱⁿ U ⟩
    mapᵘ-𝒫ᶠⁱⁿ-∈ here = here
    mapᵘ-𝒫ᶠⁱⁿ-∈ {U = (_ ∷ U@(_ ∷ _)) since (x ∷ Up)} (there p) = there (mapᵘ-𝒫ᶠⁱⁿ-∈ {U = U since Up} p)

    map-List-∈ : ∀{x} {U : List ⟨ A ⟩} -> x ∈ U -> ⟨ f ⟩ x ∈ map-List ⟨ f ⟩ U
    map-List-∈ = {!!}

    map-List-⊆ : {U V : List ⟨ A ⟩} -> U ⊆ V -> map-List ⟨ f ⟩ U ⊆ map-List ⟨ f ⟩ V
    map-List-⊆ {U = []} p = λ x ()
    map-List-⊆ {U = x ∷ U} p = λ
      { .(⟨ f ⟩ x) here → map-List-∈ (p _ here)
      ; x₁ (there y) → map-List-⊆ {U = U} (λ _ q -> p _ (there q)) _ y
      }


    mapᵘ-𝒫ᶠⁱⁿ-≤ : {U V : 𝒫ᶠⁱⁿ A} -> U ≤ V -> mapᵘ-𝒫ᶠⁱⁿ U ≤  mapᵘ-𝒫ᶠⁱⁿ V
    mapᵘ-𝒫ᶠⁱⁿ-≤ {U = U} {V} p = incl (from-⊆ (of (mapᵘ-𝒫ᶠⁱⁿ U)) (of (mapᵘ-𝒫ᶠⁱⁿ V)) (map-List-⊆ (into-⊆ ⟨ p ⟩)))



-- TODO Naming
module _ {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} where

  img : ∀ {𝑖 𝑗} {A : Set 𝑖} {B : Set 𝑗} → (f : A → B) → List A → List B
  img f [] = []
  img f (x ∷ x₁) = f x ∷ img f x₁

  img-soh : (f : StrictOrderHom A B) -> (as : List ⟨ A ⟩) → isUniqueSorted as → isUniqueSorted (img ⟨ f ⟩ as)
  img-soh (f since pf) [] x = []
  img-soh ff@(f since pf) (a ∷ .[]) [-] = [-]
  img-soh ff@(f since pf) (a ∷ (a₁ ∷ as)) (x ∷ x₁) = homPreserves pf x ∷ (img-soh ff (a₁ ∷ as) (popSort (x ∷ x₁)))
  
  Img-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
  Img-𝒫ᶠⁱⁿ f (as since pas) = let pimg = img-soh f as pas in (img ⟨ f ⟩ as) since pimg

  ∈img : ∀ {𝑖 𝑗} {A : Set 𝑖} {B : Set 𝑗} {a : A} {as : List A} → (f : A → B) → a ∈ as → f a ∈ img f as
  ∈img f here = here
  ∈img f (there x) = there (∈img f x)
{-
  map-img : ∀ {f : StrictOrderHom A B} {U V : List ⟨ A ⟩} -> U ⊆ V → img ⟨ f ⟩ U ⊆ img ⟨ f ⟩ V
  map-img stop = stop
  map-img (keep x) = keep (map-img x)
  map-img (drop x) = drop (map-img x)

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
-}


--------------------------------------------------
-- we show that isUniqueSorted is a proposition


module _ {𝑖} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  force-≡-isUniqueSorted : ∀{xs : List A} -> (p q : isUniqueSorted xs) -> p ≡ q
  force-≡-isUniqueSorted [] [] = refl
  force-≡-isUniqueSorted [-] [-] = refl
  force-≡-isUniqueSorted (x ∷ p) (y ∷ q) with force-≡ x y | force-≡-isUniqueSorted p q
  ... | refl | refl = refl

  instance
    isProp:isUniqueSorted : ∀{xs : List A} -> isProp (isUniqueSorted xs)
    isProp:isUniqueSorted = record { force-≡ = force-≡-isUniqueSorted }

module _ {A : StrictOrder 𝑖} where
  ⦗_⦘ : ⟨ A ⟩ -> 𝒫ᶠⁱⁿ A
  ⦗_⦘ a = (a ∷ []) since [-]


module _ {𝑖} {A : Set 𝑖} {{AP : hasStrictOrder A}} where

  ≰-singleton : ∀{p q : A} -> (¬ p ≡ q) -> ¬ _≤-𝒫ᶠⁱⁿ_ {A = A since AP} ⦗ p ⦘ ⦗ q ⦘
  ≰-singleton {p} {.p} p≢q (incl (take x)) = ⊥-elim (p≢q refl-≡)
  -- with ⟨ P ⟩ p here
  -- ... | here = p≢q refl


open Agora.Conventions hiding (¬_)


module _ {A : 𝒰 𝑖} where
  data _∉_ : A -> List A -> 𝒰 𝑖 where

module _ {A : StrictOrder 𝑖} where
  open Agora.Order.Preorder
  open Structure -- funnily this is needed for `of_` to work

  private instance _ = hasDecidableEquality:byStrictOrder {{of A}}


  decide-≤-𝒫ᶠⁱⁿ : ∀(u v : 𝒫ᶠⁱⁿ A) -> (¬ (u ≤ v)) +-𝒰 (u ≤ v)
  decide-≤-𝒫ᶠⁱⁿ u v with decide-≼ ⟨ u ⟩ ⟨ v ⟩ (of u) (of v)
  ... | yes p = right (incl p)
  ... | no ¬p = left (λ p -> ¬p ⟨ p ⟩)


  instance
    isDecidablePreorder:≤-𝒫ᶠⁱⁿ : isDecidablePreorder (𝒫ᶠⁱⁿ A)
    isDecidablePreorder:≤-𝒫ᶠⁱⁿ =
      -- record
      -- { _≰_ = λ xs ys -> ∑ λ x -> x ∈ ⟨ xs ⟩ ×-𝒰 (x ∉ ⟨ ys ⟩)
      -- ; impossible-≤ = {!!}
      -- ; decide-≤ = {!!}
      -- }
      record { decide-≤ = decide-≤-𝒫ᶠⁱⁿ }


record isFiniteStrictOrder (A : StrictOrder 𝑖): 𝒰 𝑖 where
  field All : 𝒫ᶠⁱⁿ A
  field intoAll : ∀{U : 𝒫ᶠⁱⁿ A} -> U ≤-𝒫ᶠⁱⁿ All

open isFiniteStrictOrder {{...}} public

module _ {A : StrictOrder 𝑖} {{_ : isFiniteStrictOrder A}} where
  ⊤-𝒫ᶠⁱⁿ : 𝒫ᶠⁱⁿ A
  ⊤-𝒫ᶠⁱⁿ = All

  terminal-⊤-𝒫ᶠⁱⁿ : ∀{U} -> U ≤ ⊤-𝒫ᶠⁱⁿ
  terminal-⊤-𝒫ᶠⁱⁿ = intoAll

  instance
    hasFiniteMeets:𝒫ᶠⁱⁿ : hasFiniteMeets (𝒫ᶠⁱⁿ A)
    hasFiniteMeets:𝒫ᶠⁱⁿ = record
      { ⊤ = {!!}
      ; terminal-⊤ = {!!}
      ; _∧_ = {!!}
      ; π₀-∧ = {!!}
      ; π₁-∧ = {!!}
      ; ⟨_,_⟩-∧ = {!!}
      }


instance
  isFiniteStrictOrder:𝔽 : ∀{n} -> isFiniteStrictOrder (𝔽 n)
  isFiniteStrictOrder:𝔽 = {!!}


