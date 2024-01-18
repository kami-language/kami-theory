{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-14.UniqueSortedList where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List.Base using (List; []; _∷_)

--------------------------------------------------

_↯_ : ∀ {𝒶 ℓ : Level} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → Dec (x ≡ y)

open hasDecidableEquality {{...}} public

--------------------------------------------------

data Tri {𝑖} (A : Set 𝑖) (B : Set 𝑖) (C : Set 𝑖) : Set 𝑖 where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≡ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C


record hasStrictOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _<_ : A → A → Set 𝑖
    irrefl< : ∀ {a : A} → ¬ (a < a)
    -- asym< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    trans< : ∀ {a b c : A} → a < b → b < c → a < c
    conn< : ∀ (a b : A) → Tri (a < b) (a ≡ b) (b < a)

open hasStrictOrder {{...}}

--------------------------------------------------

module _ {𝑖 : Level} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  data UniqueSorted : List A → Set 𝑖 where
    []  : UniqueSorted []
    [_] : ∀ x → UniqueSorted (x ∷ [])
    _∷_ : ∀ {x y xs} → x < y → UniqueSorted (y ∷ xs) → UniqueSorted (x ∷ y ∷ xs)

  popSort : (a : A) → (as : List A) → UniqueSorted (a ∷ as) → UniqueSorted as
  popSort a .[] [ .a ] = []
  popSort a .(_ ∷ _) (x ∷ x₁) = x₁

  infix 4 _∈_
  
  data _∈_ : (a : A) → (as : List A) → Set (lsuc 𝑖) where
    here : ∀ {a : A} {as : List A} → a ∈ (a ∷ as)
    there : ∀ {a b : A} {as : List A} → a ∈ as → a ∈ (b ∷ as)

  ∉[] : ∀ {a : A} → ¬ (a ∈ [])
  ∉[] {a} ()


  _∈?_ : {{_ : hasDecidableEquality A}} → (a : A) → (as : List A) → Dec (a ∈ as)
  a ∈? [] = no λ ()
  a ∈? (b ∷ as) with (a ≟ b) | a ∈? as
  ...               | yes refl | _ = yes here
  ...               | no _ | yes a∈as = yes (there a∈as)
  ...               | no a≠b | no a∉as = no λ { here → refl ↯ a≠b; (there a∈as) → a∈as ↯ a∉as}

  data _⊆_ : (as bs : List A) → Set (lsuc 𝑖) where
    allIn : ∀ {as bs : List A} → (all : ∀ (c : A) → c ∈ as → c ∈ bs) → as ⊆ bs
    
  _⊆?_ : {{_ : hasDecidableEquality A}} → (as bs : List A) → Dec (as ⊆ bs)
  [] ⊆? bs = yes (allIn (λ c ()))
  (a ∷ as) ⊆? [] = no λ { (allIn x) → x a here ↯ ∉[]}
  (a ∷ as) ⊆? bs with a ∈? bs | as ⊆? bs
  ... | yes a∈bs | yes (allIn f) = yes (allIn (λ { c here → a∈bs ; c (there x) → f c x}))
  ... | yes a∈bs | no as⊈bs = no (λ { (allIn f) → (allIn λ c c∈as → f c (there c∈as)) ↯ as⊈bs})
  ... | no a∉bs | _ = no λ { (allIn all) → all a here ↯ a∉bs}

  insert : {{_ : hasDecidableEquality A}} (a : A) → (as : List A) → UniqueSorted as → Σ _ UniqueSorted
  insert a .[] [] = (a ∷ []) , [ a ]
  insert a .(b ∷ []) [ b ] with conn< a b
  ... | tri< a<b _ _ = (a ∷ b ∷ []) , (a<b ∷ [ b ])
  ... | tri≡ _ a≡b _ = (a ∷ []) , [ a ]
  ... | tri> _ _ a>b = (b ∷ a ∷ []) , (a>b ∷ [ a ])
  insert a (b ∷ c ∷ bs) (pb ∷ pbs) with conn< a b
  ... | tri< a<b a≢b a≯b = a ∷ b ∷ c ∷ bs , (a<b ∷ (pb ∷ pbs))
  ... | tri≡ a≮b a≡b a≯b = b ∷ c ∷ bs , (pb ∷ pbs)
  ... | tri> a≮b a≢b a>b = insert a (c ∷ bs) pbs

  _∪_ : {{_ : hasDecidableEquality A}} (as bs : List A) → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → Σ _ UniqueSorted
  ([] ∪ bs) {pb = pb} = bs , pb
  (as ∪ []) {pa = pa} = as , pa
  ((a ∷ as) ∪ bs) {pa = pa} {pb = pb} = let
      abs , pab = insert a bs pb
    in (as ∪ abs) {pa = popSort a as pa} {pb = pab}

--------------------------------------------------
-- now here comes the weird stuff


open import Agora.Conventions using (
  _:&_; ⟨_⟩; _since_; ′_′; _on_;
  #structureOn; isSetoid; isSetoid:byId; _isUniverseOf[_]_;  _isUniverseOf[_]_:byBase)
open import Agora.Order.Preorder using (isPreorderData; isPreorder; isPreorder:byDef)


instance
  _isUniverseOf[_]_:List : ∀ {𝑖} {A : Set 𝑖} -> (List A) isUniverseOf[ _ ] (List A)
  _isUniverseOf[_]_:List = _isUniverseOf[_]_:byBase


module _ {𝑖 : Level} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  StrictOrder : Set (lsuc 𝑖)
  StrictOrder = (Set 𝑖) :& hasStrictOrder

  UniqueSortedList : (A : StrictOrder) -> Set 𝑖
  UniqueSortedList A = List ⟨ A ⟩ :& UniqueSorted

  -- The fancy name for UniqueSortedList: finite power set over A
  macro
    𝒫ᶠⁱⁿ : StrictOrder -> _
    𝒫ᶠⁱⁿ A = #structureOn (UniqueSortedList A)


  instance
    isSetoid:𝒫ᶠⁱⁿ : ∀ {A : StrictOrder} → isSetoid (𝒫ᶠⁱⁿ A)
    isSetoid:𝒫ᶠⁱⁿ = isSetoid:byId

  instance
    isPreorderData:≤-𝒫ᶠⁱⁿ : ∀ {A : StrictOrder} → isPreorderData (𝒫ᶠⁱⁿ A) {!!}
    isPreorderData:≤-𝒫ᶠⁱⁿ = record
      { reflexive = {!!}
      ; _⟡_ = {!!}
      ; transp-≤ = {!!}
      }
 
{-
  instance
    isPreorder:𝒫ᶠⁱⁿ : isPreorder _ (𝒫ᶠⁱⁿ A)
    isPreorder:𝒫ᶠⁱⁿ = isPreorder:byDef _≤-𝒫ᶠⁱⁿ_

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = {!!}
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = {!!}
                           ; ι₁-∨ = {!!}
                           ; [_,_]-∨ = {!!}
                           }

postulate
  -- TODO: Naming unclear
  instance hasStrictOrder:⋆ : ∀{A B} -> {{_ : StrictOrder on A}} -> {{_ : StrictOrder on B}} -> hasStrictOrder (A ⊎ B)
  -- instance hasStrictOrder:𝟙 : hasStrictOrder 𝟙

  -- instance hasStrictOrder:𝔽 : hasStrictOrder ℓ₀ (𝔽 n)


_⋆-StrictOrder_ : StrictOrder -> StrictOrder -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ ⊎ ⟨ B ⟩ ′


𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ 𝟙-𝒰 ′
-


module _ (A : StrictOrder) (B : StrictOrder) where
  postulate
    hasStrictOrderHom : ∀ {𝑖} {A B : Set 𝑖} (f : ⟨ A ⟩ -> ⟨ B ⟩) -> Set 𝑖

  StrictOrderHom = _ :& hasStrictOrderHom


-- TODO Naming
module _ {A B : StrictOrder} where
  postulate
    Img-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
    map-Img-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V

  postulate
    PreImg-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ B -> 𝒫ᶠⁱⁿ A
    map-PreImg-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V


-- postulate
--  instance hasStrictOrderHom:right : {A B : StrictOrder} -> hasStrictOrderHom B (A ⋆-StrictOrder B) right
-}

