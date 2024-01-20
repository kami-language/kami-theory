{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-14.UniqueSortedList where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

--------------------------------------------------

_↯_ : ∀ {𝒶 ℓ : Level} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → Dec (x ≡ y)

open hasDecidableEquality {{...}} public

--------------------------------------------------

data Tri {𝑖} (A : Set 𝑖) (B : Set 𝑖) (C : Set 𝑖) : Set 𝑖 where
  tri< : (a<b :   A) (a≢b : ¬ B) (a≯b : ¬ C) → Tri A B C
  tri≡ : (a≮b : ¬ A) (a≡b :   B) (a≯b : ¬ C) → Tri A B C
  tri> : (a≮b : ¬ A) (a≢b : ¬ B) (a>b :   C) → Tri A B C


record hasStrictOrder {𝑖} (A : Set 𝑖) : Set (lsuc 𝑖) where
  field
    _<_ : A → A → Set 𝑖
    irrefl< : ∀ {a : A} → ¬ (a < a)
    -- asym< : ∀ {a b : A} → a < b → ¬ (b < a) -- follows from trans and iref
    trans< : ∀ {a b c : A} → a < b → b < c → a < c
    conn< : ∀ (a b : A) → Tri (a < b) (a ≡ b) (b < a)

open hasStrictOrder {{...}}

--------------------------------------------------
-- instances

open import Data.Fin using (Fin)
open import Data.Unit using (⊤)

-- Fin n has a strict order
instance
  hasStrictOrder:𝔽 : ∀{n} -> hasStrictOrder (Fin n)
  hasStrictOrder:𝔽 = {!!}

-- The sum of two types has a strict order by "concatenating" them
instance
  hasStrictOrder:⊎ : ∀{𝑖 𝑗} -> ∀{A : Set 𝑖} {B : Set 𝑗}
                     -> {{_ : hasStrictOrder A}} {{_ : hasStrictOrder B}}
                     -> hasStrictOrder (A ⊎ B)
  hasStrictOrder:⊎ = {!!}

-- The unit type has a strict order
instance
  hasStrictOrder:Unit : hasStrictOrder ⊤
  hasStrictOrder:Unit = {!!}


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

module _ {𝑖 : Level} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  data UniqueSorted : List A → Set 𝑖 where
    []  : UniqueSorted []
    [_] : ∀ x → UniqueSorted (x ∷ [])
    _∷_ : ∀ {x y xs} → x < y → UniqueSorted (y ∷ xs) → UniqueSorted (x ∷ y ∷ xs)

  popSort : {a : A} → {as : List A} → UniqueSorted (a ∷ as) → UniqueSorted as
  popSort {a} {.[]} [ .a ] = []
  popSort {a} {.(_ ∷ _)} (x ∷ x₁) = x₁



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
  insert a (b ∷ as) with conn< a b
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
  allSort [ _ ] = []
  allSort (x ∷ [ _ ]) = all∷ x []
  allSort (a<z ∷ (z<y ∷ usyxs)) = all∷ a<z (allSort (trans< {𝑖} {A} a<z z<y ∷ usyxs))
  
  sortAll : {a : A} → {as : List A} → a <* as → UniqueSorted as → UniqueSorted (a ∷ as)
  sortAll {a} [] x₁ = [ a ]
  sortAll (x ∷ x₂) x₁ = x ∷ x₁
  
  insertAll : {a c : A} → {as : List A} → c < a → c <* as → UniqueSorted as → c <* (insert a as)
  insertAll {as = []} x x₁ usas = x ∷ x₁
  insertAll {a} {c} {b ∷ as} c<a (c<b ∷ c<*as) usas with conn< a b
  ... | tri< _ _ _ = c<a ∷ (c<b ∷ c<*as)
  ... | tri≡ _ _ _ = (c<b ∷ c<*as)
  ... | tri> a≮b a≢b a>b = let
      c<*aas = insertAll c<a c<*as (popSort usas)
    in all∷ c<b c<*aas

  insertSorted : {a : A} → {as : List A} → UniqueSorted as → UniqueSorted (insert a as)
  insertSorted {a} {[]} usas = [ a ]
  insertSorted {a} {(b ∷ as)} ([ bb ]) with conn< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ [ b ]
  ... | tri≡ a≮b a≡b a≯b = [ b ]
  ... | tri> a≮b a≢b a>b = a>b ∷ [ a ]
  insertSorted {a} {(b ∷ as)} (b<y ∷ usas) with conn< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ (b<y ∷ usas)
  ... | tri≡ a≮b a≡b a≯b = (b<y ∷ usas)
  ... | tri> a≮b a≢b a>b = let
      b<*yas = allSort (b<y ∷ usas)
      b<*y∷xs = insertAll a>b b<*yas usas
      ins = insertSorted usas
    in sortAll b<*y∷xs ins


  ∈-∷ : ∀ (a : A) → (as : List A) → a ∈ insert a as
  ∈-∷ a [] = here
  ∈-∷ a (b ∷ as) with conn< a b
  ... | tri< _ _ _ = here
  ... | tri≡ _ refl _ = here
  ... | tri> _ _ _ = there (∈-∷ a as)

  ∺∈ : ∀ {a b : A} → {as : List A} → a ∈ as → a ∈ insert b as
  ∺∈ {b = b} {as = x₁ ∷ as} x with conn< b x₁
  ... | tri< _ _ _ = there x
  ... | tri≡ _ refl _ = x
  ∺∈ {b = b} {x₁ ∷ as} here | tri> _ _ _ = here
  ∺∈ {b = b} {x₁ ∷ as} (there a∈as) | tri> _ _ _ = there (∺∈ a∈as)
  
  ∺∈∷ : ∀ {c a : A} → {as : List A} → c ∈ insert a as → (c ≡ a ⊎ c ∈ as)
  ∺∈∷ {c} {.c} {[]} here = inj₁ refl
  ∺∈∷ {c} {a} {b ∷ as} x with conn< a b
  ∺∈∷ {.a} {a} {b ∷ as} here | tri< a<b a≢b a≯b = inj₂ {!!}
  ∺∈∷ {c} {a} {b ∷ as} (there x) | tri< a<b a≢b a≯b = inj₂ {!!}
  ... | tri≡ a≮b a≡b a≯b = {!!}
  ... | tri> a≮b a≢b a>b = {!!}


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
  ∪-sorted {[]} {bs} pas pbs = pbs
  ∪-sorted {as@(_ ∷ _)} {[]} pas pbs = subst UniqueSorted ∪-idᵣ pas
  ∪-sorted {a ∷ as} {bs@(_ ∷ _)} pas pbs = ∪-sorted (popSort pas) (insertSorted pbs)


  mutual
    ∪-∈ᵣ : ∀ (a : A) → (as bs : List A) → a ∈ as → a ∈ (as ∪ bs)
    ∪-∈ᵣ a (x₁ ∷ as) [] x = x
    ∪-∈ᵣ a (.a ∷ as) (x₂ ∷ bs) here = ∪-∈ₗ a as (insert a (x₂ ∷ bs)) (∈-∷ a (x₂ ∷ bs))
    ∪-∈ᵣ a (x₁ ∷ as) (x₂ ∷ bs) (there x) = ∪-∈ᵣ a as _ x

    ∪-∈ₗ : ∀ (a : A) → (as bs : List A) → a ∈ bs → a ∈ (as ∪ bs)
    ∪-∈ₗ a [] (x₁ ∷ bs) x = x
    ∪-∈ₗ a (x₂ ∷ as) (x₁ ∷ bs) a∈bs = ∪-∈ₗ a as (insert x₂ (x₁ ∷ bs)) (∺∈ a∈bs)

  ∈-∪ : ∀ {c : A} → {as bs : List A} → c ∈ (as ∪ bs) → c ∈ as ⊎ c ∈ bs
  ∈-∪ {c} {[]} {bs} x = inj₂ x
  ∈-∪ {c} {x₁ ∷ as} {[]} x = inj₁ x
  ∈-∪ {c} {a ∷ as} {b ∷ bs} x with ∈-∪ x
  ... | inj₁ p = inj₁ (there p)
  ... | inj₂ y with ∺∈∷ y
  ... | inj₁ refl = inj₁ here
  ... | inj₂ y₁ = inj₂ y₁
  
  ι₀-∪ : ∀ {as bs : List A} → as ⊆ (as ∪ bs)
  ι₀-∪ {[]} = λ c ()
  ι₀-∪ {a ∷ as} {[]} = λ c z → z
  ι₀-∪ {a ∷ as} {b ∷ bs} with conn< a b
  ... | tri< _ _ _ = λ { x here → ∪-∈ₗ a as (a ∷ b ∷ bs) here ; x (there x₁) → ∪-∈ᵣ x as (a ∷ b ∷ bs) x₁}
  ... | tri≡ _ refl _ = λ { x here → ∪-∈ₗ a as (a ∷ bs) here ; x (there x₁) → ∪-∈ᵣ x as (a ∷ bs) x₁}
  ... | tri> _ _ _ = λ { x here →  ∪-∈ₗ a as (b ∷ insert a bs) (there (∈-∷ a bs))  ; x (there x₁) → ∪-∈ᵣ x as (b ∷ insert a bs) x₁}

  [_,_]-∪ : ∀ {as bs cs : List A} → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → {pc : UniqueSorted cs} → as ⊆ bs -> bs ⊆ cs -> (as ∪ bs) ⊆ cs
  [_,_]-∪ {[]} {bs} x all = λ { c here → all c here ; c (there x₂) → all c (there x₂)}  
  [_,_]-∪ {x₂ ∷ as} {[]} all x₁ = all x₂ here ↯ λ ()
  [_,_]-∪ {a ∷ as} {b ∷ bs} x x₁ = λ {x₂ x₃ → {!∈-∪ x₃!}}

--------------------------------------------------
-- now here comes the weird stuff

open import Agora.Conventions using (
  _:&_; ⟨_⟩; _since_; ′_′; _on_; of_ ;
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
  U ∨-𝒫ᶠⁱⁿ V = (⟨ U ⟩ ∪ ⟨ V ⟩) since ∪-sorted (of U) (of V)


  ⊥-𝒫ᶠⁱⁿ : 𝒫ᶠⁱⁿ A
  ⊥-𝒫ᶠⁱⁿ = [] since []

  initial-⊥-𝒫ᶠⁱⁿ : ∀{U : 𝒫ᶠⁱⁿ A} -> ⊥-𝒫ᶠⁱⁿ ≤ U
  initial-⊥-𝒫ᶠⁱⁿ = incl (λ {c ()})

  ι₀-∨-𝒫ᶠⁱⁿ : ∀{U V} -> U ≤ (U ∨-𝒫ᶠⁱⁿ V)
  ι₀-∨-𝒫ᶠⁱⁿ {′ [] ′} {V} = {!!}
  ι₀-∨-𝒫ᶠⁱⁿ {′ x ∷ ⟨_⟩ ′} {V} = {!!}

  [_,_]-∨-𝒫ᶠⁱⁿ : ∀{U V W} -> U ≤ W -> V ≤ W -> (U ∨-𝒫ᶠⁱⁿ V) ≤ W
  [_,_]-∨-𝒫ᶠⁱⁿ = {!!}

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = initial-⊥-𝒫ᶠⁱⁿ
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = λ {U V} -> ι₀-∨-𝒫ᶠⁱⁿ {U} {V}
                           ; ι₁-∨ = {!!}
                           ; [_,_]-∨ = [_,_]-∨-𝒫ᶠⁱⁿ
                           }



_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ ⊎ ⟨ B ⟩ ′

𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ ⊤ ′

module _ (A : StrictOrder 𝑖) (B : StrictOrder 𝑗) where
  postulate
    hasStrictOrderHom : (f : ⟨ A ⟩ -> ⟨ B ⟩) -> Set 𝑖

  StrictOrderHom = _ :& hasStrictOrderHom



-- TODO Naming
module _ {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} where
  postulate
    Img-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ A -> 𝒫ᶠⁱⁿ B
    map-Img-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V

  postulate
    PreImg-𝒫ᶠⁱⁿ : (f : StrictOrderHom A B) -> 𝒫ᶠⁱⁿ B -> 𝒫ᶠⁱⁿ A
    map-PreImg-𝒫ᶠⁱⁿ : ∀{f U V} -> U ≤ V -> Img-𝒫ᶠⁱⁿ f U ≤ Img-𝒫ᶠⁱⁿ f V


  postulate
    instance hasStrictOrderHom:inj₂ : hasStrictOrderHom B (A ⋆-StrictOrder B) inj₂

