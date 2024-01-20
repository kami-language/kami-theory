
{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-20.UniqueSortedList where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.List.Base using (List; []; _∷_)

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


{-
  insert : (a : A) → (as : List A) → UniqueSorted as → Σ _ UniqueSorted
  insert a [] _ = (a ∷ []) , [ a ]
  insert a (b ∷ []) _ with conn< a b
  ... | tri< a<b _ _ = (a ∷ b ∷ []) , (a<b ∷ [ b ])
  ... | tri≡ _ a≡b _ = (a ∷ []) , [ a ]
  ... | tri> _ _ a>b = (b ∷ a ∷ []) , (a>b ∷ [ a ])
  insert a (b ∷ c ∷ bs) (b<c ∷ pbs) with conn< a b
  ... | tri< a<b a≢b a≯b = a ∷ b ∷ c ∷ bs , (a<b ∷ (b<c ∷ pbs))
  ... | tri≡ a≮b a≡b a≯b = b ∷ c ∷ bs , (b<c ∷ pbs)
  ... | tri> a≮b a≢b a>b with insert a (c ∷ bs) pbs
  ... | [] , snd = (b ∷ [] , [ b ])
  ... | x ∷ .[] , [ x ] = (b ∷ x ∷ [] , {!!} )
  ... | x ∷ (y ∷ xs) , (x₁ ∷ snd) = (b ∷ x ∷ y ∷ xs , {!!})

-}


  _∪_ : (as bs : List A) → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → Σ _ UniqueSorted
  ([] ∪ bs) {pb = pb} = bs , pb
  (as ∪ []) {pa = pa} = as , pa
  ((a ∷ as) ∪ bs) {pa = pa} {pb = pb} = let
      abs = insert a bs
    in (as ∪ abs) {pa = popSort pa} {pb = insertSorted pb}

--------------------------------------------------
{-
  ∈-∷ : ∀ (a : A) → (as : List A) → {{pa : UniqueSorted as}} → a ∈ insert a as
  ∈-∷ a [] ⦃ [] ⦄ = here
  ∈-∷ a (b ∷ []) ⦃ pa ⦄ with conn< a b
  ... | tri< a<b _ _ = here
  ... | tri≡ _ refl _ = here 
  ... | tri> _ _ a>b = there here 
  ∈-∷ a (b ∷ x ∷ as) ⦃ pb ∷ pbs ⦄ with conn< a b
  ... | tri< a<b _ _ = here
  ... | tri≡ _ refl _ = here
  ... | tri> _ _ a>b = {!!} --∈-∷ a (x ∷ as) {{ pbs }}

  ∺∈ : ∀ {a b : A} → {as : List A} → {{pa : UniqueSorted as}} → a ∈ as → a ∈ fst (insert b as pa)
  ∺∈ {a} {b} {as = c ∷ []} ⦃ pa ⦄ a∈c∷[] with conn< b c
  ... | tri< a<b _ _ = there a∈c∷[] 
  ... | tri≡ _ refl _ = a∈c∷[]
  ∺∈ {.c} {b} {c ∷ []} ⦃ pa ⦄ here | tri> _ _ a>b = here
  ∺∈ {a} {b} {as = b₁ ∷ x₁ ∷ as} ⦃ x ∷ pa ⦄ a∈as with conn< b b₁
  ... | tri< a<b _ _ = there a∈as
  ... | tri≡ _ refl _ = a∈as
  ∺∈ {.b₁} {b} {b₁ ∷ x₁ ∷ as} ⦃ x ∷ pa ⦄ here | tri> _ _ b>b₁ = {!!}
  ∺∈ {a} {b} {b₁ ∷ x₁ ∷ as} ⦃ x ∷ pa ⦄ (there a∈as) | tri> _ _ b>b₁ = {!!} --∺∈ {{_}} a∈as

-- ∺∈ {a} {{!!}} {x₁ ∷ as} {{pa}} {!!}
-}

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


  mutual
    ∈-∪₁ : ∀ (a : A) → (as bs : List A) → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → a ∈ as → a ∈ fst ((as ∪ bs) {pa} {pb})
    ∈-∪₁ a (x₁ ∷ as) [] x = x
    ∈-∪₁ a (.a ∷ as) (x₂ ∷ bs) here = ∈-∪₂ a as (insert a (x₂ ∷ bs)) (∈-∷ a (x₂ ∷ bs))
    ∈-∪₁ a (x₁ ∷ as) (x₂ ∷ bs) (there x) = ∈-∪₁ a as _ x

    ∈-∪₂ : ∀ (a : A) → (as bs : List A) → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → a ∈ bs → a ∈ fst ((as ∪ bs) {pa} {pb})
    ∈-∪₂ a [] (x₁ ∷ bs) x = x
    ∈-∪₂ a (x₂ ∷ as) (x₁ ∷ bs) {pb = pb} a∈bs = ∈-∪₂ a as (insert x₂ (x₁ ∷ bs)) (∺∈ a∈bs)

  ι₀-∪ : ∀ {as bs : List A} → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → as ⊆ (fst ((as ∪ bs) {pa} {pb}))
  ι₀-∪ {[]} = λ c ()
  ι₀-∪ {x ∷ as} {[]} = λ c z → z
  ι₀-∪ {x ∷ as} {x₁ ∷ bs} {pa} {pb} = λ { c here → ∈-∪₂ c as (insert x (x₁ ∷ bs)) (∈-∷ x (x₁ ∷ bs)) ;
                                                    c (there c∈x∷as) → ∈-∪₁ c as _ {popSort pa} {_} c∈x∷as }

  open import Agora.Conventions using (∑_ ; fst ; snd ; Maybe ; just ; nothing)

  _∨_ : (as bs : ∑ UniqueSorted) -> ∑ UniqueSorted
  _∨_ as bs = (fst as ∪ fst bs) {snd as} {snd bs}

  head : (as : ∑ UniqueSorted) -> ∀{a} -> (a ∈ fst as) -> A
  head (x ∷ as , snd₁) p = x

  tail : (as : ∑ UniqueSorted) -> ∀{a} -> (a ∈ fst as) -> ∑ UniqueSorted
  tail (x ∷ .[] , [ .x ]) p = [] , []
  tail (x ∷ as@(_ ∷ _) , (x₁ ∷ asp)) p = as , asp

  dec-insert : ∀ a -> (as : ∑ UniqueSorted) -> ∀{x} -> x ∈ insert a (fst as) -> x ≡ a ⊎ x ∈ fst as
  dec-insert a ([] , []) {.a} here = inj₁ refl
  dec-insert a (x₁ ∷ as , asp) {x} p with conn< a x₁
  ... | tri< a<b a≢b a≯b = {!!}
  ... | tri≡ a≮b a≡b a≯b = {!!}
  ... | tri> a≮b a≢b a>b = {!!}

  either : ∀{x} -> ∀ as asp bs bsp -> (x ∈ fst ((as ∪ bs) {asp} {bsp})) -> x ∈ as ⊎ x ∈ bs
  either {x} []  asp (b ∷ bs) bsp z = {!!}
  either {x} (a ∷ as) asp [] bsp z = {!!}
  either {x} (a ∷ .[]) [ .a ] (b ∷ bs) (bsp) z = {!!}
  either {x} (a ∷ as@(_ ∷ _)) (x₂ ∷ asp) (x₁ ∷ bs) bsp z with either as asp (insert a (x₁ ∷ bs)) (insertSorted bsp) z
  ... | inj₁ x₃ = inj₁ (there x₃)
  ... | inj₂ y with dec-insert _ (_ , bsp) y
  ... | inj₁ refl = inj₁ here
  ... | inj₂ y₁ = inj₂ y₁

  -- dec-∪-head : (as bs : ∑ UniqueSorted) -> ∀{a} -> (ap : a ∈ fst (as ∨ bs)) -> head (as ∨ bs) ap ∈ fst as ⊎ head (as ∨ bs) ap ∈ fst bs
  -- dec-∪-head ([] , asp) (bs , bsp) {a} ap = {!!}
  -- dec-∪-head (x ∷ as , asp) ([] , bsp) {a} ap = {!!}
  -- dec-∪-head (x ∷ as@[] , [ .x ]) (x₁ ∷ bs , bsp) {a} ap = let Z = dec-∪-head (as , {!!}) _ {{!!}} {!!} in {!!}
  -- dec-∪-head (x ∷ as@(_ ∷ _) , (x₂ ∷ asp)) (x₁ ∷ bs , bsp) {a} ap with dec-∪-head (as , asp) (insert x (x₁ ∷ bs) , {!!}) {{!!}} {!!}
  -- ... | inj₁ X = inj₁ (there X)
  -- ... | inj₂ X with dec-insert _ (_ , bsp) X
  -- ... | inj₁ x₃ = inj₁ {!x₃!}
  -- ... | inj₂ y = inj₂ (y)

  -- dec-∪-head as bs {a} ap with as ∨ bs in eq
  -- dec-∪-head ([] , asp) (bs , bsp) {a} ap | X = {!!}
  -- dec-∪-head (x ∷ as , asp) ([] , bsp) {a} ap | X = {!!}
  -- dec-∪-head (x ∷ as , asp) (x₁ ∷ bs , bsp) {a} ap | X = {!!}



  [_,_]-∪ : ∀ {as bs cs : List A} → {pa : UniqueSorted as} → {pb : UniqueSorted bs} → {pc : UniqueSorted cs} → as ⊆ cs -> bs ⊆ cs -> fst ((as ∪ bs) {pa} {pb}) ⊆ cs
  [_,_]-∪ {[]} {bs} x all = λ { c here → all c here ; c (there x₂) → all c (there x₂)}  
  [_,_]-∪ {x₂ ∷ as} {[]} all x₁ = {!!} -- all x₂ here ↯ λ ()
  [_,_]-∪ {a ∷ as} {b ∷ bs} {_} {pa} {pb} x x₁ = {!!}
  -- with fst ((as ∪ (insert a (b ∷ bs))) {popSort {a} {as} pa} {insertSorted {a} {b ∷ bs} pb}) in eq
  -- ...| A = {!!}
  -- z1 z2 = {!!}
  -- with conn< a b
  -- ... | A = {!!}
  -- with z2 | conn< a b
  -- ... | A | Z = {!!}
 


-- PP : 
--     {𝑖 : Level} {A : Set 𝑖} ⦃ _ = z : hasStrictOrder A ⦄ (a b : A)
--     (w
--     : Tri ((z hasStrictOrder.< a) b) (a ≡ b)
--       ((z hasStrictOrder.< b) a))
--     (as bs : List A) {cs : List A} {pa : UniqueSorted (a ∷ as)}
--     {pb : UniqueSorted (b ∷ bs)} {pc : UniqueSorted cs}
--     (x : (x₁ : A) → x₁ ∈ a ∷ as → x₁ ∈ b ∷ bs)
--     (x₁ : (x₂ : A) → x₂ ∈ b ∷ bs → x₂ ∈ cs) (z1 : A)
--     (z2 : z1 ∈ fst (as ∪ (insert a (b ∷ bs) | w))) →
--     z1 ∈ cs
-- PP = ?
{-
--------------------------------------------------
-- now here comes the weird stuff

open import Agora.Conventions using (
  _:&_; ⟨_⟩; _since_; ′_′; _on_;
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
  reflexive-≤-𝒫ᶠⁱⁿ = incl (allIn (λ c x → x))

  _⟡-𝒫ᶠⁱⁿ_ : ∀{U V W} -> U ≤-𝒫ᶠⁱⁿ V -> V ≤-𝒫ᶠⁱⁿ W -> U ≤-𝒫ᶠⁱⁿ W
  incl (allIn p) ⟡-𝒫ᶠⁱⁿ incl (allIn q) = incl (allIn (λ c x → q c (p c x)))

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
  U ∨-𝒫ᶠⁱⁿ V = let a , b = (⟨ U ⟩ ∪ ⟨ V ⟩) in a since b 

  ⊥-𝒫ᶠⁱⁿ : 𝒫ᶠⁱⁿ A
  ⊥-𝒫ᶠⁱⁿ = [] since []

  initial-⊥-𝒫ᶠⁱⁿ : ∀{U : 𝒫ᶠⁱⁿ A} -> ⊥-𝒫ᶠⁱⁿ ≤ U
  initial-⊥-𝒫ᶠⁱⁿ = incl (allIn (λ {c ()}))

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
-}
