
{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2024-01-20.UniqueSortedList where

open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; cong)

open import KamiD.Dev.2024-01-20.Basics
open import KamiD.Dev.2024-01-20.StrictOrder.Base


it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A
  
--------------------------------------------------
-- decidable equality

record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → Dec (x ≡ y)

open hasDecidableEquality {{...}} public



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

  ⊈[] : ∀ {as : List A} → ¬ (as ≡ []) → ¬ (as ⊆ [])
  ⊈[] {[]} as≢[] x = refl ↯ as≢[]
  ⊈[] {x₁ ∷ as} as≢[] x = x x₁ here ↯ λ ()

  ⊆∷ : ∀ {a : A} {as bs : List A} → (a ∷ as) ⊆ bs → as ⊆ bs
  ⊆∷ sf = λ x x₁ → sf x (there x₁)

--------------------------------------------------
-- sortedness

module _ {𝑖 : Level} {A : Set 𝑖} {{_ : hasStrictOrder A}} where

  data isUniqueSorted : List A → Set 𝑖 where
    []  : isUniqueSorted []
    [-] : ∀ {x} → isUniqueSorted (x ∷ [])
    _∷_ : ∀ {x y xs} → x < y → isUniqueSorted (y ∷ xs) → isUniqueSorted (x ∷ y ∷ xs)

  popSort : {a : A} → {as : List A} → isUniqueSorted (a ∷ as) → isUniqueSorted as
  popSort [-] = []
  popSort (x ∷ x₁) = x₁



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
  insert a (b ∷ as) with conn-< a b
  ... | tri< a<b a≢b a≯b = a ∷ b ∷ as
  ... | tri≡ a≮b a≡b a≯b = b ∷ as
  ... | tri> a≮b a≢b a>b = b ∷ (insert a as)

  data _<*_ (a : A) : List A → Set 𝑖 where
    []  : a <* []
    _∷_ : ∀ {b bs} → (a < b) → a <* bs → a <* (b ∷ bs)

  all∷ : {a b : A} → {bs : List A} → a < b → a <* bs → a <* (b ∷ bs)
  all∷ a<b [] = a<b ∷ []
  all∷ a<b (a<b₁ ∷ a<*bs) = a<b ∷ a<b₁ ∷ a<*bs

  allSort : {a : A} → {as : List A} → isUniqueSorted (a ∷ as) → a <* as
  allSort [-] = []
  allSort (x ∷ [-]) = all∷ x []
  allSort (a<z ∷ (z<y ∷ usyxs)) = all∷ a<z (allSort (trans-< {𝑖} {A} a<z z<y ∷ usyxs))
  
  sortAll : {a : A} → {as : List A} → a <* as → isUniqueSorted as → isUniqueSorted (a ∷ as)
  sortAll {a} [] x₁ = [-]
  sortAll (x ∷ x₂) x₁ = x ∷ x₁
  
  insertAll : {a c : A} → {as : List A} → c < a → c <* as → isUniqueSorted as → c <* (insert a as)
  insertAll {as = []} x x₁ usas = x ∷ x₁
  insertAll {a} {c} {b ∷ as} c<a (c<b ∷ c<*as) usas with conn-< a b
  ... | tri< _ _ _ = c<a ∷ (c<b ∷ c<*as)
  ... | tri≡ _ _ _ = (c<b ∷ c<*as)
  ... | tri> a≮b a≢b a>b = let
      c<*aas = insertAll c<a c<*as (popSort usas)
    in all∷ c<b c<*aas

  insertSorted : {a : A} → {as : List A} → isUniqueSorted as → isUniqueSorted (insert a as)
  insertSorted {a} {[]} usas = [-]
  insertSorted {a} {(b ∷ as)} ([-]) with conn-< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ [-]
  ... | tri≡ a≮b a≡b a≯b = [-]
  ... | tri> a≮b a≢b a>b = a>b ∷ [-]
  insertSorted {a} {(b ∷ as)} (b<y ∷ usas) with conn-< a b
  ... | tri< a<b a≢b a≯b = a<b ∷ (b<y ∷ usas)
  ... | tri≡ a≮b a≡b a≯b = (b<y ∷ usas)
  ... | tri> a≮b a≢b a>b = let
      b<*yas = allSort (b<y ∷ usas)
      b<*y∷xs = insertAll a>b b<*yas usas
      ins = insertSorted usas
    in sortAll b<*y∷xs ins


  insertInserts : ∀ (a : A) → (as : List A) → a ∈ insert a as
  insertInserts a [] = here
  insertInserts a (b ∷ as) with conn-< a b
  ... | tri< _ _ _ = here
  ... | tri≡ _ refl _ = here
  ... | tri> _ _ _ = there (insertInserts a as)

  insertKeeps : ∀ {a b : A} → {as : List A} → a ∈ as → a ∈ insert b as
  insertKeeps {b = b} {as = x₁ ∷ as} x with conn-< b x₁
  ... | tri< _ _ _ = there x
  ... | tri≡ _ refl _ = x
  insertKeeps {b = b} {x₁ ∷ as} here | tri> _ _ _ = here
  insertKeeps {b = b} {x₁ ∷ as} (there a∈as) | tri> _ _ _ = there (insertKeeps a∈as)
  
  insertPreserves : ∀ {c a : A} → {as : List A} → c ∈ insert a as → (c ≡ a ⊎ c ∈ as)
  insertPreserves {c} {.c} {[]} here = inj₁ refl
  insertPreserves {c} {a} {b ∷ as} x with conn-< a b
  insertPreserves {.a} {a} {b ∷ as} here | tri< a<b a≢b a≯b = inj₁ refl
  insertPreserves {c} {a} {b ∷ as} (there x) | tri< a<b a≢b a≯b = inj₂ x
  ... | tri≡ a≮b a≡b a≯b = inj₂ x
  insertPreserves {.b} {a} {b ∷ as} here | tri> a≮b a≢b a>b = inj₂ here
  insertPreserves {c} {a} {b ∷ as} (there x) | tri> a≮b a≢b a>b with insertPreserves {c} {as = as} x
  ... | inj₁ x₁ = inj₁ x₁
  ... | inj₂ y = inj₂ (there y)



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

  ∪-sorted : ∀ {as bs} → isUniqueSorted as → isUniqueSorted bs → isUniqueSorted (as ∪ bs)
  ∪-sorted {[]} _ pbs = pbs
  ∪-sorted {_ ∷ _} {[]} pas _ = subst isUniqueSorted ∪-idᵣ pas
  ∪-sorted {_ ∷ _} {_ ∷ _} pas pbs = ∪-sorted (popSort pas) (insertSorted pbs)


  mutual
    ∪-∈ᵣ : ∀ (a : A) → (as bs : List A) → a ∈ as → a ∈ (as ∪ bs)
    ∪-∈ᵣ a (x₁ ∷ as) [] x = x
    ∪-∈ᵣ a (.a ∷ as) (x₂ ∷ bs) here = ∪-∈ₗ a as (insert a (x₂ ∷ bs)) (insertInserts a (x₂ ∷ bs))
    ∪-∈ᵣ a (x₁ ∷ as) (x₂ ∷ bs) (there x) = ∪-∈ᵣ a as _ x

    ∪-∈ₗ : ∀ (a : A) → (as bs : List A) → a ∈ bs → a ∈ (as ∪ bs)
    ∪-∈ₗ a [] (x₁ ∷ bs) x = x
    ∪-∈ₗ a (x₂ ∷ as) (x₁ ∷ bs) a∈bs = ∪-∈ₗ a as (insert x₂ (x₁ ∷ bs)) (insertKeeps a∈bs)

  ∈-∪ : ∀ {c : A} → {as bs : List A} → c ∈ (as ∪ bs) → c ∈ as ⊎ c ∈ bs
  ∈-∪ {c} {[]} {bs} x = inj₂ x
  ∈-∪ {c} {x₁ ∷ as} {[]} x = inj₁ x
  ∈-∪ {c} {a ∷ as} {b ∷ bs} x with ∈-∪ x
  ... | inj₁ p = inj₁ (there p)
  ... | inj₂ y with insertPreserves y
  ... | inj₁ refl = inj₁ here
  ... | inj₂ y₁ = inj₂ y₁

  
  ι₀-∪ : ∀ {as bs : List A} → as ⊆ (as ∪ bs)
  ι₀-∪ {[]} = λ c ()
  ι₀-∪ {a ∷ as} {[]} = λ c z → z
  ι₀-∪ {a ∷ as} {b ∷ bs} with conn-< a b
  ... | tri< _ _ _ = λ { x here → ∪-∈ₗ a as (a ∷ b ∷ bs) here ;
                         x (there x₁) → ∪-∈ᵣ x as (a ∷ b ∷ bs) x₁}
  ... | tri≡ _ refl _ = λ { x here → ∪-∈ₗ a as (a ∷ bs) here ;
                             x (there x₁) → ∪-∈ᵣ x as (a ∷ bs) x₁}
  ... | tri> _ _ _ = λ { x here →  ∪-∈ₗ a as (b ∷ insert a bs) (there (insertInserts a bs)) ;
                         x (there x₁) → ∪-∈ᵣ x as (b ∷ insert a bs) x₁}

  
  ι₁-∪ : ∀ {as bs : List A} → bs ⊆ (as ∪ bs)
  ι₁-∪ {[]} = λ x z → z
  ι₁-∪ {a ∷ as} {[]} = λ x ()
  ι₁-∪ {a ∷ as} {b ∷ bs} with conn-< a b
  ... | tri< _ _ _ = λ { x here → ∪-∈ₗ b as (a ∷ b ∷ bs) (there here) ;
                         x (there x₁) → ∪-∈ₗ x as (a ∷ b ∷ bs) (there (there x₁))}
  ... | tri≡ _ refl _ = λ { x here → ∪-∈ₗ a as (a ∷ bs) here ;
                             x (there x₁) → ∪-∈ₗ x as (a ∷ bs) (there x₁)}
  ... | tri> _ _ _ = λ { x here →  ∪-∈ₗ b as (b ∷ insert a bs) here ;
                         x (there x₁) → ∪-∈ₗ x as (b ∷ insert a bs) (there (insertKeeps x₁))}

  [_,_]-∪ : ∀ {as bs cs : List A} → as ⊆ cs -> bs ⊆ cs -> (as ∪ bs) ⊆ cs
  [_,_]-∪ {as} {bs} x y = λ a a∈as∪bs → [ x a , y a ]′ (∈-∪ a∈as∪bs)


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
UniqueSortedList A = List ⟨ A ⟩ :& isUniqueSorted

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
  (U since Us) ∨-𝒫ᶠⁱⁿ (V since Vs) = let a = (U ∪ V) in a since ∪-sorted Us Vs 

  instance
    hasFiniteJoins:𝒫ᶠⁱⁿ : hasFiniteJoins (𝒫ᶠⁱⁿ A)
    hasFiniteJoins:𝒫ᶠⁱⁿ = record
                           { ⊥ = [] since []
                           ; initial-⊥ = incl (λ {_ ()})
                           ; _∨_ = _∨-𝒫ᶠⁱⁿ_
                           ; ι₀-∨ = incl ι₀-∪
                           ; ι₁-∨ = λ {as} → incl (ι₁-∪ {as = ⟨ as ⟩} )
                           ; [_,_]-∨ = λ { (incl u) (incl v) → incl [ u , v ]-∪}
                           }



_⋆-StrictOrder_ : StrictOrder 𝑖 -> StrictOrder 𝑗 -> StrictOrder _
_⋆-StrictOrder_ A B = ′ ⟨ A ⟩ ⊎ ⟨ B ⟩ ′

𝟙-StrictOrder : StrictOrder _
𝟙-StrictOrder = ′ ⊤ ′

record isStrictOrderHom {𝑖 𝑗} {A : StrictOrder 𝑖} {B : StrictOrder 𝑗} (hom : ⟨ A ⟩ -> ⟨ B ⟩) : Set (𝑖 ⊔ 𝑗) where
  field
    homPreserves : ∀ {a b : ⟨ A ⟩} → a < b → hom a < hom b

open isStrictOrderHom public

module _ (A : StrictOrder 𝑖) (B : StrictOrder 𝑗) where
  StrictOrderHom = (⟨ A ⟩ → ⟨ B ⟩) :& isStrictOrderHom {A = A} {B}


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

  map-img : ∀ {f : StrictOrderHom A B} {U V : List ⟨ A ⟩} -> U ⊆ V → img ⟨ f ⟩ U ⊆ img ⟨ f ⟩ V
  map-img {f} {x₃ ∷ U} {[]} x x₁ x₂ = x ↯ ⊈[] {as = x₃ ∷ U} λ ()
  map-img {f} {x₃ ∷ U} {x₄ ∷ V} x .(⟨ f ⟩ x₃) here with x x₃ here
  ... | here = here
  ... | there x₃∈V = ∈img ⟨ f ⟩ (there x₃∈V)
  map-img {f} {x₃ ∷ U} {x₄ ∷ V} x x₁ (there x₂) = (map-img {f} (⊆∷ x)) x₁ x₂
  
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


--------------------------------------------------
-- we show that isUniqueSorted is a proposition


module _ {𝑖} {A : Set 𝑖} {{_ : hasStrictOrder A}} {{_ : ∀{a b : A} -> isProp (a < b)}} where

  force-≡-isUniqueSorted : ∀{xs : List A} -> (p q : isUniqueSorted xs) -> p ≡ q
  force-≡-isUniqueSorted [] [] = refl
  force-≡-isUniqueSorted [-] [-] = refl
  force-≡-isUniqueSorted (x ∷ p) (y ∷ q) with force-≡ x y | force-≡-isUniqueSorted p q
  ... | refl | refl = refl

  instance
    isProp:isUniqueSorted : ∀{xs : List A} -> isProp (isUniqueSorted xs)
    isProp:isUniqueSorted = record { force-≡ = force-≡-isUniqueSorted }


