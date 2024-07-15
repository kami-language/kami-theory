

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Data.UniqueSortedList.Properties where

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Conventions
open import Agora.Data.Fin.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics


module _ {𝑖} {A : Set 𝑖} {{AP : hasStrictOrder A}} where
  hasDecidableEquality:byStrictOrder : hasDecidableEquality A
  hasDecidableEquality:byStrictOrder = record { _≟_ = f }
    where
      f : (a b : A) -> _
      f a b with conn-< a b
      ... | tri< a<b a≢b a≯b = no λ {refl -> irrefl-< a<b}
      ... | tri≡ a≮b a≡b a≯b = yes a≡b
      ... | tri> a≮b a≢b a>b = no λ {refl -> irrefl-< a>b}




module _ {A : 𝒰 𝑖} {{Ap : hasStrictOrder A}} where



  split-∈ : ∀{b} {bs : List A} -> b ∈ bs -> ∑ λ bs0 -> ∑ λ bs1 -> bs0 <> (b ∷ bs1) ≡ bs
  split-∈ here = [] , _ , refl-≡
  split-∈ {bs = x ∷ bs} (there p) using
    bs0 , bs1 , p <- split-∈ p
    = (x ∷ bs0) , bs1 , cong-≡ (x ∷_) p

  comp-<,∈ : ∀{x y a} -> {as : List A} -> isUniqueSorted (a ∷ as) -> x < a -> y ∈ a ∷ as -> x < y
  comp-<,∈ Paas x<a here = x<a
  comp-<,∈ (x ∷ Paas) x<a (there q) = comp-<,∈ Paas (trans-< x<a x) q

  restrict-∈ : ∀{x y} {bs0 bs1 : List A} -> isUniqueSorted (bs0 <> (x ∷ bs1)) -> x < y -> y ∈ bs0 <> (x ∷ bs1) -> y ∈ bs1
  restrict-∈ {bs0 = []} Pbs x<y here = ⊥-elim (irrefl-< x<y)
  restrict-∈ {bs0 = []} Pbs x<y (there q) = q
  restrict-∈ {bs0 = x ∷ bs0} Pbs x<y here = let q = comp-<,∈ Pbs x<y (ι₁-⋆-∈ {bs = x ∷ bs0} here) in ⊥-elim (irrefl-< q)
  restrict-∈ {bs0 = x ∷ []} Pbs x<y (there here) = ⊥-elim (irrefl-< x<y)
  restrict-∈ {bs0 = x ∷ []} Pbs x<y (there (there q)) = q
  restrict-∈ {bs0 = x ∷ x₁ ∷ bs0} (x₂ ∷ Pbs) x<y (there q) = restrict-∈ {bs0 = x₁ ∷ bs0} Pbs x<y q


  split-⊆ : ∀{x} {as bs0 bs1 : List A}
          -> isUniqueSorted (x ∷ as) -> isUniqueSorted (bs0 <> (x ∷ bs1))
          -> x ∷ as ⊆ bs0 <> (x ∷ bs1) -> as ⊆ bs1
  split-⊆ {x = x} {as = []} {bs0 = bs0} {bs1} Pas Pbs p y ()
  split-⊆ {x = x} {as = a ∷ as} {bs0 = bs0} {bs1} (x<a ∷ Pas) Pbs p y yp
    using z <- p y (there yp)
    = restrict-∈ Pbs (comp-<,∈ Pas x<a yp) z

  drop-isUniqueSorted : ∀{a} {as : List A} -> isUniqueSorted (a ∷ as) -> isUniqueSorted as
  drop-isUniqueSorted [-] = []
  drop-isUniqueSorted (x ∷ Pas) = Pas

  drop*-isUniqueSorted : {bs as : List A} -> isUniqueSorted (bs <> as) -> isUniqueSorted as
  drop*-isUniqueSorted {bs = []} p = p
  drop*-isUniqueSorted {bs = x ∷ bs} p = drop*-isUniqueSorted {bs = bs} (drop-isUniqueSorted p)

  from-⊆ : ∀ {as bs : List A} -> isUniqueSorted as -> isUniqueSorted bs -> as ⊆ bs -> as ≼ bs
  from-⊆ {as = []} {bs = bs} Pas Pbs p = []≼
  from-⊆ {as = x ∷ as} {bs = bs} Pas Pbs p with split-∈ (p _ here)
  ... | bs0 , bs1 , refl-≡ = ι₁-⋆-≼ {bs = bs0} (take (from-⊆ (drop-isUniqueSorted Pas) (drop-isUniqueSorted (drop*-isUniqueSorted {bs = bs0} Pbs)) (split-⊆ Pas Pbs p)))

  into-⊆ : ∀ {as bs : List A} -> as ≼ bs -> as ⊆ bs
  into-⊆ done = refl-⊆
  into-⊆ (skip p) = skip-⊆ (into-⊆ p)
  into-⊆ (take p) = take-⊆ (into-⊆ p)




  -----------------------------------------
  -- deciding equality

  private instance _ = hasDecidableEquality:byStrictOrder {{Ap}}

  decide-≼ : (as bs : List A) -> isUniqueSorted as -> isUniqueSorted bs -> isDecidable (as ≼ bs)
  decide-≼ as bs Pas Pbs with as ⊆? bs
  ... | no x = no (λ p -> x (into-⊆ p))
  ... | yes x = yes (from-⊆ Pas Pbs x)


module _ {A : StrictOrder 𝑖} where

  ι₀-∪-≼ : ∀ {as bs : UniqueSortedList A} → ⟨ as ⟩ ≼ (⟨ as ⟩ ∪ ⟨ bs ⟩)
  ι₀-∪-≼ {as = as} {bs} = from-⊆ (of as) (∪-sorted (of as) (of bs)) (ι₀-∪ )

  ι₁-∪-≼ : ∀ {as bs : UniqueSortedList A} → ⟨ bs ⟩ ≼ (⟨ as ⟩ ∪ ⟨ bs ⟩)
  ι₁-∪-≼ {as = as} {bs} = from-⊆ (of bs) (∪-sorted (of as) (of bs)) (ι₁-∪ {as = ⟨ as ⟩})

  [_,_]-∪-≼ : ∀ {as bs cs : UniqueSortedList A} → ⟨ as ⟩ ≼ ⟨ cs ⟩ -> ⟨ bs ⟩ ≼ ⟨ cs ⟩ -> (⟨ as ⟩ ∪ ⟨ bs ⟩) ≼ ⟨ cs ⟩
  [_,_]-∪-≼ {as} {bs} {cs} p q = from-⊆ (∪-sorted (of as) (of bs)) (of cs) [ into-⊆ p , into-⊆ q ]-∪



