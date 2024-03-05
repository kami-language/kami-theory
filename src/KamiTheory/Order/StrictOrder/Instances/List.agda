-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Order.StrictOrder.Instances.List where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base


-- We show that there is a strict (lexicographic) order on List A for a strict order A

module _ {A : 𝒰 𝑖} {{Ap : hasStrictOrder A}} where
  data _<-List_ : (u v : List A) -> 𝒰 𝑖 where
    empty : ∀{u us} -> [] <-List (u ∷ us)
    take : ∀{u us v vs} -> (u < v) -> (u ∷ us) <-List (v ∷ vs)
    next : ∀{u vs ws} -> vs <-List ws -> (u ∷ vs) <-List (u ∷ ws)

  irrefl-<-List : ∀{us} -> ¬ us <-List us
  irrefl-<-List (take x) = irrefl-< x
  irrefl-<-List (next p) = irrefl-<-List p

  trans-<-List : ∀{us vs ws} -> us <-List vs -> vs <-List ws -> us <-List ws
  trans-<-List empty (take x) = empty
  trans-<-List empty (next q) = empty
  trans-<-List (take x) (take y) = take (trans-< x y)
  trans-<-List (take x) (next q) = take x
  trans-<-List (next p) (take x) = take x
  trans-<-List (next p) (next q) = next (trans-<-List p q)

  head-<-List : ∀{a b} {as bs} -> (a ∷ as) <-List (b ∷ bs) -> ¬ (b < a)
  head-<-List (take p) = asym-< p
  head-<-List (next p) = irrefl-<

  tail-<-List : ∀{a} {as bs} -> (a ∷ as) <-List (a ∷ bs) -> (as <-List bs)
  tail-<-List (take x) = ⊥-elim (irrefl-< x)
  tail-<-List (next p) = p

  conn-<-List : (a b : List A) -> Tri (a <-List b) (a ≡ b) (b <-List a)
  conn-<-List [] [] = tri≡ (λ ()) refl-≡ (λ ())
  conn-<-List [] (x ∷ b) = tri< empty (λ ()) (λ ())
  conn-<-List (x ∷ a) [] = tri> (λ ()) (λ ()) empty
  conn-<-List (a ∷ as) (b ∷ bs) with conn-< a b
  ... | tri< a<b a≢b a≯b = tri< (take a<b) (λ p -> a≢b (head-≡ p)) (λ p -> head-<-List p a<b)
  ... | tri> a≮b a≢b a>b = tri> ((λ p -> head-<-List p a>b)) ((λ p -> a≢b (head-≡ p))) (take a>b)
  ... | tri≡ a≮b refl-≡ a≯b with conn-<-List as bs
  ... | tri< as<bs as≢bs as≯bs = tri< (next as<bs) (λ p -> as≢bs (tail-≡ p)) (λ p → as≯bs (tail-<-List p))
  ... | tri≡ a≮b₁ refl-≡ a≯b₁ = tri≡ irrefl-<-List refl-≡ irrefl-<-List
  ... | tri> as≮bs as≢bs as>bs = tri> ((λ p → as≮bs (tail-<-List p))) ((λ p -> as≢bs (tail-≡ p))) (next as>bs)

  force-≡-<-List : ∀{as bs} -> (a b : as <-List bs) → a ≡ b
  force-≡-<-List empty empty = refl-≡
  force-≡-<-List (take x) (take y) = cong-≡ take (force-≡ x y)
  force-≡-<-List (take x) (next b) = ⊥-elim (irrefl-< x)
  force-≡-<-List (next a) (take x) = ⊥-elim (irrefl-< x)
  force-≡-<-List (next a) (next b) = cong-≡ next (force-≡-<-List a b)

  instance
    isProp:<-List : ∀{as bs : List A} -> isProp (as <-List bs)
    isProp:<-List = record { force-≡ = force-≡-<-List }

  instance
    isStrictOrder:<-List : isStrictOrder _<-List_
    isStrictOrder:<-List = record
      { irrefl-< = irrefl-<-List
      ; trans-< = trans-<-List
      ; conn-< = conn-<-List
      }

  instance
    hasStrictOrder:List : hasStrictOrder (List A)
    hasStrictOrder:List = record { _<_ = _<-List_ }



