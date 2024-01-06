
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2023-12-30.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2023-12-26.Core

{-# BUILTIN REWRITE _≣_ #-}

Name = ℕ

module _ {A B : 𝒰 𝑖} where
  transp-≣ : (A ≣ B) -> A -> B
  transp-≣ refl-≣ a = a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
  cong₂-≣ : (f : A -> B -> C) -> ∀{a₀ a₁ : A} -> ∀{b₀ b₁ : B} -> a₀ ≣ a₁ -> b₀ ≣ b₁ -> f a₀ b₀ ≣ f a₁ b₁
  cong₂-≣ f refl-≣ refl-≣ = refl-≣

-- cong-≣ : {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> (f : (a : A) -> B a) -> {a b : A} -> (a ≣ b) -> f a ≣ f b
cong-≣ : {A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (f : A -> B) -> {a b : A} -> (a ≣ b) -> f a ≣ f b
cong-≣ f refl-≣ = refl-≣

ap₀ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≣ b -> A
ap₀ {a = a} _ = a

ap₁ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≣ b -> A
ap₁ {b = b} _ = b

J1 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑘} -> ∀{a b : A} -> (p : a ≣ b) -> (F : A -> 𝒰 𝑗) -> (f : ∀ a -> F a -> B) -> (x : F a) -> f b (transp-≣ (cong-≣ F p) x) ≣ f a x
J1 refl-≣ F f x = refl-≣



----------------------------------------------------------------
-- A new way forward:
--
-- We look at unifying the forall and existential quantification.
--
-- In the following sense:
--
--   When one has a sum ∑ (a : A) (B a) then we don't add anything
--   to the context when showing b : B a, but we substitute the (a : A)
--   When one has a product ∏ (a : A) (B a) then we don't have a value
--   for (a : A), but we add one into the context while checking B.
--   One could, instead, have a certain derivative (∂ : Term -> Hom_Hole Γ Γ')
--   which describes how the negative parts of the context get modified
--   by the (a : A) term. If we write (hole ↦ z) then with the `hole`
--   term we create a new hole, and as such, `(∂ hole) Γ ≣ (Γ , A)`
--   which means that (b : B a) gets a new A-variable. While if we don't
--   create a new hole, but merely project one from the context, then
--   this is also visible in the derivative: `(∂ (var x)) (Γ , x , Δ) ≣ (Γ , Δ , x)`.
--   But as one can see, no new variable is created.
--
--   We have a very strong _,_ operator: 
--   I can say:
--
--     hole a : ℕ⁻
--
--     hole a , [ a + a ] : ∑ (a : ℕ⁻) (ℕ⁺)
--
--     (hole a , [ a + a ]) , (a := 2) ⇝ [ 2 + 2]
--
--   This means:
--   f , (a := 2)  -- is valid "f 2"
--   f , (a + 2)   -- is also valid "λ a ↦ f a , a + 2"
--
--   We can write protocols as:
--   P ≔ hole a , f a , hole b , g a b , hole c , hole d , x a c d
--   and we can apply them as:
--   P , (a := 2) ⇝ f 2 , hole b , g 2 b , hole c , hole d , x 2 c d
--   P , (a := 2) , (b := 3) ⇝ f 2 , g 2 b , hole c , hole d , x 2 c d
--
--   I can also transport holes from the context again into the term:
--   hole a , a + a , var a -- (but this makes the `a + a` term inaccessible?)
--
--   assume I have [f : -A ⊗ B , g : -B ⊗ C] in the context, then
--   ALL f , ALL g , (π₁ g := ALL(π₂ f)) : -A ⊗ C
--
--   Maps exist only in the non-charged flavor:
--    t : Γ ⊢ [ -A ⊗ -A ] ⇒ [ -A ]
--    t = λ (a0 , a1) ↦ join a0 a1
--
--    s : Γ ⊢ [ -A ⊗ B ] ⊗ [ -B ⊗ C ] ⇒ [ -A ⊗ C ]
--    s = λ ((a , b0) , (b1 , c)) ↦ (a , (b1 := b0) , c)
--
--    r : Γ ⊢ (A ⇒ B) ⇒ [ -A ⊗ B ]
--    r = λ f ↦ hole a , f a
--
--    q : Γ ⊢ [ -A ⊗ B ] ⇒ (A ⇒ B)
--    q = λ (a0 , b) ↦ λ a ↦ extract ((a0 := a) , b)
--
--    p : Γ ⊢ (x : [ X ]) ⇒ ((a : ↓ x) ⇒ (↑ x a)) -- i.e., I can interpret a protocol x : X as a function from the inputs to the outputs
--
--
--   I might define _⇒_ in terms of the _⊗_ ?
--   Then I would say: A ⇒ B := [ -A ⊗ +B ]
--   Thus we would have:
--    t : Γ ⊢ [ -[ -A ⊗ -A ] ⊗ +[ -A ]]
--    t = ?
--
--
--
--------------------------------------------------------
-- Choreographies
--
-- Our model is a topological space with space and time
-- arrow assignments.
--
-- We might *not* need a sophisticated time and space system,
-- though what do we need?
--
-- Next steps: Taking distributed algorithms and formulating
-- them with a dream syntax / typing.
--
--------------------------------------------------------
--
-- We have a new judgement type for communication types:
-- Example:
--  [ b ∶ Bool ＠ 0 ] ⊢Comm [ Val b ](0 → 1) ⊗ [ Val b ](1 → 2)
--
-- In order to typecheck `Γ ⊢[0 → 1] (Val b)` we require that
-- we have `Γ ⊢0 b`, that is, that the variable `b` is accessible
-- at location 0. Additionally, once we have [ Val b ](0 → 1) in
-- the context, we get
--   `{ [ Val b ](0 → 1) }↓＠ 1`
--   ≡ `{[ Val b ](0 → 1) ↓＠ 1 }`
--   ≡ `{ Val b ＠ 1 }`
--
-- It may be enough to only transmit variable values? It seems
-- simpler to do so, so let's do it.
--
-- Now how would we describe the transmission of a vector?
--
-- First, for a tuple:
--  { a : A ＠ 0 , b : B ＠ 0} ⊢Comm [ A ](0 → 1) ⊗ [ B ](0 → 1)
--
-- For a vector we need a function:
--  T : {} ⊢ ∀ (n : ℕ ＠ {0 , 1}) -> (v : Vec A n ＠ 0) -> CommType{0,1}
--  T zero [] = 𝟙
--  T (suc n) (x ∷ xs) = [ Val x ](0 → 1) ⊗ T n xs
--
-- NOTES:
--  The problematic part is letting "1" know which branch we take.
--  The rule is that if we pattern match on a value which is available
--  only at a certain number of locations, then only these locations should
--  observe differences in behaviour.
--  This means: assume (n : ℕ ＠ 0) is only available at "0". Then
--  the two branches of `T` should show unifiable behaviour at "1".
--  This can be achieved if we first send a Maybe value which says whether
--  we have an element or not.
--
--  T : {} ⊢ ∀ (n : ℕ ＠ 0) -> (v : Vec A n ＠ 0) -> CommType{0,1}
--  T zero [] = [ Val nothing : Maybe A ](0 → 1)
--  T (suc n) (x ∷ xs) = [ Val (just x) : Maybe A ](0 → 1) ⊗ T n xs
--
--  I can show observations:
--  O₁ : ∀ (n ＠ 0) (v ＠ 0) -> take0 (T n v ↓＠ 1) ≡ nothing -> n ≡ 0
--                              ~~~~~~~~~~~~~~~~~~
--                                     ^ of type `Maybe A`
--
--                              ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~    ~~~~~
--                                   ^ property ＠ 1               ^ property ＠ 0
--
-- NOTE: It looks like equality is special in the sense that we can have
-- an equality located at 1 which speaks about elements at 0.
--
-- This means that I can implement `T n v ＠ 1` by doing the following:
--
-- t₁ : ∀ (n ＠ 0) (v ＠ 0) -> T n v ↓＠ 1
-- t₁ n v = hole (x : Maybe A) , case x of (nothing ↦ ... using O₁ ... need: nothing, done)
--                                         (just x ↦ )
--
-- Let's take fancy holes, maybe that works:
--
--  T : {} ⊢ ∀ (n : ℕ ＠ 0) -> (v : Vec A n ＠ 0) -> CommType{0,1}
--  T zero [] = [ Val nothing : Maybe A ](0 → 1)
--  T (suc n) (x ∷ xs) = [ Val (just x) : Maybe A ](0 → 1) ⊗ T n xs
--
-- We have `∥ T n v ∥ ≡ [ Maybe A ](0 → 1) ⊗ {(zero⁻¹ n) ∣ T (suc⁻¹ n) (cons⁻¹ xs)}`
--
-- I can show: for (x : T n v ＠ 1) -> Take0 x ≡ nothing -> (n ≡ 0)
--             for (x : T n v ＠ 1) -> Take0 x ≡ just val ->  ∃ (n' ＠ 0). (n ≡ suc n') -> Take1 x
--
-- Another approach:
--
-- If : Bool -> 𝒰 -> 𝒰
-- If true A = A
-- If false A = 𝟙
--
-- SendOne : (b : Bool ＠ 0) -> (If b A ＠ 0) -> CommType{0,1}
-- SendOne b x = [ Val b ] ⊗ 
--
-- splitList : List A -> (b : Bool) ⊗ If b (A ⊗ List A)
-- splitList [] = false , tt
-- splitList (x ∷ xs) = true , (x , xs)
--
-- SendList : (xs : List A ＠ 0) -> CommType{0,1}
-- SendList xs = let (b , head&tail) = splitList xs
--               in [ Val b ](0 → 1) ⊗ case b of
--                                       false -> 𝟙
--                                       true -> let (head , tail) = head&tail
--                                               in [ Val head ](0 → 1) ⊗ SendList tail
--
-- Let's say we have "Tag"-types for sum types. Then we can only pattern match in
-- a {0,1} context on a sum type if the tag is available at all locations without
-- necessarily the data itself.
--
-- SendList : (xs : List A ＠ 0) -> CommType{0,1}
-- SendList xs = [ Val (tag xs) ](0 → 1) ⊗ case xs { [] ↦ 𝟙 | (x ∷ xs) ↦ [ Val x ](0 → 1) ⊗ SendList xs }
--
-- I want to show:
-- sendList : (xs : List A ＠ 0) -[ SendList xs ]-> (Val xs {T = List A} ＠ 1)
--
-- Note: the function not only sends a list, but the typesystem knows that it
-- is the same list now at 1.
--
-- sendList＠0 xs =
--   tag xs ,
--   case xs
--     { []       ↦ tt
--     , (x ∷ xs) ↦ x , sendList＠0 xs
--     }
--
-- sendList＠1 = hole xs , case xs { [] ↦ tt , [] | (_ ∷ _) ↦ hole x , xs = sendList＠1 , (x ∷ xs) }
--
-- I also can implement them at once:
--
-- sendList xs =
--   send(0 → 1) (tag xs) ,
--   case xs
--     { []       ↦ (tt＠0 , []＠1)
--     | (x ∷ xs) ↦ (x' = send(0 → 1) x) , (xs' = sendList xs) , (tt＠0 , (x' ∷ xs')＠1)
--     }
--
--------------------------------------------------------
-- Example: summing n numbers: https://arxiv.org/pdf/1911.00705.pdf (page 16)
--
-- Idea: client sends `n` and then n numbers, the server sums them all up, and
-- returns the result.
--
-- Ex₊ : (n : ℕ＠0,1) -> CommType{0,1}
-- Ex₊ zero = [ ℕ ](1 → 0)
-- Ex₊ (suc n) = [ ℕ ](0 → 1) ⊗ Ex₊ n
--
-- Ex : (n : ℕ＠0) -> CommType{0,1}
-- Ex n = [ Val n ](0 → 1) ⊗ Ex₊ n
--
-- ex₊ : ∀(n ＠ 0,1) -> ∀(v : Vec ℕ n ＠ 0) -> (acc : ℕ ＠ 1) -[ Ex₊ n ]-> ℕ ＠ 0
--
-- ex₊＠0 zero _ = hole res &↑ res
-- ex₊＠0 (suc n) (x ∷ xs) = x , ex＠0 n x
--
-- ex₊＠1 zero acc = acc
-- ex₊＠1 (suc n) acc = hole x , ex₊＠1 n (x + acc)
--
-- Now implemented choreographically:
-- ex₊ zero [] acc = (res＠0 ⇜ acc＠1) , &↑ res
-- ex₊ (suc n) (x ∷ xs) acc = (x＠1 ⇜ x＠0) , ex₊ n xs (acc + x)
--
-- ex : ∀(n ＠ 0) -> ∀(v : Vec ℕ n ＠ 0) -[ Ex n ]-> ℕ ＠ 0
-- ex n v = (n＠1 ⇜ n＠0) , ex₊ n v 0


