
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
--
----------------------------------------------------------------
-- Example: indirect information: https://link.springer.com/article/10.1007/s10270-022-01040-x (example 3.1, page 4)
--
-- Idea: (quote)
-- ```
--    As a running example, let us consider three par-
--    ticipants p, q, r. p chooses whether to send a message to r or
--    not; this choice is communicated to r through an intermediate
--    participant q.
-- ```
--
-- Note: renaming processes [p,q,r] ↦ [0,1,2]
--
-- Ex : (b : Bool ＠ 0) -> CommType{0,1,2}
-- Ex b = [ Val b ](0 → 1) ⊗ [ Val b ](1 → 2) ⊗ If b ([ A ](0 → 2))
--
-- ex : (b ＠ 0) -> (a : A ＠ 0) -> If b A ＠ 2
-- ex b a = (b＠2 ⇜ b＠1 ⇜ b＠0) , case b { true ↦ (a＠2 ⇜ a＠0) &↑ a | false ↦ tt}
--
----------------------------------------------------------------
-- Example: two-buyers problem: https://link.springer.com/article/10.1007/s10270-022-01040-x (example 3.2, page 5)
--
-- Idea: (quote)
-- ```
--    A second running example is the well-known
--    two-buyers problem, as in [17]. First Buyer 1 sends a book
--    title to Seller, then Seller sends back a quote to both Buyer 1
--    and Buyer 2, then Buyer 1 tells Buyer 2 how much she wants
--    to contribute, and Buyer 2 tells Seller if she accepts the quote
--    or not. If the deal is drawn, Seller tells Buyer 2 the expected
--    delivery date at her address.
-- ```
--
-- ...
--
----------------------------------------------------------------
-- Example: dining philosophers
--
-- We have three processes which are locally correct, but where
-- combining all of them produces a deadlock.
--
-- The local types look like this:
--
-- P0 : CommType{0,1,2}
-- P0 = [ ℕ ](2 → 0) ⊗ [ ℕ ](0 → 1)
--
-- P1 : CommType{0,1,2}
-- P1 = [ ℕ ](0 → 1) ⊗ [ ℕ ](1 → 2)
--
-- Interestingly enough, we currently have no way to specify
-- invalid (deadlocking) "local" types. If we want to implement
-- three processes, we have to give a global type for them.
-- There is no way to "merge" three "partial" types to get a
-- possibly invalid global type.
--
----------------------------------------------------------------
-- Development/Thinking. Topic: Remote resources, channels
--
-- We have seen that it is nice in some sense that we don't have
-- "local session types". But we still want to extract channels
-- in the sense that we can have a server whose implementation
-- we don't have access to, but who we can still talk to.
--
-- Let us try to use our global types + hyper-local types for that.
--
-- We have a situation where a server can be accessed by various
-- clients... Because assuming we have fixed roles, implementing
-- for only some of the roles is already possible in our theory.
--
-- Idea: we have a "global name service" which can connect us to
-- a server we want to talk with.
--
-- We say that we want to speak with "test.determi.io", and we
-- get a partially implemented term with the type of this program.
-- This means that we need to at least be able to compare types
-- to make sure that our partner behaves as we expect.
--
-- getRandom : ℕ ＠ 0
-- getRandom =
--   (T : CommType{0,Server}, t : T↓Server) <- getChannel "test.determi.io"
--   assert T ≡ [ n : ℕ ](0 → Server) ⊗ [ Fin n ](Server → 0)
--   let t₀ : (𝟙 -[ T ]-> ℕ ＠ 0)  ↓ 0
--          = (n : ℕ) ⊗ (- Fin n) ⊗ ℕ
--       t₀ = 100 , hole i , cast i
--   in (pair t t0) tt : ℕ ＠ 0
--
-- Here we get `t`, a partial implementation of the `T` protocol.
-- If we have a partial implementation in scope, we are obliged to
-- discharge such an assumption. We do this by providing the rest
-- of the implementation with `t₀`, and then we discharge by combining
-- them with `pair`.
--
-- This suggests that there is some kind of scheduling operation
-- which takes a partial implementation and runs it, but passes
-- the "channel" (without I/O-state) somewhere else, such that
-- another process can connect to this server.
--
-- t₁ :{1} ℕ＠1 -[ T ]-> ℕ＠1
-- t₁ = ?
--
-- t : (∀ α. Channel T (0,α) {0}) -> ℕ＠1 -[ T ]-> ℕ＠1
-- t c n = pair (c 1) t₁
--
-- Where `(∀ α. Channel T (0,α) {0})` means that this is a channel
-- to an implementation of `T` where the type T is located at 0 and α,
-- it is implemented only for 0, and we can choose ourselves what α
-- should be.

----------------------------------------------------------------
-- Current questions:
--  - How do we represent "no communication"? Is it enough if we say that
--    the type 𝟙 does not require any communication? Do we need sth more
--    formal?
--  - Currently, the local implementations to do not retain the information
--    with whom they communicate. This is not future-proof, in the sense
--    that during compilation we are definitely going to need this information.
--    Usually such information is kept in "local session types" which we currently
--    do not represent. This has the effect that the dining philosopher deadlock
--    cannot even be stated.
--  - What is the relationship between partial implementations and channels?
--    partial implementations have input and output types, and have to be "scheduled"
--    in order to get a channel which can be communicated to other processes...
--    In some sense, the scheduler owns the processes which it has scheduled...
--    We might have a difference between "internal" and "external" locations:
--    The scheduler in "Topic: Remote resources, channels" owns the location `0`,
--    while the term `t` does not. It can still instantiate the protocol T to {0,1},
--    but it cannot schedule anything to location 0.
