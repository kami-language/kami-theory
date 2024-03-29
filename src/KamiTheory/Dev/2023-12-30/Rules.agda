-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2023-12-30.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

open import KamiTheory.Dev.2023-12-26.Core

{-# BUILTIN REWRITE _≡_ #-}

Name = ℕ

module _ {A B : 𝒰 𝑖} where
  transp-≡ : (A ≡ B) -> A -> B
  transp-≡ refl-≡ a = a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
  cong₂-≡ : (f : A -> B -> C) -> ∀{a₀ a₁ : A} -> ∀{b₀ b₁ : B} -> a₀ ≡ a₁ -> b₀ ≡ b₁ -> f a₀ b₀ ≡ f a₁ b₁
  cong₂-≡ f refl-≡ refl-≡ = refl-≡

-- cong-≡ : {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> (f : (a : A) -> B a) -> {a b : A} -> (a ≡ b) -> f a ≡ f b
cong-≡ : {A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (f : A -> B) -> {a b : A} -> (a ≡ b) -> f a ≡ f b
cong-≡ f refl-≡ = refl-≡

ap₀ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≡ b -> A
ap₀ {a = a} _ = a

ap₁ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≡ b -> A
ap₁ {b = b} _ = b

J1 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑘} -> ∀{a b : A} -> (p : a ≡ b) -> (F : A -> 𝒰 𝑗) -> (f : ∀ a -> F a -> B) -> (x : F a) -> f b (transp-≡ (cong-≡ F p) x) ≡ f a x
J1 refl-≡ F f x = refl-≡



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
--   term we create a new hole, and as such, `(∂ hole) Γ ≡ (Γ , A)`
--   which means that (b : B a) gets a new A-variable. While if we don't
--   create a new hole, but merely project one from the context, then
--   this is also visible in the derivative: `(∂ (var x)) (Γ , x , Δ) ≡ (Γ , Δ , x)`.
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
--
--  T : {} ⊢ ∀ (n : ℕ ＠ {0 , 1}) -> CommType{0,1}
--  T zero = 𝟙
--  T (suc n) = [ A ](0 → 1) ⊗ T n
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
--
----------------------------------------------------------------
-- Remote resources & location ownership
--
-- Let us assume that we want proper channels. Then we have multiple
-- concepts:
--  1. The location (server) where the code is executed.
--  2. The location (scheduler) which knows about the server and can
--     provide us with a channel to it.
--  3. The location (client) which accesses the server.
--
-- Communication types (channels) are implemented incrementally.
-- Each location can schedule part of a communication, and gets
-- an according channel as proof of scheduling. Channels with matching
-- role implementations can be joined. A fully implemented channel can
-- be consumed by whichever location. This location is playing the role
-- of the connector, i.e., telling the individual participants their
-- partners, and thus establishing the connection/protocol.
--
-- Assume I have `T : CommType{α,β}`.
--
-- T : CommType{α,β}
-- T = [ ℕ ](α → β) ⊗ [ ℕ ](β → α)
--
-- t₀ : {0,(α)} -> ℕ＠0 -[ T ]-> ℕ＠0
-- t₀ = ?
--
-- step : {S,0} -> ℕ＠0 -> (ℕ＠0 × Chan T {0,(α)} ＠S)
-- step n = schedule t₀ n (0 under S)
--
-- scheduler :{S} -> ℕ＠S -> !(Chan T {0,(α)})
-- scheduler = ?
--
-- Now assume I have two processes talking with the scheduler.
--
-- U : CommType{S,a,b}
-- U = [Chan T {0,(α)}](S → a) ⊗ [Chan T {0,(β)}](S → b)
--
--
-- u₁ :{(0),1} -[ T ]-> 𝟙
-- u₁ = hole n , n + 1
--
-- u :{S,1,2} -> ℕ＠S -[ U ]-> 𝟙
-- u＠0 = hole c₀ , connect＠1 {c₀ , schedule u₁}
--             ~~                    ~~~~~~~~~~~
--             ^                     ^ Chan T {(0), 1}
--             | Chan T {0,(α)}
--
--                             ~~~~~~~~~~~~~~~~~
--                             ^ Chan T {(0),(1)}
--
-- We see that if we have `f : {0,1} -> A -[ U ]-> B`, we can
-- do `f↓0 : {0,(1)} -> A↓0 -[ U ]-> B↓0`.
-- And we have:
-- f ≡ λ a ↦ connect {schedule (f↓0 a↓0) , schedule (f↓1 a↓1)}
--
-- The idea is as follows:
--  - partial implementations are copyable, but not proper terms,
--    in that they cannot be executed stand-alone.
--  - partial implementations can be scheduled, which creates a
--    channel signifying the "implemented vs missing" information.
--    This channel is not copyable.
--  - Channels can be merged if they implement the different aspects
--    of the same communication type
--  - Once a channel is fully implemented, it can be discarded with `connect`.
--
-- Again:
-- We see that if we have `f : {0,1} -[ U ]-> B`, we can
-- do `f↓0 : {0,(1)} -[ U ]-> B↓0`.
-- And we have:
-- f ≡ (let (ca , va) = schedule (f↓0)
--           (cb , vb) = schedule (f↓1)
--      in connect {ca , cb} , (va , vb)
--      )
--
----------------------------------------------------------------
-- Schedule and related things
--
-- The current problem is that schedule acts on two locations.
-- There is the hosts' location and the clients'. The question is,
-- is this really required, or just accidental?
-- What schedule has to do, is:
--  - take a partial implementation of a Comm-Type and instantiate
--    it once, providing us with the return type, and with the
--    Channel for communicating with this instance.
-- It seems like this behaviour does not require multiple locations.
--
-- On the other hand, such a scheduled computation has to run on
-- a different thread than the scheduler because while the scheduler
-- is free to act and send the channel, the scheduled task has to
-- wait until it is connected...
--
-- This means that a choreography `f : {0,1} -[ T ]-> B` is itself
-- not yet scheduled? We can schedule it, and what we get, is a scheduling
-- of the parts on the locations `0` and `1`. But this means that
-- there is also the (full) channel on the supervisor location which
-- is dropped.
--
-- so we have to say:
--
-- t : {S,0,1} -> B＠{0,1}
-- t = let (c , v) = schedule f in connect c , v
--          ~   ~
--          ^   ^ v : B ＠{0,1}
--          | c : Chan T {(0),(1)} ＠S
--
-- Is a supervisor divisible from a scheduled process? That is,
-- is there a term which describes "scheduling" individually for
-- S and 0? Can I project to only S or only 0?
--
-- Apriori it seems like communication between supervisor and
-- process is different than between various processes. This means
-- that I cannot project onto every location.
--
--
-- Locally, a choreography begins with:
--  - Knowing my own code
--  - Knowing the identity of my communication partners
--
-- This means: If I know the identity, I don't need any communications
-- to start... Well not exactly. I still need to know that my partners
-- are actually also doing the appropriate thing. This (virtual) information
-- has to be delivered to me from my supervisor. Which again is only possible
-- if my supervisor is behaving correctly and going to give me that information.
-- Thus matching choreographies are not solvable from an "information"
-- point of view.
--
-- Now assume that the type system can guarantee me that, if I know my partners,
-- that they are doing the correct thing.
--
-- For that, we take choreographies as basis. Partial implementations are especially
-- marked. The program is only well-written if it is a combined term (defined for
-- all participants).
--
----------------------------------------------------------------
-- About external participants
--
-- What we want to allow is: Defining a server which accepts connections
-- from various clients and executes choreographies with them.
--
-- This is an asymetric situation: The choreographies themselves are
-- for two participants, but the overall architecture is one where
-- the server does not know the names and locations of its clients before-
-- hand. This means that we are required to encode this somehow.
--
-- This means, we have a two-loc choreography T.
--
-- T : CommType{0,α}
-- T = ?
--
-- Now we want to create a server which does not know its clients.
--
-- Server : {0} -[ ν α. T{0,(α)} ]-> 𝟙＠0
--
-- The interesting thing is that `ν α` is part of the CommType.
-- Which makes sense since there has to happen a communication
-- to connect a client with the server.
--
----------------------------------------------------------------
-- Indeterminacy
--
-- Assume I have three locations {0,1,2}. Now we want to write a
-- CommType{0,1,2} which expresses the fact that 2 will receive a
-- message from either 0 or 1, without knowing from whom - until
-- it gets the message.
--
-- This means we have something like:
--
-- S : CommType{0,1,2}
-- S = μ＠0 ∈ {1,2}. [ A ](μ → 0)
--
-- Now:
-- s₁ : {(0),1,(2)} -> A＠1 -[ S ]-> 𝟙＠1
-- s₁ a = (μ = 1) , a
--
-- s₂ : {(0),(1),2} -[ S ]-> 𝟙＠2
-- s₂ = (μ = 1) , tt
--
-- s₀ : {0,(1),(2)} -[ S ]-> A＠0
-- s₀ = (select-hole μ) , hole a , a
--
-- We need that both s₁ and s₂ decide on the same role to send,
-- s₀ does not need to participate in the decision, only has to
-- receive the outcome.
--
-- But this is like this because μ is in a contravariant position.
-- If we had `μ∈{1,2}. [ A ](0 → μ)`, then we would send a message
-- to either of {1,2} - but these processes don't know who is going
-- to be the target. We might say that there has to be some `μ＠{0,1,2}`,
-- though we don't care how it is decided. So we might say:
--
-- S : μ＠{0,1,2} ∈ {1,2} -> CommType{0,1,2}
-- S μ = [ A ](μ → 0)
--
-- s₁ : (μ : {1,2} ＠{0,1,2}) -> A＠μ -[ S μ ]-> A＠0
--
-- So what we need is some communication which can create
--
-- f : {0,1,2} -> X -> {1,2}＠{0,1,2}
-- f = ?
--
-- Then we can do
-- g : {0,1,2} -> (x : X) -> A＠(f x) -[ S (f x) ]-> A＠0
--
-- The thing is that in this case, the participants are already clear.
-- When we have a server and a random client though, the participants
-- are potentially everyone on the internet.
--
-- This means that the procedure to choose who is going to connect to
-- the server involves an arbiter. But that does not solve the underlying
-- problem. Since there still needs to be some connection event where one
-- client connects to the arbiter, who doesn't know where the connection
-- might come from.
--
-- The solution that first, there has to be a communication which decides
-- the source-role is not applicable since this would be a communication
-- between all devices on the net.
--
-- This means that there is a CommType as follows:
--
-- T : CommType{0,1,2}
-- T = (Open μ∈{1,2} → 0) ⊗ [ A ](μ → 0)
--
-- s₁ : {(0),1,(2)} -[ T ]-> 𝟙
-- s₁ = open 0 , a₁ | tt
--
-- s₂ : {(0),1,(2)} -[ T ]-> 𝟙
-- s₂ = open 0 , a₂ | tt
--
-- The interesting thing is that we don't know whether the connection
-- will be successful. 
--
-- Also, this makes the 1 and 2 participants of T more optional.
-- We don't know whether they will participate...
--
-- T : CommType{0,{1,2}}
-- T = (Open μ∈{1,2} → 0) ⊗ [ A ](μ → 0)
--                            ~~~~~~~~~~~~
--                            ^ : CommType{0,μ} <- here μ is no longer optional,
--                                                 because a decision has been made.
--
-- This means that T does not have to be implemented for the optional roles...
-- But we need a "global name" for other processes to participate?
-- Or we say that `Port 5000 : RoleSet`, and:
--
-- T : (R : Roleset) -> CommType{0,{R}}
-- T = (Open μ∈R → 0) ⊗ [ A ](μ → 0)
--
-- Then we can:
-- main =
--   let R : Roleset
--       R = newroleset
--
--       t : {0} -[ T R {0} ]-> 𝟙
--       t = ?
--
--       s : {1 ∈ R} -[ T (1∈R) {1} ]-> 𝟙
--       s = ?
--
-- Let's reiterate:
-- T : (R : RoleSet) -> CommType{0,μ∈R,ν∈R}
-- T R = Accept μ. [ A ](μ → 0) ⊗ Accept ν. [ A ](0 → ν)
--
-- t₀ : (R : RoleSet) -[ T R ＠ 0 ]-> 𝟙
-- t₀ R = accept μ , hole a , accept ν , a
--
-- R : RoleSet
-- R = Global
--
-- t₁ : {1} -> A＠1 -[ T R ＠ 1 ]-> A＠1
-- t₁ a = connect μ { μ = 1 ↦ a , a                                               : T R ＠ 1 (μ ≔ 1)
--                  | μ ≠ 1 ↦ connect ν { ν = 1 ↦ hole b , b | ν ≠ 1 ↦ a }     : T R ＠ 1 (μ ≠ 1)
--                  }                      ~~~~~~~~~~~~~~~~~~~
--                                         ^ : T R ＠ 1 (μ ≠ 1)(ν = 1)
--
-- Now to reduce these terms, we need to know the exact R, and we need to
-- consider all possibilities for (μ ∈ R , ν ∈ R).
--
-- Can we extract the indeterministic source or do we have to apply it step-by-step?
-- If things get dependently typed, step-by-step is the only way.
--
-- Given a T : CommType{...}, we get Trace T : TraceType{...}, the tracetype
-- tells us which choices appear during execution.
--
-- If we have a term `t : {...} -[ T ]-> X`, then we can compute
-- `t ⇝[ c ] : X` if we have `c : Trace T`. For choreographies
-- this `Trace T` is a singleton type because the communication
-- happens deterministically, once one knows all input data. For
-- more advanced communication patterns this is not so. Thus, we can
-- forget the -[ T ]-> annotation only if `Trace T` is trivial.
--
-- Adding open connections with `Accept μ. t` terms, the trace type
-- is no longer deterministic (contractible). This means that the
-- execution of such a term might (!) be nondeterministic, and can
-- be only predicted if we know all choices beforehand (c : Trace T).
--
--
----------------------------------------------------------------
-- Variable forwarding
--
-- For channel types to be dependent, we need to have knowledge over a common
-- Γ{0,1} context. Now assume I have [ a : A＠0 ], how do I get the knowledge
-- accross to 1? 
--
-- If I have:
--
-- T : CommType{0,1}
-- T = ⟮0 → 1⟯[ A ] ⊗ ⟮1 → 0⟯[ B ]
--
-- t₁ : (-A ⊗ +B) -> T↓1
-- t₁ (a , b) = hole x , (a := x) b
--
-- or
--
-- t₁ (a , b) = a , b
--
--
----------------------------------------------------------------
-- Examples for Olivia
--
-- T : CommType{0,1}
-- T = (a : ⟮0 → 1⟯[ A ]) ⊗ ⟮1 → 0⟯[ B a ]
--
-- t₀ : (f : (A -> B)＠1) -[ T ＠ 1 ]-> 𝟙
--
-- t₁ : (a : A＠0) -[ T ＠ 0 ]-> B＠0
--
--
--
-- Also eine Frage an dich, angenommen wir haben
--
-- T : CommType{0,1}
-- T = ⟮0 → 1⟯[ A ] ⊗ ⟮1 → 0⟯[ B ]
--
-- und dann wollen wir T fuer beide rollen einzeln implementieren. Die Idee ist, dass fuer die implementation *nur* die lokalen typen relevant sind und es ueberhaupt keine rollenannotationen gibt. Ich hab jetzt davor bei unseren Beispielen aber trotzdem immer so globale types (also mit @0 und @1 annotationen) fuer die lokalen implementationen t0 und t1 geschrieben... Wie wuerdest du die echten lokalen types fuer die beiden folgenden zueinander passenden implementationen von T aufschreiben? Ich hab die mal wieder mit so "fake local types" aufgeschrieben:
--
-- t₀ : (f : (A -> B)＠1) -[ T ＠ 1 ]-> 𝟙
--
-- t₁ : (a : A＠0) -[ T ＠ 0 ]-> B＠0
--
--
----------------------------------------------------------------
-- Without negative types
--
-- T : CommType{0,1}
-- T = [ A ](0 → 1)
--
-- t₀ : A -> ∑ A -> 𝟙
-- t₀ a = a , tt
--
-- t₁ : ∏ A -> A
-- t₁ = λ a ↦ a
--
-- t : (a : A ＠ 0) -[ T ]-> A＠1
-- t a = (b＠1 ⇜ a＠0) ▶ b
--
-- _⇜_▶_
--
----------------------------------------------------------------
--
-- T : CommType{0,1,2}
-- T = ⟮0 → 1⟯[ A ] ⊗ ⟮1 → 2⟯[ B ] ⊗ ⟮2 → 0⟯[ B ]
--
-- T＠0 = ∑ 
--
-- h : (a : A＠0) -> (t : T) -> C a ?
-- Γ ⊢ T CommType      Γ , ↓ T ⊢ C Type
-- ------------------------------------
--         Γ ⊢ -[ T ]-> C Type
--
----------------------------------------------------------------
-- Variable forwarding, part 2
--
-- We are, in fact, forwarding arbitrary values. Mostly because
-- variables are not stable under substitution. Now assume that
-- we have `a : A ＠ 0`. We can form the type `Val{0} a ＠ 1`
-- which says that we know the value of `a` at location 1.
-- If we have `t : A ＠ i` and `s : Val{i} t ＠ j` we can build
-- {t,s} : A ＠{i;j}




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
