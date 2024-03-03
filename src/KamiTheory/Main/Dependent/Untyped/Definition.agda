----------------------------------------------------------
--
-- Untyped terms of the Kami language
--
-- In this file the datatype of untyped terms is defined. This
-- is done generically over an arbitrary higher-order signature,
-- which makes the definition of substitution and weakening
-- very concise.
--
-- The file is originally from a project by Joakim Öhman et al.,
-- but quite some changes were required to integrate a modesystem
-- into it. The overall structure remains the same.
--
----------------------------------------------------------
--
-- Original file by Joakim Öhman et al.
-- See here: https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda
--
-- Original license:
-- ```
--   Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--   Permission is hereby granted, free of charge, to any person obtaining a copy
--   of this software and associated documentation files (the "Software"), to deal
--   in the Software without restriction, including without limitation the rights
--   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
--   copies of the Software, and to permit persons to whom the Software is
--   furnished to do so, subject to the following conditions:

--   The above copyright notice and this permission notice shall be included in all
--   copies or substantial portions of the Software.

--   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
--   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
--   SOFTWARE.
-- ```

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Untyped.Definition where

-- Raw terms, weakening (renaming) and substitution.

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product
open import KamiTheory.ThirdParty.logrel-mltt.Tools.List
import KamiTheory.ThirdParty.logrel-mltt.Tools.PropositionalEquality as PE

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition
open import Data.Vec using ([] ; _∷_ ; _++_ ; lookup) renaming (Vec to StdVec)

open import Agora.Conventions using (𝑖 ; 𝑗 ; 𝒰 ; _､_ ; hasDecidableEquality ; _≡_ ; yes ; no)
open import KamiTheory.Basics

-- Kami: We additionally parametrize over a set P, describing the set of locations
-- module KamiUntyped (P : ModeSystem 𝑖) where
private variable
  P : ModeSystem 𝑖

infixl 30 _∙_
infix 30 Π_/▹_
infix 30 Π_/_▹_
infix 30 Π_//_▹_
infixr 32 _/_▹▹_
infixr 32 _/▹▹_
infix 30 Σ_/_▹_
infix 30 Σ_//_▹_
infixr 32 _××_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


module _ {A : 𝒰 𝑖} {{_ : hasDecidableEquality A}} where
  β-decide-≡-Vec : ∀{n} -> {x : StdVec A n} -> decide-≡-Vec x x ≡ yes refl
  β-decide-≡-Vec = {!!}

  {-# REWRITE β-decide-≡-Vec #-}


-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Term Ps added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

data Con (A : Nat → 𝒰 𝑖) : Nat → 𝒰 𝑖 where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private
  variable
    n m ℓ : Nat


data Metakind : Set where
  term modality : Metakind
  transition : Metakind

-- Representation of sub terms using a list of binding levels

data GenTs (T : 𝒰 𝑗) (A : Nat -> Metakind → 𝒰 𝑖) : Nat → List (Metakind × Nat) → 𝒰 (𝑖 ､ 𝑗) where
  []  : {n : Nat} → GenTs T A n []
  _⦊_∷_ : ∀{k : Metakind} -> {n b : Nat} {bs : List (Metakind × Nat)}
            -> (μs : T) -> (t : A (b + n) k) -> (ts : GenTs T A n bs)
            → GenTs T A n ((k , b) ∷ bs)

infixr 20 _⦊_∷_

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term


open import Data.Nat using (suc ; zero)

pattern n0 = zero
pattern n1 = suc (zero)

data MainKind : (ns : List (Metakind × Nat)) → Set where
  Ukind : MainKind []

  Pikind  : MainKind ((term , n0) ∷ (term , n1) ∷ [])
  Lamkind : MainKind ((term , n1) ∷ [])
  Appkind : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  Sigmakind : MainKind ((term , n0) ∷ (term , n1) ∷ [])
  Prodkind  : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Fstkind   : MainKind ((term , n0) ∷ [])
  Sndkind   : MainKind ((term , n0) ∷ [])

  -- booleans
  𝓀-BB : MainKind []
  𝓀-trueₜ : MainKind []
  𝓀-falseₜ : MainKind []
  𝓀-boolrec : MainKind ((term , n0) ∷ (term , n1) ∷ (term , n0) ∷ (term , n0) ∷ [])

  -- natural numbers
  Zerokind   : MainKind []
  Suckind    : MainKind ((term , n0) ∷ [])
  Natreckind : MainKind ((term , n1) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ [])

  -- vectors
  Veckind    : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Nilkind    : MainKind []
  Conskind   : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Vecreckind : MainKind ((term , (suc n1)) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ [])
  𝓀-head : MainKind ((term , n0) ∷ [])
  𝓀-tail : MainKind ((term , n0) ∷ [])

  -- unit and empty type
  Starkind : MainKind []
  Emptyreckind : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  -- modality system
  𝓀-Modal : MainKind ((term , n0) ∷ []) -- _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Global
  𝓀-mod : MainKind ((term , n0) ∷ [])
  𝓀-letunmod : MainKind ((term , n0) ∷ (term , n1) ∷ (term , n1) ∷ [])


-- local leafs get their own kind

data LeafKind : Set where
  Natkind    : LeafKind
  Emptykind  : LeafKind
  Unitkind   : LeafKind

data Kind : (ns : List (Metakind × Nat)) → Set where
  main : ∀{ns} -> MainKind ns -> Kind ns
  leaf : LeafKind -> Kind []

  -- the transform term gets its own top-level kind
  𝓀-transform : Kind ((transition , n0) ∷ (term , n0) ∷ [])


-- Terms are indexed by its number of unbound variables and are either:
-- de Bruijn style variables or
-- generic terms, formed by their kind and sub terms. The definition is below.
data Term (P : ModeSystem 𝑖) (n : Nat) : 𝒰 𝑖

-- Terms can be of different kinds - we need this to accomodate
-- both modalities and transformations between them.
data KindedTerm (P : ModeSystem 𝑖) (n : Nat) : (k : Metakind) -> 𝒰 𝑖 where
  term : Term P n -> KindedTerm P n term
  modality : SomeModeHom P -> KindedTerm P n modality
  transition : Transition P vis -> KindedTerm P n transition

-- An entry (of the context) consists of a term and a modality annotation.
data Entry (P : ModeSystem 𝑖) (n : Nat) : 𝒰 𝑖 where
  _//_ : Term P n -> SomeModeHom P -> Entry P n

pattern _/_ A μs = A // (_ ↝ _ ∋ μs)
infixl 21 _//_ _/_


-- The definition of terms.
data Term P n where
  gen : {bs : List (Metakind × Nat)} (k : Kind bs) (c : GenTs (Modality P) (KindedTerm P) n bs) → Term P n
  var : (x : Fin n) → Transition P all → Term P n




private
  variable
    A B C D t u v : Term P n
    F E G H : Entry P n

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
pattern UU = gen (main Ukind) []

pattern Π_/▹_ A B = gen (main Pikind) (incl (_ ↝ _ ∋ id) ⦊ term A ∷ id ⦊ term B ∷ [])
pattern Π_/_▹_ A μ B = gen (main Pikind) (incl (_ ↝ _ ∋ μ) ⦊ term A ∷ id ⦊ term B ∷ [])
pattern Π_//_▹_ A μ B = gen (main Pikind) (μ ⦊ term A ∷ id ⦊ term B ∷ [])

pattern Σ_/_▹_ A μ B  = gen (main Sigmakind) (incl (_ ↝ _ ∋ μ) ⦊ term A ∷ id ⦊ term B ∷ [])
pattern Σ_//_▹_ A μ B = gen (main Sigmakind) (μ ⦊ term A ∷ id ⦊ term B ∷ [])




-- function types
pattern lam↦_ t = gen (main Lamkind) (id ⦊ term t ∷ [])
infix 23 lam↦_

pattern _∘[[_]]_ t μ u = gen (main Appkind) (id ⦊ term t ∷ μ ⦊ term u ∷ [])
pattern _∘[_]_ t μ u = gen (main Appkind) (id ⦊ term t ∷ incl (_ ↝ _ ∋ μ) ⦊ term u ∷ [])
infixl 24 _∘[[_]]_ _∘[_]_ _∘_
pattern _∘_ t u = gen (main Appkind) (id ⦊ term t ∷ id ⦊ term u ∷ [])


-- Sum types
prod : (t u : Term P n) → Term P n       -- Dependent products
prod t u = gen (main Prodkind) (id ⦊ term t ∷ id ⦊ term u ∷ [])
pattern _,,_ t u = gen (main Prodkind) (id ⦊ term t ∷ id ⦊ term u ∷ [])

fstₜ : (t : Term P n) → Term P n          -- First projection
fstₜ t = gen (main Fstkind) (id ⦊ term t ∷ [])

sndₜ : (t : Term P n) → Term P n          -- Second projection
sndₜ t = gen (main Sndkind) (id ⦊ term t ∷ [])

-- Introduction and elimination of natural numbers.
pattern NN = gen (leaf Natkind) []
pattern zeroₜ = gen (main Zerokind) []
pattern sucₜ t = gen (main Suckind) (id ⦊ term t ∷ [])
pattern natrec A t u v = gen (main Natreckind) (id ⦊ term A ∷ id ⦊ term t ∷ id ⦊ term u ∷ id ⦊ term v ∷ [])

-- booleans
pattern BB = gen (main 𝓀-BB) []
pattern trueₜ = gen (main 𝓀-trueₜ) []
pattern falseₜ = gen (main 𝓀-falseₜ) []
pattern boolrec_into_false:_true:_ t A u v = gen (main 𝓀-boolrec) (id ⦊ term t ∷ id ⦊ term A ∷ id ⦊ term u ∷ id ⦊ term v ∷ [])

-- vectors.
pattern Vec m t = gen (main Veckind) (id ⦊ term m ∷ id ⦊ term t ∷ [])

nilₜ : Term P n                         -- Empty vector.
nilₜ = gen (main Nilkind) []

consₜ : (v : Term P n) → (vs : Term P n) → Term P n -- Append.
consₜ v vs = gen (main Conskind) (id ⦊ term v ∷ id ⦊ term vs ∷ [])

vecrec : (μ η : SomeModeHom P) -> (G : Term P (1+ (1+ n))) (z s l vs : Term P n) → Term P n  -- Vector recursor ( is a binder).
vecrec μ η G z s l vs = gen (main Vecreckind) ((id) ⦊ term G ∷ id ⦊ term z ∷ id ⦊ term s ∷ id ⦊ term l ∷ id ⦊ term vs ∷ [])

pattern headₜ vs = gen (main 𝓀-head) (id ⦊ term vs ∷ [])
pattern tailₜ vs = gen (main 𝓀-tail) (id ⦊ term vs ∷ [])

-- Unit and empty type
pattern Empty = gen (leaf Emptykind) []
pattern Unit = gen (leaf Unitkind) []

star : Term P n                        -- Unit element
star = gen (main Starkind) []

Emptyrec : (A e : Term P n) → Term P n   -- Empty type recursor
Emptyrec A e = gen (main Emptyreckind) (id ⦊ term A ∷ id ⦊ term e ∷ [])


-- Modal types
pattern Modal A μ     = gen (main 𝓀-Modal) (μ ⦊ term A ∷ []) --  id ⦊ (modality (((_ ↝ _ ∋ μ)))) ∷ [])
pattern ⟨_∣_⟩ A μ = Modal A (incl (_ ↝ _ ∋ μ))

-- modal terms
pattern mod[[_]] μ t        = gen (main 𝓀-mod) (μ ⦊ term t ∷ [])
pattern mod[_] μ t        = mod[[ incl (_ ↝ _ ∋ μ) ]] t
pattern letunmod[[_]]_into_by_ μ t Y s  = gen (main 𝓀-letunmod) (μ ⦊ term t ∷ id ⦊ term Y ∷ id ⦊ term s ∷ [])
pattern letunmod[_]_into_by_ μ t Y s  = letunmod[[ incl (_ ↝ _ ∋ μ) ]] t into Y by s
pattern letunmod_into_by_ t Y s = letunmod[ id ] t into Y by s
infix 25 letunmod[[_]]_into_by_ letunmod[_]_into_by_ letunmod_into_by_

-- special modal term for Kami
pattern transform ξ t  = gen (𝓀-transform) (id ⦊ transition ξ ∷ id ⦊ term t ∷ [])




-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType



------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Nat → Nat → Set where
  id    : {n : Nat} → Wk n n                      -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ Nat.zero = ρ
liftn ρ (1+ n)   = lift (liftn ρ n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List (Metakind × Nat)} (ρ : Wk m n) (c : GenTs (Modality P) (KindedTerm P) n bs) → GenTs (Modality P) (KindedTerm P) m bs
  wkGen ρ []                = []
  wkGen ρ (_⦊_∷_ {b = b} ξs t c) = ξs ⦊ (wk-Kinded (liftn ρ b) t) ∷ (wkGen ρ c)

  wk-Kinded : ∀{k : Metakind} -> {m n : Nat} (ρ : Wk m n) (t : KindedTerm P n k) → KindedTerm P m k
  wk-Kinded ρ (term x) = term (wk ρ x)
  wk-Kinded ρ (transition ξ) = transition ξ
  wk-Kinded ρ (modality μ) = modality μ

  wk : {m n : Nat} (ρ : Wk m n) (t : Term P n) → Term P m
  wk ρ (var x ξ)   = var (wkVar ρ x) ξ
  wk ρ (gen k c) = gen k (wkGen ρ c)


-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term P n → Term P (1+ n)
wk1 = wk (step id)





-- Non-dependent version of Π.

_//_▹▹_ : Term P n → Modality P -> Term P n → Term P n
A // μ ▹▹ B = Π A // μ ▹ wk1 B

_/_▹▹_ : ∀{k l} -> Term P n → ModeHom P k l -> Term P n → Term P n
A / μ ▹▹ B = Π A / μ ▹ wk1 B

_/▹▹_ : ∀{m : Mode P} -> Term P n → Term P n → Term P n
_/▹▹_ {m = m} A B = Π A / id {m = m} ▹ wk1 B


-- Non-dependent products.

_××_ : ∀{k : Mode P} -> Term P n → Term P n → Term P n
_××_ {k = k} A B = Σ A // incl (k ↝ k ∋ id) ▹ wk1 B


------------------------------------------------------------------------
-- Pushing transitions
--
-- To push transitions down, we actually need a transition for each
-- variable. We call such a collection `Transitions`


-- A term like `λ (A / μ) . λ (B / η) . λ (C / ω) . t` corresponds to a list
-- (ω ∷ η ∷ μ ∷ []), which looks inverted because the first item has to belong to
-- variable zero.
-- Nevertheless, this vector should return the following modalities for the vars:
-- 0 -> ω ◆ η ◆ μ
-- 1 -> η ◆ μ
-- 2 -> μ
VarExtensionWk : (P : ModeSystem 𝑖) (n : Nat) -> 𝒰 _
VarExtensionWk P n = StdVec (Modality P) n

data isTransitionRequired : Set where
  required notRequired : isTransitionRequired

record Transitions (P : ModeSystem 𝑖) (n : Nat) (r : Range) : 𝒰 𝑖 where
  constructor transitions
  field get : Transition P r
  field postExtension : Modality P
  field requirements : StdVec isTransitionRequired n

open Transitions public

concatAll : VarExtensionWk P n -> Modality P
concatAll [] = id
concatAll (x ∷ vs) = x ◆-Modality concatAll vs

getVarTransition : VarExtensionWk P n -> Fin n -> Modality P
getVarTransition (x ∷ xs) x0 = concatAll (x ∷ xs)
getVarTransition (x ∷ xs) (_+1 i) = getVarTransition xs i

uniformExtension : VarExtensionWk P n
uniformExtension {n = n0} = []
uniformExtension {n = 1+ n} = id ∷ uniformExtension

fillVec : ∀{A : Set} -> A -> StdVec A n
fillVec {n = n0} a = []
fillVec {n = 1+ n} a = a ∷ (fillVec a)

-- a uniform transitions collection can be created from a single
-- transition
uniformTransitions : ∀{v} -> Transition P v -> Transitions P n v
uniformTransitions ξ = transitions ξ id (fillVec required)

intoModalities : StdVec (SomeModeHom P) n -> StdVec (Modality P) n
intoModalities [] = []
intoModalities (x ∷ xs) = incl x ∷ intoModalities xs

-- The μs are the new modalities, the xs are the already preexisting, thus
-- we have to do simple appending here
liftVarExtension : ∀{b} -> (μs : StdVec (SomeModeHom P) b) -> (xs : VarExtensionWk P n) -> VarExtensionWk P (b + n)
liftVarExtension μs xs = intoModalities μs ++ xs


liftPostTransition : ∀{b} -> Modality P -> Transitions P n all -> Transitions P (b + n) all
liftPostTransition μ (transitions ξ post reqs) = transitions ξ (μ ◆-Modality post) (fillVec notRequired ++ reqs)

getTransition : Fin n -> Transitions P n all -> Transition P all
getTransition x ξs with lookup (requirements ξs) x
... | notRequired = id
... | required = (postExtension ξs ↷-Transition get ξs)

-- Pushes a transition down the term. We push it until the next
-- `transform` term or variable.
mutual
  push-Gen : ∀{bs} -> Transitions P n all -> GenTs (Modality P) (KindedTerm P) n bs -> GenTs (Modality P) (KindedTerm P) n bs
  push-Gen ξs [] = []
  push-Gen ξs (μ ⦊ t ∷ ts) = μ ⦊ push-Kinded (liftPostTransition μ ξs) t ∷ push-Gen ξs ts

  push-Kinded : ∀{k} -> Transitions P n all -> KindedTerm P n k -> KindedTerm P n k
  push-Kinded ξs (term x) = term (push ξs x)
  push-Kinded ξs (modality μ) = modality μ
  push-Kinded ξs (transition ζ) = transition ζ

  push : Transitions P n all -> Term P n -> Term P n
  push ξs (gen (main x) c) = gen (main x) (push-Gen ξs c)
  push ξs (gen (leaf x) c) = gen (leaf x) []
  push ξs (transform ζ t) with ξ' , ζ' <- commute-Transition-vis ζ (get ξs)
                          = transform ζ' (push (transitions ξ' (postExtension ξs) ((requirements ξs))) t)
  push ξs (var x ζ) = var x (ζ ◆-Transition (getTransition x ξs))

  -- TODO change system so we don't need this case.
  push x (gen 𝓀-transform (_ ⦊ transition x₁ ∷ _ ⦊ term x₂ ∷ [])) = zeroₜ


_^[_] : Term P n -> ∀{μ η : SomeModeHom P} -> ModalityTrans P all μ η -> Term P n
_^[_] A ξ = push (uniformTransitions (incl ξ)) A

infix 60 _^[_]



record Shiftings (P : ModeSystem 𝑖) (n : Nat) : 𝒰 𝑖 where
  constructor shiftings
  field get : SomeModeHom P
  field requirements : StdVec isTransitionRequired n

open Shiftings public

-- NOTE: we currently ignore μ, but it might be required in the future
liftShifting : ∀{b} -> Modality P -> Shiftings P n -> Shiftings P (b + n)
liftShifting μ (shiftings ξ reqs) = shiftings ξ (fillVec required ++ reqs)

getShifting : Fin n -> Shiftings P n -> Modality P
getShifting x ξs with lookup (requirements ξs) x
... | notRequired = id
... | required = (incl (get ξs))


mutual
  shift-Gen : ∀{bs} -> Shiftings P n -> GenTs (Modality P) (KindedTerm P) n bs -> GenTs (Modality P) (KindedTerm P) n bs
  shift-Gen ξs [] = []
  shift-Gen ξs (μ ⦊ t ∷ ts) = μ ⦊ shift-Kinded (liftShifting μ ξs) t ∷ shift-Gen ξs ts

  shift-Kinded : ∀{k} -> Shiftings P n -> KindedTerm P n k -> KindedTerm P n k
  shift-Kinded ξs (term x) = term (shift ξs x)
  shift-Kinded ξs (modality μ) = modality μ
  shift-Kinded ξs (transition ζ) = transition ζ

  shift : Shiftings P n -> Term P n -> Term P n
  shift ξs (Π A // μ ▹ B) = Π (shift ξs A) // μ ◆-Modality (incl (get ξs)) ▹ shift (liftShifting μ ξs) B
  shift ξs (gen (main x) c) = gen (main x) (shift-Gen ξs c)
  shift ξs (gen (leaf x) c) = gen (leaf x) []
  shift ξs (transform ζ t) = transform ζ (shift ξs t)
  shift ξs (var x ζ) = var x (ζ ↶-Transition getShifting x ξs)

  -- TODO change system so we don't need this case.
  shift x (gen 𝓀-transform (_ ⦊ transition x₁ ∷ _ ⦊ term x₂ ∷ [])) = zeroₜ

_↶[_] : ∀{a b} -> Term P n -> ModeHom P a b -> Term P n
_↶[_] t μ = shift (shiftings (_ ↝ _ ∋ μ) (fillVec notRequired)) t



mutual
  untransform-Gen : ∀{bs} -> GenTs (Modality P) (KindedTerm P) n bs -> GenTs (Modality P) (KindedTerm P) n bs
  untransform-Gen [] = []
  untransform-Gen (μs ⦊ t ∷ x) = μs ⦊ untransform-KindedTerm t ∷ untransform-Gen x

  untransform-Term : Term P n -> Term P n
  untransform-Term (gen (main x) c) = gen (main x) (untransform-Gen c)
  untransform-Term (gen (leaf x) c) = gen (leaf x) []
  untransform-Term (gen 𝓀-transform (_ ⦊ (transition ξ) ∷ _ ⦊ (term t) ∷ [])) = push (uniformTransitions (into-all-Transition ξ)) (untransform-Term t)
  untransform-Term (var x x₁) = var x x₁

  untransform-KindedTerm : ∀{k} -> KindedTerm P n k -> KindedTerm P n k
  untransform-KindedTerm (term x) = term (untransform-Term x)
  untransform-KindedTerm (modality μ) = modality μ
  untransform-KindedTerm (transition ξ) = transition ξ

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : (P : ModeSystem 𝑖) -> Nat → Nat → 𝒰 𝑖
Subst P m n = Fin n → Term P m

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst P m (1+ n) → Term P m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst P m (1+ n) → Subst P m n
tail σ x = σ (x +1)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst P m n) (x : Fin n) → Term P m
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst P n n
idSubst x = var x (id)

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst P m n → Subst P (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst P m n) → Subst P (1+ m) (1+ n)
liftSubst σ x0     = var x0 id
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst P k m → (n : Nat) → Subst P (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst P m n
toSubst pr x = var (wkVar pr x) id

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : {bs : List (Metakind × Nat)} (σ : Subst P m n) (g : GenTs (Modality P) (KindedTerm P) n bs) → GenTs (Modality P) (KindedTerm P) m bs
  substGen σ  []      = []
  substGen σ (_⦊_∷_ {b = b} ξs t ts) = ξs ⦊ subst-Kinded (liftSubstn σ b) t ∷ (substGen σ ts)

  subst-Kinded : ∀{k : Metakind} (σ : Subst P m n) (t : KindedTerm P n k) → KindedTerm P m k
  subst-Kinded σ (term x) = term (subst σ x)
  subst-Kinded σ (transition ξ) = transition ξ --  (subst σ t)
  subst-Kinded σ (modality μ) = modality μ
  -- subst-Kinded σ (x // p) = subst σ x // p

  subst : (σ : Subst P m n) (t : Term P n) → Term P m
  subst σ (var x ξ) = push (uniformTransitions ξ) (substVar σ x) -- if we substitute a variable with an annotation, we have to push this annotation down the term
  subst σ (gen x c) = gen x (substGen σ c)



-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst P m n → Term P m → Subst P m (1+ n)
consSubst σ t  x0    = t
consSubst σ t (x +1) = σ x

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term P n → Subst P n (1+ n)
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst P ℓ m → Subst P m n → Subst P ℓ n
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk ℓ m → Subst P m n → Subst P ℓ n
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst P ℓ m → Wk m n → Subst P ℓ n
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term P (1+ n)) (s : Term P n) → Term P n
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term P (1+ n)) (s : Term P (1+ n)) → Term P (1+ n)
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


-- B-subst : (σ : Subst P m n) (W : BindingType) (F : Term P n) (G : Term P (1+ n))
--         → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
-- B-subst σ BΠ F G = PE.refl
-- B-subst σ BΣ F G = PE.refl


