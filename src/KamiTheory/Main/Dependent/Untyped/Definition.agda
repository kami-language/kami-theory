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

-- {-# OPTIONS --without-K #-}

module KamiTheory.Main.Dependent.Untyped.Definition where

-- Raw terms, weakening (renaming) and substitution.



open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product
open import KamiTheory.ThirdParty.logrel-mltt.Tools.List
import KamiTheory.ThirdParty.logrel-mltt.Tools.PropositionalEquality as PE

-- open import KamiTheory.Main.Dependent.Modality.Definition
open import KamiTheory.Main.Generic.ModeSystem.Definition

open import Agora.Conventions using (𝑖 ; 𝒰)

-- Kami: We additionally parametrize over a set P, describing the set of locations
-- module KamiUntyped (P : 2Graph 𝑖) where
private variable
  P : 2Graph 𝑖

infixl 30 _∙_
infix 30 Π_▹_
infix 30 Π_▹[_]_
infixr 22 _▹▹_
infixr 22 _▹▹[_]_
infix 30 Σ_▹_
infixr 22 _××_
infix 30 ⟦_⟧_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Term Ps added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

data Con (A : Nat → Set) : Nat → Set where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private
  variable
    n m ℓ : Nat


data Metakind : Set where
  term entry modality : Metakind
  transition : Visibility -> Metakind

-- Representation of sub terms using a list of binding levels

data GenTs (A : Nat -> Metakind → 𝒰 𝑖) : Nat → List (Metakind × Nat) → 𝒰 𝑖 where
  []  : {n : Nat} → GenTs A n []
  _∷_ : ∀{k : Metakind} -> {n b : Nat} {bs : List (Metakind × Nat)} (t : A (b + n) k) (ts : GenTs A n bs) → GenTs A n ((k , b) ∷ bs)

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term


open import Data.Nat using (suc ; zero)

pattern n0 = zero
pattern n1 = suc (zero)

data MainKind : (ns : List (Metakind × Nat)) → Set where
  Ukind : MainKind []

  Pikind  : MainKind ((entry , n0) ∷ (term , n1) ∷ (term , n1) ∷ [])
  Lamkind : MainKind ((term , n1) ∷ [])
  Appkind : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  Sigmakind : MainKind ((entry , n0) ∷ (term , n1) ∷ [])
  Prodkind  : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Fstkind   : MainKind ((term , n0) ∷ [])
  Sndkind   : MainKind ((term , n0) ∷ [])

  Zerokind   : MainKind []
  Suckind    : MainKind ((term , n0) ∷ [])
  Natreckind : MainKind ((term , n1) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ [])

  Veckind    : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Nilkind    : MainKind []
  Conskind   : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  Vecreckind : MainKind ((term , (suc n1)) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ (term , n0) ∷ [])

  Starkind : MainKind []

  Emptyreckind : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  -- Kami modality system
  -- 𝓀-/ : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  -- Kami modalities
  -- 𝓀-⇄ : MainKind ((location , n0) ∷ (term , n0) ∷ []) -- Com : Γ ⊢WFSort (A / Global) -> Γ ⊢WFMod Com R A

  -------------------
  -- Kami universe types
  -- 𝓀-Univ-⇄ : MainKind ((location , n0) ∷ (term , n0) ∷ [])

  -------------------
  -- Kami types (global)
  𝓀-Modal : MainKind ((term , n0) ∷ (modality , n0) ∷ []) -- _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Global
  -- 𝓀-＠ : MainKind ((term , n0) ∷ (location , n0) ∷ []) -- _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Global
  -- 𝓀-Com : MainKind ((location , n0) ∷ (term , n0) ∷ []) -- Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global

  -- Kami modality terms
  𝓀-mod : MainKind ((term , n0) ∷ [])
  𝓀-unmod : MainKind ((term , n0) ∷ [])
  -- 𝓀-send : MainKind ((term , n0) ∷ [])
  -- 𝓀-recv : MainKind ((term , n0) ∷ [])
  -- 𝓀-narrow : MainKind ((term , n0) ∷ [])

  ---------------------------------------------
  -- Mode transformations (transitions)

  -- The type of transition spaces
  𝓀-Tr : MainKind []

  -- Constructing a transition space with a single transition
  𝓀-tr : MainKind ((term , n0) ∷ (modality , n0) ∷ (modality , n0) ∷ [])

  -- identity transition
  𝓀-end : MainKind []

  -- Constructing a space from multiple transitions
  -- 𝓀-transitions : MainKind ((transitions , n0) ∷ [])

  -- Concatenating two spaces
  𝓀-≫ : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  𝓀-∥ : MainKind ((term , n0) ∷ (term , n0) ∷ [])

  ---------------------------------------------
  -- Combining transition spaces with types
  -- 𝓀-[]▹ : MainKind ((term , n0) ∷ (term , n0) ∷ [])
  -- 𝓀-exec : MainKind ((term , n0) ∷ [])
  -- 𝓀-prepare : MainKind ((term , n0) ∷ [])
  𝓀-transform : MainKind ((term , n0) ∷ [])


  ---------------------------------------------
  -- Applying Mode transformations (transitions)

  -- "apply the transformation from ηs to μs to t and put the result
  --  into the context, such that s can use it"



  -- 𝓀-let-in : MainKind ((term , n0) ∷ (term , n1) ∷ [])



-- local leafs get their own kind

data LeafKind : Set where
  Natkind    : LeafKind
  Emptykind  : LeafKind
  Unitkind   : LeafKind

data Kind : (ns : List (Metakind × Nat)) → Set where
  main : ∀{ns} -> MainKind ns -> Kind ns
  leaf : LeafKind -> Kind []
  𝓀-transform : Kind ((transition vis , n0) ∷ (term , n0) ∷ [])

-- Term Ps are indexed by its number of unbound variables and are either:
-- de Bruijn style variables or
-- generic terms, formed by their kind and sub terms



data Term (P : 2Graph 𝑖) (n : Nat) : 𝒰 𝑖

data KindedTerm (P : 2Graph 𝑖) (n : Nat) : (k : Metakind) -> 𝒰 𝑖 where
  term : Term P n -> KindedTerm P n term
  modality : Modality P -> KindedTerm P n modality
  transition : ∀{v} -> Transition P v -> KindedTerm P n (transition v)
  _//_ : Term P n -> Modality P -> KindedTerm P n entry

pattern _/_ A μs = A // _ ↝ _ ∋ μs
infixl 21 _//_ _/_


data Term P n where
  gen : {bs : List (Metakind × Nat)} (k : Kind bs) (c : GenTs (KindedTerm P) n bs) → Term P n
  var : ∀{v} -> (x : Fin n) → Transition P v → Term P n


Entry : (P : 2Graph 𝑖) (n : Nat) -> 𝒰 𝑖
Entry P n = KindedTerm P n entry





private
  variable
    A B C D t u v : Term P n
    -- B        : Term P (1+ n)
    F E G H : Entry P n

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constₜructors.
-- UU      : Term P n                      -- Universe.
pattern UU = gen (main Ukind) []

pattern end        = gen (main 𝓀-end) ([])

-- Π_▹_ : (A : Term P n) (B : Term P (1+ n)) → Term P n  -- Dependent function type (B is a binder).
pattern Π_▹_ A B = gen (main Pikind) (A ∷ term end ∷ term B ∷ [])
pattern Π_▹[_]_ A ξ B = gen (main Pikind) (A ∷ term ξ ∷ term B ∷ [])

-- Σ_▹_ : (A : Term P n) (B : Term P (1+ n)) → Term P n  -- Dependent sum type (B is a binder).
pattern Σ_▹_ A B = gen (main Sigmakind) (A ∷ term B ∷ [])

-- NN      : Term P n                      -- Type of natural numbers.
pattern NN = gen (leaf Natkind) []

-- Vec : (m : Term n) (t : Term n) → Term n -- Vector type.
pattern Vec m t = gen (main Veckind) (term m ∷ term t ∷ [])

-- Empty : Term P n                       -- Empty type
pattern Empty = gen (leaf Emptykind) []

-- Unit  : Term P n                       -- Unit type
pattern Unit = gen (leaf Unitkind) []

-- lam    : (t : Term P (1+ n)) → Term P n  -- Function abstraction (binder).
pattern lam t = gen (main Lamkind) (term t ∷ [])

-- _∘_    : (t u : Term P n) → Term P n     -- Application.
pattern _∘_ t u = gen (main Appkind) (term t ∷ term u ∷ [])


prod : (t u : Term P n) → Term P n       -- Dependent products
prod t u = gen (main Prodkind) (term t ∷ term u ∷ [])
pattern _,ₜ_ t u = gen (main Prodkind) (term t ∷ term u ∷ [])

fstₜ : (t : Term P n) → Term P n          -- First projection
fstₜ t = gen (main Fstkind) (term t ∷ [])

sndₜ : (t : Term P n) → Term P n          -- Second projection
sndₜ t = gen (main Sndkind) (term t ∷ [])

-- Introduction and elimination of natural numbers.
zeroₜ   : Term P n                      -- Natural number zero.
zeroₜ = gen (main Zerokind) []

sucₜ    : (t : Term P n)       → Term P n -- Successor.
sucₜ t = gen (main Suckind) (term t ∷ [])

natrec : (A : Term P (1+ n)) (t u v : Term P n) → Term P n  -- Natural number recursor (A is a binder).
natrec A t u v = gen (main Natreckind) (term A ∷ term t ∷ term u ∷ term v ∷ [])

-- Introduction and elimination of vectors.
nilₜ : Term P n                         -- Empty vector.
nilₜ = gen (main Nilkind) []

consₜ : (v : Term P n) → (vs : Term P n) → Term P n -- Append.
consₜ v vs = gen (main Conskind) (term v ∷ term vs ∷ [])

vecrec : (G : Term P (1+ (1+ n))) (z s l vs : Term P n) → Term P n  -- Vector recursor ( is a binder).
vecrec G z s l vs = gen (main Vecreckind) (term G ∷ term z ∷ term s ∷ term l ∷ term vs ∷ [])


star : Term P n                        -- Unit element
star = gen (main Starkind) []

Emptyrec : (A e : Term P n) → Term P n   -- Empty type recursor
Emptyrec A e = gen (main Emptyreckind) (term A ∷ term e ∷ [])


-- pattern Univ-⇄ R A = gen (main 𝓀-Univ-⇄) ((location R) ∷ term A ∷ [])

-- pattern Com R A      = gen (main 𝓀-Com) ((location R) ∷ term A ∷ [])
-- pattern com T a      = gen (main 𝓀-com) (term T ∷ term a ∷ [])
-- pattern comtype a    = gen (main 𝓀-comtype) (term a ∷ [])
-- pattern comval a     = gen (main 𝓀-comval) (term a ∷ [])

pattern Modal A μ     = gen (main 𝓀-Modal) (term A ∷ (modality μ) ∷ [])
-- pattern _＠_ L U     = gen (main 𝓀-＠) (term L ∷ (location U) ∷ [])
-- pattern loc U t      = gen 𝓀-loc ((location U) ∷ term t ∷ []) -- NOTE, this one is *not* wrapped in `main`
-- pattern unloc t      = gen (main 𝓀-unloc) (term t ∷ [])


-- pattern send t       = gen (main 𝓀-send) (term t ∷ [])
-- pattern recv t       = gen (main 𝓀-recv) (term t ∷ [])
pattern mod t        = gen (main 𝓀-mod) (term t ∷ [])
pattern unmod t      = gen (main 𝓀-unmod) (term t ∷ [])


-- Transformations / Transitions
pattern Tr           = gen (main 𝓀-Tr) ([])
pattern _/_⇒_ A μ η = gen (main 𝓀-tr) (term A ∷ modality μ ∷ modality η ∷ [])
pattern _≫_ m n     = gen (main 𝓀-≫) (term m ∷ term n ∷ [])
pattern _∥_ m n     = gen (main 𝓀-∥) (term m ∷ term n ∷ [])
-- pattern [_]▹_ T A    = gen (main 𝓀-[]▹) (term T ∷ term A ∷ [])
-- infixr 30 [_]▹_

infixl 40 _≫_
infixl 30 _∥_

-- pattern exec t       = gen (main 𝓀-exec) (term t ∷ [])
-- pattern prepare t       = gen (main 𝓀-prepare) (term t ∷ [])
pattern transform t  = gen (main 𝓀-transform) (term t ∷ [])


-- pattern let-tr t s   = gen (main 𝓀-let-tr) (term t ∷ term s ∷ [])
-- pattern let-in t s   = gen (main 𝓀-let-in) (term t ∷ term s ∷ [])

infixl 30 _/_⇒_


-- pattern locskip      = gen (main 𝓀-locskip) []

-- pattern _≫_ x f     = gen (main 𝓀-≫) (term x ∷ term f ∷ [])
-- pattern _>_ x f     = gen (main 𝓀->) (term x ∷ term f ∷ [])

-- pattern Share A U V  = gen (main 𝓀-Share) (term A ∷ (location U) ∷ (location V) ∷ [])
-- pattern share a      = gen (main 𝓀-share) (term a ∷ [])

-- pattern End          = gen (main 𝓀-End) []
-- pattern end a        = gen (main 𝓀-end) (term a ∷ [])




-- infixl 40 _≫_
-- infixl 50 _＠_



-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_▹_ : BindingType → Entry P n → Term P (1+ n) → Term P n
⟦ BΠ ⟧ F ▹ G = Π F ▹ G
⟦ BΣ ⟧ F ▹ G = Σ F ▹ G

-- Injectivity of term constₜructors w.r.t. propositional equality.

-- If  W F G = W H E  then  F = H  and  G = E.

B-PE-injectivity : ∀ W → ⟦ W ⟧ F ▹ A PE.≡ ⟦ W ⟧ E ▹ B → F PE.≡ E × A PE.≡ B
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : sucₜ t PE.≡ sucₜ u → t PE.≡ u
suc-PE-injectivity PE.refl = PE.refl


-- Neutral P terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral (P : 2Graph 𝑖) : KindedTerm P n term → Set where
  -- var       : (x : Fin n) → Neutral P (var x)
  -- ∘ₙ        : Neutral P t   → Neutral P (t ∘ u)
  -- fstₙ      : Neutral P t   → Neutral P (fstₜ t)
  -- sndₙ      : Neutral P t   → Neutral P (sndₜ t)
  -- natrecₙ   : Neutral P v   → Neutral P (natrec G t u v)
  -- vecrecₙ   : Neutral P v   → Neutral P (vecrec G t u v)
  -- Emptyrecₙ : Neutral P t   → Neutral P (Emptyrec A t)

{-

-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {P : 2Graph 𝑖} {n : Nat} : Term P n → Set where

  -- Type constₜructors are whnfs.
  Uₙ     : Whnf UU
  Πₙ     : Whnf (Π A ▹ B)
  Σₙ     : Whnf (Σ A ▹ B)
  ℕₙ     : Whnf NN
  Vecₙ   : Whnf (Vec A F)
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam t)
  zeroₙ : Whnf zeroₜ
  sucₙ  : Whnf (sucₜ t)
  nilₙ  : Whnf nilₜ
  consₙ : Whnf (consₜ t u)
  starₙ : Whnf star
  prodₙ : Whnf (prod t u)

  -- Neutral Ps are whnfs.
  ne    : Neutral P t → Whnf t


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : Neutral P A → UU PE.≢ A
U≢ne () PE.refl

ℕ≢ne : Neutral P A → NN PE.≢ A
ℕ≢ne () PE.refl

Empty≢ne : Neutral P A → Empty PE.≢ A
Empty≢ne () PE.refl

Unit≢ne : Neutral P A → Unit PE.≢ A
Unit≢ne () PE.refl

B≢ne : ∀ W → Neutral P A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

U≢B : ∀ W → UU PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → NN PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral P t → zeroₜ PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral P t → sucₜ u PE.≢ t
suc≢ne () PE.refl

nil≢ne : Neutral P t → nilₜ PE.≢ t
nil≢ne () PE.refl

cons≢ne : Neutral P t → consₜ u v PE.≢ t
cons≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {P : 2Graph 𝑖} {n : Nat} : Term P n → Set where
  zeroₙ :             Natural zeroₜ
  sucₙ  :             Natural (sucₜ t)
  nilₙ  :             Natural nilₜ
  consₙ :             Natural (consₜ u v)
  ne    : Neutral P t → Natural t


-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {P : 2Graph 𝑖} {n : Nat} : Term P n → Set where
  Πₙ     :             Type (Π A ▹ B)
  Σₙ     :             Type (Σ A ▹ B)
  ℕₙ     :             Type NN
  Vecₙ   :             Type (Vec A F)
  Emptyₙ :             Type Empty
  Unitₙ  :             Type Unit
  ne     : Neutral P t → Type t

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {P : 2Graph 𝑖} {n : Nat} : Term P n → Set where
  lamₙ : Function (lam t)
  ne   : Neutral P t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {P : 2Graph 𝑖} {n : Nat} : Term P n → Set where
  prodₙ : Product (prod t u)
  ne    : Neutral P t → Product t

-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

naturalWhnf : Natural t → Whnf t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf consₙ  = consₙ
naturalWhnf nilₙ   = nilₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Πₙ     = Πₙ
typeWhnf Σₙ     = Σₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf Vecₙ   = Vecₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ  = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodₙ  = prodₙ
productWhnf (ne x) = ne x

⟦_⟧ₙ : (W : BindingType) → Whnf (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ BΠ = Πₙ
⟦_⟧ₙ BΣ = Σₙ

-}

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
  wkGen : {m n : Nat} {bs : List (Metakind × Nat)} (ρ : Wk m n) (c : GenTs (KindedTerm P) n bs) → GenTs (KindedTerm P) m bs
  wkGen ρ []                = []
  wkGen ρ (_∷_ {b = b} t c) = (wk-Kinded (liftn ρ b) t) ∷ (wkGen ρ c)

  -- wk-Mod : {m n : Nat} (ρ : Wk m n) (t : Mod P n) → Mod P m
  -- wk-Mod ρ (ML x) = ML x
  -- wk-Mod ρ (⇄ R A) = ⇄ R (wk ρ A)

  wk-Kinded : ∀{k : Metakind} -> {m n : Nat} (ρ : Wk m n) (t : KindedTerm P n k) → KindedTerm P m k
  wk-Kinded ρ (term x) = term (wk ρ x)
  wk-Kinded ρ (transition v) = transition v
  wk-Kinded ρ (modality μ) = modality μ
  wk-Kinded ρ (x / p) = wk ρ x / p

  wk : {m n : Nat} (ρ : Wk m n) (t : Term P n) → Term P m
  wk ρ (var x ξ)   = var (wkVar ρ x) ξ
  wk ρ (gen k c) = gen k (wkGen ρ c)


-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term P n → Term P (1+ n)
wk1 = wk (step id)

-- Weakening of a neutral term.

{-
wkNeutral : ∀ ρ → Neutral P t → Neutral P {n} (wk ρ t)
wkNeutral ρ (var n)       = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)        = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (fstₙ n)      = fstₙ (wkNeutral ρ n)
wkNeutral ρ (sndₙ n)      = sndₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n)   = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (vecrecₙ n)   = vecrecₙ (wkNeutral ρ n)
wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n = n} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ consₙ  = consₙ
wkNatural ρ nilₙ   = nilₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n = n} (wk ρ t)
wkType ρ Πₙ     = Πₙ
wkType ρ Σₙ     = Σₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Vecₙ   = Vecₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n = n} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n = n} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ ρ → Whnf t → Whnf {n = n} (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Σₙ      = Σₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Vecₙ    = Vecₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ nilₙ    = nilₙ
wkWhnf ρ consₙ   = consₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)
-}


-- Non-dependent version of Π.

_▹▹_ : Entry P n → Term P n → Term P n
A ▹▹ B = Π A ▹ wk1 B

_▹▹[_]_ : Entry P n → Term P n -> Term P n → Term P n
A ▹▹[ ξ ] B = Π A ▹[ wk1 ξ ] wk1 B

-- Non-dependent products.

_××_ : Entry P n → Term P n → Term P n
A ×× B = Σ A ▹ wk1 B


------------------------------------------------------------------------
-- Pushing transitions
--


-- Pushes a transition down the term. We push it until the next
-- `transform` term or variable.
push : ∀{v} -> Transition P v -> Term P n -> Term P n
push ξ (gen k c) = {!!}
push ξ (var x ζ) = {!!}


untransform-Term : Term P n -> Term P n
untransform-Term (gen (main x) c) = {!!}
untransform-Term (gen (leaf x) c) = {!!}
untransform-Term (gen 𝓀-transform c) = {!!}
untransform-Term (var x ξ) = {!!}

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : (P : 2Graph 𝑖) -> Nat → Nat → 𝒰 𝑖
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
idSubst x = var x ({!!} ⇒ {!!} ∋ {!!})

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst P m n → Subst P (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst P m n) → Subst P (1+ m) (1+ n)
liftSubst σ x0     = var x0 {!!}
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst P k m → (n : Nat) → Subst P (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst P m n
toSubst pr x = var (wkVar pr x) {!!}

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : {bs : List (Metakind × Nat)} (σ : Subst P m n) (g : GenTs (KindedTerm P) n bs) → GenTs (KindedTerm P) m bs
  substGen σ  []      = []
  substGen σ (_∷_ {b = b} t ts) = subst-Kinded (liftSubstn σ b) t ∷ (substGen σ ts)

  subst-Kinded : ∀{k : Metakind} (σ : Subst P m n) (t : KindedTerm P n k) → KindedTerm P m k
  subst-Kinded σ (term x) = term (subst σ x)
  subst-Kinded σ (transition v) = transition v
  subst-Kinded σ (modality μ) = modality μ
  subst-Kinded σ (x / p) = subst σ x / p

  subst : (σ : Subst P m n) (t : Term P n) → Term P m
  subst σ (var x ξ) = push ξ (substVar σ x) -- if we substitute a variable with an annotation, we have to push this annotation down the term
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




