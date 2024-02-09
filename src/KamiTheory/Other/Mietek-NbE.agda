----------------------------------------------------------------------------------------------------

-- Abel (2013) "Normalization by evaluation: Dependent types and impredicativity"
-- https://www.cse.chalmers.se/~abela/habil.pdf
--
-- Kovacs (2017) "A machine-checked correctness proof of normalization by evaluation for
--   simply typed lambda calculus"
-- https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf
--
-- Coquand (2002) "A formalised proof of the soundness and completeness of a simply typed
--   lambda-calculus with explicit substitutions"
-- https://github.com/dpndnt/library/blob/master/doc/pdf/coquand-2002.pdf


----------------------------------------------------------------------------------------------------

module KamiTheory.Other.Mietek-NbE where

open import Data.Empty public
  using (⊥ ; ⊥-elim)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; _×_ ; _,_)
  renaming (proj₁ to fst ; proj₂ to snd)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (_∘_ ; _$_ ; flip ; id)

open import Level public
  using ()
  renaming (zero to ℓ₀)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; cong ; subst ; sym ; module ≡-Reasoning)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)


----------------------------------------------------------------------------------------------------

coe : ∀ {𝓍} {X Y : Set 𝓍} (eq : X ≡ Y) (x : X) → Y
coe = subst id

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′ : X} (eq : x ≡ x′) →
      f x ≡ f x′
_&_ = cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x y : X} (eq₁ : f ≡ g) (eq₂ : x ≡ y) →
      f x ≡ g y
refl ⊗ refl = refl

recℕ : ∀ {𝓍} {X : Set 𝓍} (z : X) (s : ∀ (n : ℕ) (x : X) → X) (n : ℕ) → X
recℕ z s zero    = z
recℕ z s (suc n) = s n (recℕ z s n)


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  -- intrinsically well-typed de Bruijn indices
  infix 4 _∋_
  data _∋_ : ∀ (Γ : List X) (A : X) → Set 𝓍 where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  -- order-preserving embeddings
  infix 4 _⊆_
  data _⊆_ : ∀ (Γ Γ′ : List X) → Set 𝓍 where
    stop : [] ⊆ []
    drop : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → Γ ⊆ A ∷ Γ′
    keep : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → A ∷ Γ ⊆ A ∷ Γ′

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {[]}    = stop
  refl⊆ {A ∷ Γ} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} (e : Γ ⊆ Γ′) (e′ : Γ′ ⊆ Γ″) → Γ ⊆ Γ″
  trans⊆ e        stop      = e
  trans⊆ e        (drop e′) = drop (trans⊆ e e′)
  trans⊆ (drop e) (keep e′) = drop (trans⊆ e e′)
  trans⊆ (keep e) (keep e′) = keep (trans⊆ e e′)

  wk⊆ : ∀ {Γ A} → Γ ⊆ A ∷ Γ
  wk⊆ = drop refl⊆

  -- renaming of indices
  ren∋ : ∀ {Γ Γ′} {A : X} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → Γ′ ∋ A
  ren∋ stop     i       = i
  ren∋ (drop e) i       = suc (ren∋ e i)
  ren∋ (keep e) zero    = zero
  ren∋ (keep e) (suc i) = suc (ren∋ e i)


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _`⊃_
data Ty : Set where
  _`⊃_ : ∀ (A B : Ty) → Ty
  `ℕ   : Ty

-- contexts
Cx : Set
Cx = List Ty

data Const : ∀ (A : Ty) → Set where
  `zero : Const `ℕ
  `suc  : Const (`ℕ `⊃ `ℕ)
  `rec  : ∀ {A} → Const (A `⊃ (`ℕ `⊃ A `⊃ A) `⊃ `ℕ `⊃ A)

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _`$_
data _⊢_ (Γ : Cx) : ∀ (A : Ty) → Set where
  `v   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  `λ   : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
  _`$_ : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → Γ ⊢ B
  `c   : ∀ {A} (n : Const A) → Γ ⊢ A

-- simultaneous substitutions
infix 3 _⊢*_
data _⊢*_ (Γ : Cx) : ∀ (Δ : Cx) → Set where
  []  : Γ ⊢* []
  _∷_ : ∀ {A Δ} (d : Γ ⊢ A) (ds : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ

-- TODO: later
postulate
  _≡?_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≡ d′)


----------------------------------------------------------------------------------------------------

-- renaming of terms
ren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (d : Γ ⊢ A) → Γ′ ⊢ A
ren e (`v i)     = `v (ren∋ e i)
ren e (`λ d)     = `λ (ren (keep e) d)
ren e (d₁ `$ d₂) = ren e d₁ `$ ren e d₂
ren e (`c n)     = `c n

ren* : ∀ {Γ Γ′ Δ} (e : Γ ⊆ Γ′) (ds : Γ ⊢* Δ) → Γ′ ⊢* Δ
ren* e []       = []
ren* e (d ∷ ds) = ren e d ∷ ren* e ds

weak : ∀ {Γ A B} (d : Γ ⊢ B) → A ∷ Γ ⊢ B
weak d = ren wk⊆ d

weak* : ∀ {Γ Δ A} (ds : Γ ⊢* Δ) → A ∷ Γ ⊢* Δ
weak* ds = ren* wk⊆ ds

lift* : ∀ {Γ Δ A} (ds : Γ ⊢* Δ) → A ∷ Γ ⊢* A ∷ Δ
lift* ds = `v zero ∷ weak* ds

refl* : ∀ {Γ} → Γ ⊢* Γ
refl* {[]}    = []
refl* {A ∷ Γ} = lift* refl*

-- substitution of indices
sub∋ : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (k : Γ ∋ A) → Ξ ⊢ A
sub∋ (s ∷ ss) zero    = s
sub∋ (s ∷ ss) (suc i) = sub∋ ss i

-- substitution
sub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (d : Γ ⊢ A) → Ξ ⊢ A
sub ss (`v i)     = sub∋ ss i
sub ss (`λ d)     = `λ (sub (lift* ss) d)
sub ss (d₁ `$ d₂) = sub ss d₁ `$ sub ss d₂
sub ss (`c n)     = `c n

sub* : ∀ {Γ Ξ Δ} (ss : Ξ ⊢* Γ) (ds : Γ ⊢* Δ) → Ξ ⊢* Δ
sub* ss []       = []
sub* ss (d ∷ ds) = sub ss d ∷ sub* ss ds

cut : ∀ {Γ A B} (s : Γ ⊢ A) (d : A ∷ Γ ⊢ B) → Γ ⊢ B
cut s d = sub (s ∷ refl*) d

get* : ∀ {Γ Δ Δ′} (e : Δ ⊆ Δ′) (ds : Γ ⊢* Δ′) → Γ ⊢* Δ
get* stop     ds       = ds
get* (drop e) (d ∷ ds) = get* e ds
get* (keep e) (d ∷ ds) = d ∷ get* e ds


----------------------------------------------------------------------------------------------------

mutual
  -- d is in β-short η-long normal form
  data NF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `λ    : ∀ {A B} {d : A ∷ Γ ⊢ B} (nf : NF d) → NF (`λ d)
    `zero : NF (`c `zero)
    `suc  : ∀ {d : Γ ⊢ `ℕ} (nf : NF d) → NF (`c `suc `$ d)
    `nnf  : ∀ {d : Γ ⊢ `ℕ} (nnf : NNF d) → NF d

  -- d is in β-short η-long neutral normal form
  data NNF {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
    `v   : ∀ {A} (i : Γ ∋ A) → NNF (`v i)
    _`$_ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (nnf₁ : NNF d₁) (nf₂ : NF d₂) → NNF (d₁ `$ d₂)
    `rec : ∀ {A} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ `ℕ `⊃ A `⊃ A} {d₃ : Γ ⊢ `ℕ} (nf₁ : NF d₁) (nf₂ : NF d₂)
             (nnf₃ : NNF d₃) →
           NNF (`c `rec `$ d₁ `$ d₂ `$ d₃)

mutual
  renNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (nf : NF d) → NF (ren e d)
  renNF e (`λ d)     = `λ (renNF (keep e) d)
  renNF e `zero      = `zero
  renNF e (`suc d)   = `suc (renNF e d)
  renNF e (`nnf nnf) = `nnf (renNNF e nnf)

  renNNF : ∀ {Γ Γ′ A} {d : Γ ⊢ A} (e : Γ ⊆ Γ′) (nnf : NNF d) → NNF (ren e d)
  renNNF e (`v i)              = `v (ren∋ e i)
  renNNF e (nwnf₁ `$ wnf₂)     = renNNF e nwnf₁ `$ renNF e wnf₂
  renNNF e (`rec nf₁ nf₂ nnf₃) = `rec (renNF e nf₁) (renNF e nf₂) (renNNF e nnf₃)

-- NF and NNF are functional
mutual
  funNF : ∀ {Γ A} {d : Γ ⊢ A} (nf nf′ : NF d) → nf ≡ nf′
  funNF (`λ nf)          (`λ nf′)         = `λ & funNF nf nf′
  funNF `zero            `zero            = refl
  funNF (`suc nf)        (`suc nf′)       = `suc & funNF nf nf′
  funNF (`suc _)         (`nnf (() `$ _))
  funNF (`nnf (() `$ _)) (`suc _)
  funNF (`nnf nnf)       (`nnf nnf′)      = `nnf & funNNF nnf nnf′

  funNNF : ∀ {Γ A} {d : Γ ⊢ A} (nnf nnf′ : NNF d) → nnf ≡ nnf′
  funNNF (`v i)               (`v .i)                = refl
  funNNF (nnf₁ `$ nf₂)        (nnf₁′ `$ nf₂′)        = _`$_ & funNNF nnf₁ nnf₁′ ⊗ funNF nf₂ nf₂′
  funNNF (() `$ _ `$ _ `$ _)  (`rec _ _ _)
  funNNF (`rec _ _ _)         (() `$ _ `$ _ `$ _)
  funNNF (`rec nf₁ nf₂ nnf₃)  (`rec nf₁′ nf₂′ nnf₃′) = `rec & funNF nf₁ nf₁′ ⊗ funNF nf₂ nf₂′
                                                                             ⊗ funNNF nnf₃ nnf₃′

-- d is in η-short form at _`⊃_
data ηSF⊃ {Γ} : ∀ {A} (d : Γ ⊢ A) → Set where
  `v   : ∀ {A} (i : Γ ∋ A) → ηSF⊃ (`v i)
  _`$_ : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → ηSF⊃ (d₁ `$ d₂)
  `c   : ∀ {A} (n : Const A) → ηSF⊃ (`c n)

-- -- TODO: are we using this anywhere?
-- ηSF⊃? : ∀ {Γ A} (d : Γ ⊢ A) → Dec (ηSF⊃ d)
-- ηSF⊃? (`v i)     = yes (`v i)
-- ηSF⊃? (`λ d)     = no λ ()
-- ηSF⊃? (d₁ `$ d₂) = yes (d₁ `$ d₂)
-- ηSF⊃? (`c n)     = yes (`c n)

funηSF⊃ : ∀ {Γ A} {d : Γ ⊢ A} (ηsf⊃ ηsf⊃′ : ηSF⊃ d) → ηsf⊃ ≡ ηsf⊃′
funηSF⊃ (`v i)     (`v .i)      = refl
funηSF⊃ (d₁ `$ d₂) (.d₁ `$ .d₂) = refl
funηSF⊃ (`c n)     (`c .n)      = refl


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  refl≝  : ∀ {A} {d : Γ ⊢ A} → d ≝ d
  sym≝   : ∀ {A} {d d′ : Γ ⊢ A} (p : d ≝ d′) → d′ ≝ d
  trans≝ : ∀ {A} {d d′ d″ : Γ ⊢ A} (p : d ≝ d′) (p′ : d′ ≝ d″) → d ≝ d″
  compλ  : ∀ {A B} {d d′ : A ∷ Γ ⊢ B} (p : d ≝ d′) → `λ d ≝ `λ d′
  comp$  : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (p₁ : d₁ ≝ d₁′) (p₂ : d₂ ≝ d₂′) →
           d₁ `$ d₂ ≝ d₁′ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : cut d₂ d₁ ≡ d′) →
           `λ d₁ `$ d₂ ≝ d′
  βredℕ₁ : ∀ {A} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ `ℕ `⊃ A `⊃ A} →
           `c `rec `$ d₁ `$ d₂ `$ `c `zero ≝ d₁
  βredℕ₂ : ∀ {A} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ `ℕ `⊃ A `⊃ A} {d₃ : Γ ⊢ `ℕ} →
           `c `rec `$ d₁ `$ d₂ `$ (`c `suc `$ d₃) ≝ d₂ `$ d₃ `$ (`c `rec `$ d₁ `$ d₂ `$ d₃)
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) →
           d ≝ `λ (d′ `$ `v zero)

≡→≝ : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≡ d′) → d ≝ d′
≡→≝ refl = refl≝

module ≝-Reasoning where
  infix 1 begin_
  begin_ : ∀ {Γ A} {d d′ : Γ ⊢ A} (p : d ≝ d′) → d ≝ d′
  begin_ p = p

  infixr 2 _≝⟨⟩_
  _≝⟨⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′} (p : d ≝ d′) → d ≝ d′
  d ≝⟨⟩ p = p

  infixr 2 _≝⟨_⟩_
  _≝⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (p : d ≝ d′) (p′ : d′ ≝ d″) → d ≝ d″
  d ≝⟨ p ⟩ p′ = trans≝ p p′

  infixr 2 _≝˘⟨_⟩_
  _≝˘⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (p : d′ ≝ d) (p′ : d′ ≝ d″) → d ≝ d″
  d ≝˘⟨ p ⟩ p′ = trans≝ (sym≝ p) p′

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d ≡ d′) (p′ : d′ ≝ d″) → d ≝ d″
  d ≡⟨ eq ⟩ p′ = trans≝ (≡→≝ eq) p′

  infixr 2 _≡˘⟨_⟩_
  _≡˘⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d′ ≡ d) (p′ : d′ ≝ d″) → d ≝ d″
  d ≡˘⟨ eq ⟩ p′ = trans≝ (≡→≝ (sym eq)) p′

  infix 3 _∎
  _∎ : ∀ {Γ A} (d : Γ ⊢ A) → d ≝ d
  d ∎ = refl≝


----------------------------------------------------------------------------------------------------

-- normal order reduction
infix 4 _⟹_
data _⟹_ {Γ} : ∀ {A} (d d′ : Γ ⊢ A) → Set where
  compλ  : ∀ {A B} {d d′ : A ∷ Γ ⊢ B} (r : d ⟹ d′) → `λ d ⟹ `λ d′
  comp$₁ : ∀ {A B} {d₁ d₁′ : Γ ⊢ A `⊃ B} {d₂ : Γ ⊢ A} (ηsf⊃₁ : ηSF⊃ d₁) (r₁ : d₁ ⟹ d₁′) →
           d₁ `$ d₂ ⟹ d₁′ `$ d₂
  comp$₂ : ∀ {A B} {d₁ : Γ ⊢ A `⊃ B} {d₂ d₂′ : Γ ⊢ A} (nnf₁ : NNF d₁) (r₂ : d₂ ⟹ d₂′) →
           d₁ `$ d₂ ⟹ d₁ `$ d₂′
  βred⊃  : ∀ {A B} {d₁ : A ∷ Γ ⊢ B} {d₂ : Γ ⊢ A} {d′ : Γ ⊢ B} (eq : cut d₂ d₁ ≡ d′) →
           `λ d₁ `$ d₂ ⟹ d′
  βredℕ₁ : ∀ {A} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ `ℕ `⊃ A `⊃ A} →
           `c `rec `$ d₁ `$ d₂ `$ `c `zero ⟹ d₁
  βredℕ₂ : ∀ {A} {d₁ : Γ ⊢ A} {d₂ : Γ ⊢ `ℕ `⊃ A `⊃ A} {d₃ : Γ ⊢ `ℕ} →
           `c `rec `$ d₁ `$ d₂ `$ (`c `suc `$ d₃) ⟹ d₂ `$ d₃ `$ (`c `rec `$ d₁ `$ d₂ `$ d₃)
  ηexp⊃  : ∀ {A B} {d : Γ ⊢ A `⊃ B} {d′ : A ∷ Γ ⊢ A `⊃ B} (eq : weak d ≡ d′) (nf : NF d)
             (ηsf⊃ : ηSF⊃ d) →
           d ⟹ `λ (d′ `$ `v zero)

-- d is in reducible form
RF : ∀ {Γ A} (d : Γ ⊢ A) → Set
RF d = Σ _ λ d′ → d ⟹ d′

-- d is in irreducible form
¬R : ∀ {Γ A} (d : Γ ⊢ A) → Set
¬R d = ∀ {d′} → ¬ d ⟹ d′

¬RF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (¬rf : ¬ RF d) → ¬R d
¬RF→¬R ¬rf r = (_ , r) ↯ ¬rf

¬R→¬RF : ∀ {Γ A} {d : Γ ⊢ A} (¬r : ¬R d) → ¬ RF d
¬R→¬RF ¬r (_ , r) = r ↯ ¬r

mutual
  NF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (nf : NF d) → ¬R d
  NF→¬R (`λ nf)    (compλ r)                 = r ↯ NF→¬R nf
  NF→¬R (`λ _)     (ηexp⊃ _ _ ())
  NF→¬R (`suc _)   (comp$₁ _ (ηexp⊃ _ () _))
  NF→¬R (`nnf nnf) r                         = NNF→¬R nnf r

  NNF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (nnf : NNF d) → ¬R d
  NNF→¬R (`v _)               (ηexp⊃ _ () _)
  NNF→¬R (nnf₁ `$ nf₂)        (comp$₁ ηsf⊃₁′ r₁)              = r₁ ↯ NNF→¬R nnf₁
  NNF→¬R (nnf₁ `$ nf₂)        (comp$₂ nnf₁′ r₂)               = r₂ ↯ NF→¬R nf₂
  NNF→¬R (() `$ _ `$ _ `$ _)  βredℕ₁
  NNF→¬R (() `$ _ `$ _ `$ _)  βredℕ₂
  NNF→¬R (_ `$ _)             (ηexp⊃ _ () _)
  NNF→¬R (`rec _ _ _)         (comp$₁ _ (comp$₁ _ (comp$₁ _
                                 (ηexp⊃ _ () _))))
  NNF→¬R (`rec _ _ _)         (comp$₁ _ (comp$₂ (() `$ _) _))
  NNF→¬R (`rec _ _ _)         (comp$₂ (() `$ _ `$ _) _)
  NNF→¬R (`rec _ _ (() `$ _)) βredℕ₂
  NNF→¬R (`rec _ _ _)         (ηexp⊃ _ () _)

-- _⟹_ is deterministic
det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) → d′ ≡ d″
det⟹ (compλ r)                       (compλ r′)                      = `λ & det⟹ r r′
det⟹ (compλ _)                       (ηexp⊃ _ _ ())
det⟹ (comp$₁ ¬λ r₁)                  (comp$₁ ¬λ′ r₁′)                = (_`$ _) & det⟹ r₁ r₁′
det⟹ (comp$₁ ¬λ r₁)                  (comp$₂ nnf₁′ r₂′)              = r₁ ↯ NNF→¬R nnf₁′
det⟹ (comp$₁ () (compλ _))           (βred⊃ refl)
det⟹ (comp$₁ () (ηexp⊃ _ _ _))       (βred⊃ refl)
det⟹ (comp$₁ _ (comp$₁ _
         (comp$₁ _ (ηexp⊃ _ () _))))             βredℕ₁
det⟹ (comp$₁ _ (comp$₂ (() `$ _) _)) βredℕ₁
det⟹ (comp$₁ _ (comp$₁ _
         (comp$₁ _ (ηexp⊃ _ () _))))             βredℕ₂
det⟹ (comp$₁ _ (comp$₂ (() `$ _) _)) βredℕ₂
det⟹ (comp$₂ nnf₁ r₂)                (comp$₁ ¬λ′ r₁′)                = r₁′ ↯ NNF→¬R nnf₁
det⟹ (comp$₂ nnf₁ r₂)                (comp$₂ nnf₁′ r₂′)              = (_ `$_) & det⟹ r₂ r₂′
det⟹ (comp$₂ (() `$ _ `$ _) _)       βredℕ₂
det⟹ (βred⊃ refl)                    (comp$₁ () _)
det⟹ (βred⊃ refl)                    (βred⊃ refl)                    = refl
det⟹ βredℕ₁                          (comp$₁ _ (comp$₁ _
                                         (comp$₁ _ (ηexp⊃ _ () _))))
det⟹ βredℕ₁                          (comp$₁ _ (comp$₂ (() `$ _) _))
det⟹ βredℕ₁                          βredℕ₁                          = refl
det⟹ βredℕ₂                          (comp$₁ _ (comp$₁ _
                                         (comp$₁ _ (ηexp⊃ _ () _))))
det⟹ βredℕ₂                          (comp$₁ _ (comp$₂ (() `$ _) _))
det⟹ βredℕ₂                          (comp$₂ (() `$ _ `$ _) _)
det⟹ βredℕ₂                          βredℕ₂                          = refl
det⟹ (ηexp⊃ _ _ ())                  (compλ _)
det⟹ (ηexp⊃ _ () _)                  βredℕ₁
det⟹ (ηexp⊃ _ () _)                  βredℕ₂
det⟹ (ηexp⊃ refl nf ηsf⊃)            (ηexp⊃ refl nf′ ηsf⊃′)          = refl

-- _⟹_ is functional
fun⟹ : ∀ {Γ A} {d d′ : Γ ⊢ A} (r r′ : d ⟹ d′) → r ≡ r′
fun⟹ (compλ r)            (compλ r′)             = compλ & fun⟹ r r′
fun⟹ (compλ _)            (ηexp⊃ _ _ ())
fun⟹ (comp$₁ ηsf⊃₁ r₁)    (comp$₁ ηsf⊃₁′ r₁′)    = comp$₁ & funηSF⊃ ηsf⊃₁ ηsf⊃₁′ ⊗ fun⟹ r₁ r₁′
fun⟹ (comp$₁ ηsf⊃₁ r₁)    (comp$₂ nnf₁′ r₂′)     = r₁ ↯ NNF→¬R nnf₁′
fun⟹ (comp$₁ () _)        (βred⊃ _)
fun⟹ (comp$₁ _ (comp$₁ _
         (comp$₂ () _)))    βredℕ₁
fun⟹ (comp$₁ _ (comp$₁ _
         (ηexp⊃ _ () _)))   βredℕ₁
fun⟹ (comp$₂ nnf₁ r₂)     (comp$₁ ηsf⊃₁′ r₁′)    = r₁′ ↯ NNF→¬R nnf₁
fun⟹ (comp$₂ nnf₁ r₂)     (comp$₂ nnf₁′ r₂′)     = comp$₂ & funNNF nnf₁ nnf₁′ ⊗ fun⟹ r₂ r₂′
fun⟹ (βred⊃ _)            (comp$₁ () _)
fun⟹ (βred⊃ refl)         (βred⊃ refl)           = refl
fun⟹ βredℕ₁               (comp$₁ _ (comp$₁ _
                              (comp$₂ () _)))
fun⟹ βredℕ₁               (comp$₁ _ (comp$₁ _
                              (ηexp⊃ _ () _)))
fun⟹ βredℕ₁               βredℕ₁                 = refl
fun⟹ βredℕ₂               βredℕ₂                 = refl
fun⟹ (ηexp⊃ _ _ ())       (compλ _)
fun⟹ (ηexp⊃ refl nf ηsf⊃) (ηexp⊃ refl nf′ ηsf⊃′) = ηexp⊃ refl & funNF nf nf′ ⊗ funηSF⊃ ηsf⊃ ηsf⊃′

pattern injRF x = inj₁ x
pattern injNF x = inj₂ x

-- TODO: later
RF⊎NF : ∀ {Γ A} (d : Γ ⊢ A) → RF d ⊎ NF d
-- RF⊎NF (`v i)        = {!!} -- injNF (`nnf (`v i))
-- RF⊎NF (`λ d)        with RF⊎NF d
-- ... | injRF (_ , r) = injRF (_ , compλ r)
-- ... | injNF nf      = injNF (`λ nf)
-- RF⊎NF (d₁ `$ d₂)    with RF⊎NF d₁ | RF⊎NF d₂
-- RF⊎NF (d₁ `$ d₂) | injRF (_ , r₁) | _ = injRF (_ , comp$₁ {!!} r₁)
-- RF⊎NF (d₁ `$ d₂) | injNF y | injRF (_ , r₂) = {!y!} -- injRF (_ , comp$₂ {!!} r₂)
-- RF⊎NF (d₁ `$ d₂) | injNF y | injNF y₁ = {!!}
-- RF⊎NF (`c n)     = {!!}

¬R→NF : ∀ {Γ A} {d : Γ ⊢ A} (¬r : ¬R d) → NF d
¬R→NF {d = d} ¬r with RF⊎NF d
... | injRF rf = rf ↯ ¬R→¬RF ¬r
... | injNF nf = nf

¬NF→RF : ∀ {Γ A} {d : Γ ⊢ A} (¬nf : ¬ NF d) → RF d
¬NF→RF {d = d} ¬nf with RF⊎NF d
... | injNF nf = nf ↯ ¬nf
... | injRF rf = rf

RF→¬NF : ∀ {Γ A} {d : Γ ⊢ A} (rf : RF d) → ¬ NF d
RF→¬NF (d′ , r) nf = r ↯ NF→¬R nf

¬RF→NF : ∀ {Γ A} {d : Γ ⊢ A} (¬rf : ¬ RF d) → NF d
¬RF→NF = ¬R→NF ∘ ¬RF→¬R

NF→¬RF : ∀ {Γ A} {d : Γ ⊢ A} (nf : NF d) → ¬ RF d
NF→¬RF = ¬R→¬RF ∘ NF→¬R


----------------------------------------------------------------------------------------------------

-- iterated reduction
infix 4 _⟹*_
data _⟹*_ {Γ} : ∀ {A} (d : Γ ⊢ A) (d′ : Γ ⊢ A) → Set where
  done : ∀ {A} {d : Γ ⊢ A} → d ⟹* d
  step : ∀ {A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (rs : d′ ⟹* d″) → d ⟹* d″

trans⟹* : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (rs : d ⟹* d′) (rs′ : d′ ⟹* d″) → d ⟹* d″
trans⟹* done        rs′ = rs′
trans⟹* (step r rs) rs′ = step r (trans⟹* rs rs′)

-- _⟹_ has the diamond property
dia⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) →
         Σ (Γ ⊢ A) λ d‴ → d′ ⟹* d‴ × d″ ⟹* d‴
dia⟹ r r′ with det⟹ r r′
... | refl  = _ , done , done

-- _⟹_ is confluent
conf⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (rs : d ⟹* d′) (rs′ : d ⟹* d″) →
          Σ (Γ ⊢ A) λ d‴ → d′ ⟹* d‴ × d″ ⟹* d‴
conf⟹ done        rs′           = _ , rs′ , done
conf⟹ (step r rs) done          = _ , done , step r rs
conf⟹ (step r rs) (step r′ rs′) with det⟹ r r′
... | refl                        = conf⟹ rs rs′

skip⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (nf″ : NF d″) (r : d ⟹ d′) (rs′ : d ⟹* d″) →
          d′ ⟹* d″
skip⟹ nf″ r done          = r ↯ NF→¬R nf″
skip⟹ nf″ r (step r′ rs′) with det⟹ r r′
... | refl                  = rs′

-- _⟹*_ is deterministic
det⟹* : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (nf′ : NF d′) (nf″ : NF d″) (rs : d ⟹* d′)
            (rs′ : d ⟹* d″) →
          d′ ≡ d″
det⟹* nf′ nf″ done        done          = refl
det⟹* nf′ nf″ done        (step r′ rs′) = r′ ↯ NF→¬R nf′
det⟹* nf′ nf″ (step r rs) rs′           = det⟹* nf′ nf″ rs (skip⟹ nf″ r rs′)

≡→⟹* : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≡ d′) → d ⟹* d′
≡→⟹* refl = done

module ⟹-Reasoning where
  infix 1 begin_
  begin_ : ∀ {Γ A} {d d′ : Γ ⊢ A} (rs : d ⟹* d′) → d ⟹* d′
  begin_ rs = rs

  infixr 2 _⟹⟨_⟩_
  _⟹⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (r : d ⟹ d′) (rs : d′ ⟹* d″) → d ⟹* d″
  d ⟹⟨ r ⟩ rs = step r rs

  infixr 2 _⟹*⟨⟩_
  _⟹*⟨⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′} (rs : d ⟹* d′) → d ⟹* d′
  d ⟹*⟨⟩ rs = rs

  infixr 2 _⟹*⟨_⟩_
  _⟹*⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (rs : d ⟹* d′) (rs′ : d′ ⟹* d″) → d ⟹* d″
  d ⟹*⟨ rs ⟩ rs′ = trans⟹* rs rs′

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d ≡ d′) (rs′ : d′ ⟹* d″) → d ⟹* d″
  d ≡⟨ eq ⟩ rs′ = trans⟹* (≡→⟹* eq) rs′

  infix 3 _∎
  _∎ : ∀ {Γ A} (d : Γ ⊢ A) → d ⟹* d
  d ∎ = done


----------------------------------------------------------------------------------------------------

-- iterated reduction to NF
infix 4 _⇓_
_⇓_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Set
d ⇓ d′ = NF d′ × d ⟹* d′

step⇓ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (es′ : d′ ⇓ d″) → d ⇓ d″
step⇓ r (nf″ , rs′) = nf″ , step r rs′

skip⇓ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (es′ : d ⇓ d″) → d′ ⇓ d″
skip⇓ r (nf″ , rs′) = nf″ , skip⟹ nf″ r rs′

-- _⇓_ is deterministic
det⇓ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (es : d ⇓ d′) (es′ : d ⇓ d″) → d′ ≡ d″
det⇓ (nf′ , rs) (nf″ , rs′) = det⟹* nf′ nf″ rs rs′


----------------------------------------------------------------------------------------------------

-- d is weakly normalizing
WN : ∀ {Γ A} (d : Γ ⊢ A) → Set
WN d = Σ _ λ d′ → d ⇓ d′

-- d is strongly normalizing
data SN {Γ A} (d : Γ ⊢ A) : Set where
  mkSN : ∀ (h : ∀ {d′} (r : d ⟹ d′) → SN d′) → SN d

recSN : ∀ {Γ A 𝓅} (P : ∀ (d : Γ ⊢ A) → Set 𝓅)
          (H : ∀ {d} (h : ∀ {d′} (r : d ⟹ d′) → P d′) → P d) {d} (sn : SN d) →
        P d
recSN P H (mkSN h) = H λ r → recSN P H (h r)

SN→WN : ∀ {Γ A} {d : Γ ⊢ A} (sn : SN d) → WN d
SN→WN {d = d} sn = recSN WN aux sn
  where
    aux : ∀ {d′} (h : ∀ {d″} (r : d′ ⟹ d″) → WN d″) → WN d′
    aux {d′} h with RF⊎NF d′
    ... | injNF nf′      = d′ , nf′ , done
    ... | injRF (d″ , r) with h r
    ... | d‴ , nf″ , rs  = d‴ , nf″ , step r rs

WN→SN : ∀ {Γ A} {d : Γ ⊢ A} (wn : WN d) → SN d
WN→SN (_ , wnf′ , rs) = WN→SN′ wnf′ rs
  where
    WN→SN′ : ∀ {Γ A} {d d′ : Γ ⊢ A} (nf′ : NF d′) (rs : d ⟹* d′) → SN d
    WN→SN′ {d = d} nf′ done        = mkSN λ r′ → r′ ↯ NF→¬R nf′
    WN→SN′ {d = d} nf′ (step r rs) = mkSN λ r′ → aux r′
      where
        aux : ∀ {d″} (r′ : d ⟹ d″) → SN d″
        aux r′ with det⟹ r r′
        ... | refl = WN→SN′ nf′ rs


----------------------------------------------------------------------------------------------------

-- d is hereditarily weakly normalizing
HWN : ∀ {Γ A} (d : Γ ⊢ A) → Set
HWN′ : ∀ {Γ A} (d : Γ ⊢ A) → Set

HWN d = WN d × HWN′ d

HWN′ {A = A `⊃ B} d = ∀ {d′} → HWN d′ → HWN (d `$ d′)
HWN′ {A = `ℕ}     d = ℕ

data HWN* {Γ} : ∀ {Δ} (ds : Γ ⊢* Δ) → Set where
  []  : HWN* []
  _∷_ : ∀ {A Δ} (d : Γ ⊢ A) (ds : Γ ⊢* Δ) → HWN* (d ∷ ds)

reflHWN* : ∀ {Γ} → HWN* {Γ} refl*
reflHWN* {[]}    = []
reflHWN* {A ∷ Γ} = `v zero ∷ weak* refl*

postulate
  genhwn : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (hs : HWN* ss) (d : Γ ⊢ A) → HWN (sub ss d)
  idsub : ∀ {Γ A} (d : Γ ⊢ A) → sub refl* d ≡ d

hwn : ∀ {Γ A} (d : Γ ⊢ A) → HWN d
hwn d = coe (HWN & idsub d) (genhwn refl* reflHWN* d)

wn : ∀ {Γ A} (d : Γ ⊢ A) → WN d
wn d = fst (hwn d)

sn : ∀ {Γ A} (d : Γ ⊢ A) → SN d
sn = WN→SN ∘ wn


----------------------------------------------------------------------------------------------------

-- TODO: is there a neater proof that _⟹_ is irreflexive?
irrefl⟹ : ∀ {Γ A} (d : Γ ⊢ A) → ¬ d ⟹ d
irrefl⟹ d r       with wn d
... | d′ , nf′ , rs with aux rs
  where
    aux : ∀ {d′} (rs′ : d ⟹* d′) → d ≡ d′
    aux done          = refl
    aux (step r′ rs′) with det⟹ r r′
    ... | refl        = aux rs′
... | refl          = r ↯ NF→¬R nf′

-- TODO: can we prove that _⟹*_ is functional?
-- fun⟹* : ∀ {Γ A} {d d′ : Γ ⊢ A} (rs rs′ : d ⟹* d′) → rs ≡ rs′


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World  : Set
    _≤_    : ∀ (W W′ : World) → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} (e : W ≤ W′) (e′ : W′ ≤ W″) → W ≤ W″

module _ {ℳ : Model} where
  private module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ∀ (W : ℳ.World) (A : Ty) → Set
  W ⊩ A `⊃ B = ∀ {W′} (e : W ℳ.≤ W′) (v : W′ ⊩ A) → W′ ⊩ B
  -- W ⊩ `ℕ  = ℕ
  W ⊩ `ℕ     = Σ ([] ⊢ `ℕ) λ d → NF d

  mov : ∀ {W W′ A} (e : W ℳ.≤ W′) (v : W ⊩ A) → W′ ⊩ A
  mov {A = A `⊃ B} e v = λ e′ → v (ℳ.trans≤ e e′)
  mov {A = `ℕ}     e v = v

  infix 3 _⊩*_
  data _⊩*_ (W : ℳ.World) : ∀ (Γ : Cx) → Set where
    []  : W ⊩* []
    _∷_ : ∀ {Γ A} (v : W ⊩ A) (vs : W ⊩* Γ) → W ⊩* A ∷ Γ

  mov* : ∀ {W W′ Γ} (e : W ℳ.≤ W′) (vs : W ⊩* Γ) → W′ ⊩* Γ
  mov* e []       = []
  mov* e (v ∷ vs) = mov e v ∷ mov* e vs

infix 3 _∣_⊩_
_∣_⊩_ : ∀ (ℳ : Model) (W : Model.World ℳ) (A : Ty) → Set
ℳ ∣ W ⊩ A = _⊩_ {ℳ} W A

infix 3 _∣_⊩*_
_∣_⊩*_ : ∀ (ℳ : Model) (W : Model.World ℳ) (Δ : Cx) → Set
ℳ ∣ W ⊩* Δ = _⊩*_ {ℳ} W Δ

infix 3 _⊨_
_⊨_ : ∀ (Γ : Cx) (A : Ty) → Set₁
Γ ⊨ A = ∀ {ℳ : Model} {W : Model.World ℳ} (vs : ℳ ∣ W ⊩* Γ) → ℳ ∣ W ⊩ A

reflect∋ : ∀ {Γ A} (i : Γ ∋ A) → Γ ⊨ A
reflect∋ zero    (v ∷ vs) = v
reflect∋ (suc i) (v ∷ vs) = reflect∋ i vs

-- reflectConst : ∀ {Γ A} (n : Const A) → Γ ⊨ A
-- reflectConst `zero     vs = zero
-- reflectConst `suc      vs = λ e → suc
-- reflectConst `rec  {ℳ} vs = λ e z e′ s e″ →
--                               recℕ (mov (ℳ.trans≤ e′ e″) z) λ n′ v →
--                                 s e″ n′ ℳ.refl≤ v
--   where module ℳ = Model ℳ

-- TODO: somehow we already need ↑ to finish defining this?!
reflectConst : ∀ {Γ A} (n : Const A) → Γ ⊨ A
reflectConst `zero vs = `c `zero , `zero
reflectConst `suc  vs = λ { e (d , nf) → `c `suc `$ d , `suc nf }
reflectConst `rec  vs = λ { e z e′ s e″ (d , nf) → {!!} }

reflect : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊨ A
reflect (`v i)         vs = reflect∋ i vs
reflect (`λ d)         vs = λ e v → reflect d (v ∷ mov* e vs)
reflect (d₁ `$ d₂) {ℳ} vs = reflect d₁ vs ℳ.refl≤ $ reflect d₂ vs
  where module ℳ = Model ℳ
-- reflect d vs = {!d!}
-- TODO: when case splitting on d in the above line, with the below line commented out
-- "An internal error has occurred. Please report this as a bug.
--  Location of the error: src/full/Agda/TypeChecking/Coverage.hs:469"
reflect (`c n)         vs = reflectConst n vs

-- canonical model
𝒞 : Model
𝒞 = record
      { World  = Cx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      }

↓ : ∀ {Γ A} {d : Γ ⊢ A} (nnf : NNF d) → 𝒞 ∣ Γ ⊩ A
↑ : ∀ {Γ A} (v : 𝒞 ∣ Γ ⊩ A) → Σ (Γ ⊢ A) λ d → NF d

↓ {A = A `⊃ B} nwnf = λ e v → ↓ (renNNF e nwnf `$ snd (↑ v))
↓ {A = `ℕ}     nwnf = {!!}

↑ {A = A `⊃ B} v with ↑ (v wk⊆ (↓ (`v zero)))
... | d , nf     = `λ d , `λ nf
↑ {A = `ℕ}     v = {!!}

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↓ (`v zero) ∷ mov* wk⊆ refl⊩*

reify : ∀ {Γ A} (o : Γ ⊨ A) → Σ _ λ d′ → NF d′
reify o = ↑ (o refl⊩*)

-- NOTE: we don't know whether d reduces to d′
nbe : ∀ {Γ A} (d : Γ ⊢ A) → Σ _ λ d′ → NF d′
nbe = reify ∘ reflect


----------------------------------------------------------------------------------------------------

-- TODO: wtf is up with these inference failures?
postulate
  -- Abel p.8: "preservation of meaning"
  lem₁ : ∀ {ℳ : Model} {W : Model.World ℳ}
           {Γ A} (d : Γ ⊢ A) →
         reflect d ≡ reflect (fst (nbe d)) {ℳ} {W}

  -- Abel p.8: "idempotency"
  -- Kovacs p.59: "stability"
  lem₂ : ∀ {Γ A} (d : Γ ⊢ A) (nf : NF d) →
         d ≡ fst (nbe d)

  -- Abel p.8: "semantic equality"
  lem₃ : ∀ {ℳ : Model} {W : Model.World ℳ}
           {Γ A} (d d′ : Γ ⊢ A) (eq : reflect d {ℳ} {W} ≡ reflect d′) →
         nbe d ≡ nbe d′

  -- Coquand p.68: "extensional equality on semantic objects"
  Eq : ∀ {ℳ : Model} {W : Model.World ℳ} {A} (v v′ : ℳ ∣ W ⊩ A) → Set

  -- Coquand p.73
  thm₁ : ∀ {Γ A} {v v′ : Γ ⊩ A} (eq : Eq v v′) →
         ↑ v ≡ ↑ v′

  -- Coquand p.73
  cor₁ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : Eq (reflect d refl⊩*) (reflect d′ refl⊩*)) →
         nbe d ≡ nbe d′

  -- Abel p.10: "soundness of definitional equality"
  -- Coquand p.74: "completeness of conversion rules"
  -- Kovacs p.45: "completeness"
  thm₂ : ∀ {Γ A} (d : Γ ⊢ A) →
         d ≝ fst (nbe d)

  -- Coquand p.75: "completeness of conversion rules"
  thm₃ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : Eq (reflect d refl⊩*) (reflect d′ refl⊩*)) →
         d ≝ d′

  -- Coquand p.76: "soundness of conversion rules"
  thm₄ : ∀ {ℳ : Model} {W : Model.World ℳ}
           {Γ A} (d d′ : Γ ⊢ A) (p : d ≝ d′) (vs : ℳ ∣ W ⊩* Γ) →
         Eq (reflect d {ℳ} {W} vs) (reflect d′ vs)

  -- Coquand p.76: "correctness of decision algorithm for conversion"
  thm₅ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : nbe d ≡ nbe d′) →
         d ≝ d′

  -- Abel p.10: "completeness of definitional equality"
  -- Coquand p.76: "completeness of decision algorithm for conversion"
  -- Kovacs p.52: "soundness"
  thm₆ : ∀ {Γ A} {d d′ : Γ ⊢ A} (p : d ≝ d′) →
         nbe d ≡ nbe d′

-- Kovacs p.59: "decision procedure for conversion"
_≝?_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≝ d′)
d ≝? d′ with fst (nbe d) ≡? fst (nbe d′)
... | yes eq = yes (begin
    d            ≝⟨ thm₂ d ⟩
    fst (nbe d)  ≡⟨ eq ⟩
    fst (nbe d′) ≝˘⟨ thm₂ d′ ⟩
    d′           ∎)
  where open ≝-Reasoning
... | no ¬eq = no λ p → (fst & thm₆ p) ↯ ¬eq
