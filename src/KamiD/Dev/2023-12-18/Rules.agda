{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2023-12-18.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

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




-- spaces
-- data Space : 𝒰₀
-- data _⊢Subspace : Space -> 𝒰₀
-- data _⊢Pt : Space -> 𝒰₀
-- data _⊢Ln_⇾_ : (Σ : Space) -> (a b : Σ ⊢Pt) -> 𝒰₀

-- private variable
--   Σ : Space

-- times
-- data Time : 𝒰₀
-- data _⊢T : Time -> 𝒰₀
-- data _⊢TExt : Time -> 𝒰₀
-- data _⊢T_ : (Τ : Time) -> Τ ⊢TExt -> 𝒰₀
-- data _⊢_<T_ : (Τ : Time) -> ∀{X} -> (s t : Τ ⊢T X) -> 𝒰₀

-- private variable
--   Τ : Time

-------------------
-- we have a layer system for the context argument

Layer : 𝒰₀

private variable
  K L : Layer


-- types
data Ctx : Layer -> 𝒰₀

private variable
  Γ Δ : Ctx L

data _⇛_ : Ctx L -> Ctx L -> 𝒰₀
data _⇛♮_ : Ctx L -> Ctx L -> 𝒰₀

data _⊢Type : ∀ (Γ : Ctx L) -> 𝒰₀

private variable
  A : Γ ⊢Type
  B : Γ ⊢Type
-- -- data _⊢VType_,_ : ∀ Σ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> ℕ -> 𝒰₀
-- data _⊢PtType_ : ∀ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> 𝒰₀
-- data _⊢PtBase_ : ∀ (Γ : Ctx Σ Τ) -> Σ ⊢Pt -> 𝒰₀
-- data _⊢LnType_ : ∀ (Γ : Ctx Σ Τ) -> ∀{a b} -> Σ ⊢Ln a ⇾ b -> 𝒰₀

-- data _⊢TypeOp : (Γ : Ctx L) -> 𝒰₀

-- terms
data _⊢Var_ : ∀ (Γ : Ctx L) -> (A : Γ ⊢Type) -> 𝒰₀
data _⊢_ : ∀ (Γ : Ctx L) -> (A : Γ ⊢Type) -> 𝒰₀

-- private variable
--   U V : Σ ⊢Subspace
--   x y : Σ ⊢Pt

-- _↷_ : Γ ⊢TypeOp -> Γ ⊢Type -> Γ ⊢Type



---------------------------------------------
-- parameters for basic types
-- data Charge : 𝒰₀ where
--   ⁺ ⁻ : Charge

data Chargelike : 𝒰₀ where
  ◌ +- : Chargelike

data Timelike : 𝒰₀ where
  𝟙 : Timelike

private variable
  τ : Timelike

data Charge : 𝒰₀ where
  + - : Charge

-- data _⇌_ : Layer -> Layer -> 𝒰₀ where
--   ⁺ ⁻ : 𝟙 ⇌ ℂ

Layer = Chargelike ×-𝒰 Timelike

---------------------------------------------
-- types


data Ctx where
  [] : Ctx L

  -- this should actually also contain the fragmentation
  -- assignment
  _,[_] : ∀ (Γ : Ctx L) -> Γ ⊢Type -> Ctx L



data _⊢Ctx : Ctx L -> 𝒰₀ where
  [] : Γ ⊢Ctx
  [_]∷_ :  (A : Γ ⊢Type) -> Γ ,[ A ] ⊢Ctx -> Γ ⊢Ctx

infixl 50 [_]∷_



_⋆-Ctx_ : (Γ : Ctx L) -> Γ ⊢Ctx -> Ctx L
Γ ⋆-Ctx [] = Γ
Γ ⋆-Ctx ([ A ]∷ Δ) = Γ ,[ A ] ⋆-Ctx Δ

_,[_]-⊢Ctx : (E : Γ ⊢Ctx) -> (Γ ⋆-Ctx E) ⊢Type -> Γ ⊢Ctx
[] ,[ x ]-⊢Ctx = [ x ]∷ []
([ A ]∷ E) ,[ x ]-⊢Ctx = [ A ]∷ (E ,[ x ]-⊢Ctx)


data _⊢Ctx₊ : Ctx L -> 𝒰₀

_⋆-Ctx₊_ : ∀ (Γ : Ctx L) -> Γ ⊢Ctx₊ -> Ctx L

data _⊢Ctx₊ where
  [] : Γ ⊢Ctx₊
  _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Type -> Γ ⊢Ctx₊

_⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≣ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

-- [] ⋆-Ctx₊₂ E = {!!}
-- (Δ ,[ x ]) ⋆-Ctx₊₂ E = {!!}
Δ ⋆-Ctx₊₂ [] = Δ
Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≣ (cong-≣ _⊢Type (sym-≣ assoc-⋆-Ctx₊)) x ]

Γ ⋆-Ctx₊ [] = Γ
Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

-- J1 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑘} -> ∀{a b : A} -> (p : a ≣ b) -> (F : A -> 𝒰 𝑗) -> (f : ∀ a -> F a -> B) -> (x : F a) -> f b (transp-≣ (cong-≣ F p) x) ≣ f a x

assoc-⋆-Ctx₊ {E = []} = refl-≣
assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
  let p = sym-≣ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
  in J1 p _⊢Type _,[_] x

{-# REWRITE assoc-⋆-Ctx₊ #-}




infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_

[_]Ctx₊∷_ : ∀ A -> Δ ,[ A ] ⊢Ctx₊ -> Δ ⊢Ctx₊
[_]Ctx₊∷_ {Δ = Δ} A E =
  let X : Δ ⊢Ctx₊
      X = [] ,[ A ]
  in X ⋆-Ctx₊₂ E


-- ev-Ctx₊ : Γ ⊢Ctx₊ -> Γ ⊢Ctx
-- ev-Ctx₊ [] = []
-- ev-Ctx₊ (E ,[ x ]) = {!!} -- ev-Ctx₊ E ,[ x ]-⊢Ctx

_⋆⁻¹-Ctx_ : (Γ : Ctx L) -> Γ ⊢Ctx -> Ctx L
[] ⋆⁻¹-Ctx Δ = [] ⋆-Ctx Δ
(Γ ,[ x ]) ⋆⁻¹-Ctx Δ = Γ ⋆⁻¹-Ctx [ x ]∷ Δ

-- βₗ-⋆-Ctx : ∀{Δ} -> Γ ,[ A ] ⋆-Ctx Δ ≣ Γ ⋆-Ctx [ A ]∷ Δ
-- βₗ-⋆-Ctx {Δ = []} = refl-≣
-- βₗ-⋆-Ctx {Δ = [ A ]∷ Δ} = refl-≣

-- {-# REWRITE βₗ-⋆-Ctx #-}

-- Γ ⋆-Ctx Δ = Γ

  --------------
  -- Normalizable
  -- wkT : ∀ T -> Ctx Σ Τ -> Ctx Σ (Τ , T)
  -- _⟨_⟩ : Ctx Σ Τ -> Τ ⊢T -> Ctx Σ Τ

-- {-# REWRITE testeq #-}

Dull-Ctx : Ctx (+- , τ) -> Ctx (◌ , τ)
Dull-Type : ∀{Γ : Ctx (+- , τ)} -> Γ ⊢Type -> Dull-Ctx Γ ⊢Type

record hasNotation-Dull (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field Dull : (a : A) -> B a

open hasNotation-Dull {{...}} public

instance
  hasNotation-Dull:Ctx : hasNotation-Dull (Ctx (+- , τ)) (const (Ctx (◌ , τ)))
  hasNotation-Dull:Ctx = record { Dull = Dull-Ctx }

instance
  hasNotation-Dull:Type : ∀{Γ : Ctx (+- , τ)} -> hasNotation-Dull (Γ ⊢Type) (const (Dull Γ ⊢Type))
  hasNotation-Dull:Type = record { Dull = Dull-Type }

Dull-Ctx [] = []
Dull-Ctx (Γ ,[ A ]) = Dull-Ctx Γ ,[ Dull-Type A ]


Restr-Ctx : (Γ : Ctx L) -> ∀{X} -> Γ ⊢Var X -> Ctx L
Restr-Type : {Γ : Ctx L} -> ∀(X : Γ ⊢Type) -> (v : Γ ⊢Var X) -> Restr-Ctx Γ v ⊢Type



_[_≔_] : ∀(Γ : Ctx (+- , τ)) {X} -> (v : Γ ⊢Var X) -> Restr-Ctx Γ v ⊢ Restr-Type X v -> Ctx (+- , τ)

-- _[_≔_] : ∀(Γ : Ctx L) {X} -> Γ ⊢Var X -> Γ ⊢ X -> Ctx (L)

-- Dull : Ctx (+- , τ) -> Ctx (◌ , τ)
-- Dull G = {!!}





-- postulate
--   β-Dull : ∀{Γ : Ctx (+- , τ)} {A}
--          -> Dull (Γ ,[ A ]) ≣ Dull-Ctx Γ ,[ Dull-Type A ]

-- {-# REWRITE β-Dull #-}



infixl 40 _,[_]
-- infixl 60 ⟨_⦙_


_[_]-Type : Δ ⊢Type -> Γ ⇛♮ Δ -> Γ ⊢Type

♮-⇛ : Γ ⇛ Δ -> Γ ⇛♮ Δ
♮-⇛ = {!!}

data _⇛_ where
  id : ∀{Γ : Ctx L} -> Γ ⇛ Γ
  π₁ : ∀{Γ Δ : Ctx L} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ
  _,_ : ∀{Γ Δ : Ctx L} -> (δ : Γ ⇛ Δ) -> ∀{A} -> Γ ⊢ (A [ ♮-⇛ δ ]-Type) -> Γ ⇛ Δ ,[ A ]
  _◆-⇛_ : ∀{Γ Δ Ε : Ctx L} -> Γ ⇛ Δ -> Δ ⇛ Ε -> Γ ⇛ Ε
  ε : Γ ⇛ []

data _⇛♮_ where
  ε : Γ ⇛♮ []
  _,_ : ∀{A} -> (σ : Γ ⇛♮ Δ) -> Γ ⊢ (A [ σ ]-Type) -> Γ ⇛♮ Δ ,[ A ]
  -- _×-⇛♮_ : (σ : Γ ⇛♮ Δ) -> (A : Δ ⊢Type) -> Γ ,[ A [ σ ]-Type ] ⇛♮ Δ ,[ A ]


Dull-⇛ : (Γ ⇛ Δ) -> Dull-Ctx Γ ⇛ Dull-Ctx Δ
Dull-⇛ = {!!}


-- ι-subst-Ctx : ∀{A : Γ ⊢Type} {v} {x : Restr Γ v ⊢ Restr-Type A v} -> Γ ⇛ (Γ [ v ≔ x ])
-- ι-subst-Ctx = {!!}

σ-subst-Ctx : ∀{A : Γ ⊢Type} {v : Γ ⊢Var A} {x} -> (Γ [ v ≔ x ]) ⇛ Γ


wk : ∀{Γ : Ctx L} {A : Γ ⊢Type} -> (Γ ,[ A ] ⇛ Γ)
wk = π₁ id

data BaseType : 𝒰₀ where
  NN End : BaseType

data _⊢Type where
  -- gen : (ϕ : K ⇌ L) -> ⟨ ϕ ⦙ Γ ⊢Type -> Γ ⊢Type
  -- D⁻ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Type
  -- D⁺ : ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Type
  -- ⨇ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  -- ⨈ : (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  Base : ∀{Γ : Ctx (◌ , τ)} -> BaseType -> Γ ⊢Type
  ⨉ : Charge -> (X : Γ ⊢Type) -> (Γ ,[ X ] ⊢Type) -> Γ ⊢Type
  D : Charge -> ∀{Γ : Ctx (+- , τ)} -> Dull Γ ⊢Type -> Γ ⊢Type
  Fam : Γ ⊢ Base NN -> Γ ⊢Type

pattern ⨇ X Y = ⨉ + X Y
pattern ⨈ X Y = ⨉ - X Y
pattern D⁺ A = D + A
pattern D⁻ A = D - A

Dull-Type {Γ = Γ} (D c X) = X
Dull-Type {Γ = Γ} (⨉ c X Y) = ⨉ c (Dull-Type X) (Dull-Type Y)


wk-Type : ∀{A} -> Γ ⊢Type -> Γ ,[ A ] ⊢Type
wk-Type (D c X) = {!!}
wk-Type (⨉ c X X₁) = {!!}
wk-Type (Base x) = {!!}
wk-Type (Fam x) = {!!}

-- su-Type : ∀{A} -> {X : Δ ,[ A ] ⊢Type} -> (Δ ⊢ A) -> Δ ,[ A ] ⊢ X -> Δ ⊢Type
-- su-Type = {!!}

-- split-sub : ∀{A} -> (σ : Γ ⇛♮ Δ ,[ A ]) -> Γ ⇛♮ Δ
-- split-sub id = {!!}
-- split-sub (π₁ σ) = split-sub (split-sub σ)
-- split-sub (σ , x) = {!!}
-- split-sub (σ ◆-⇛ σ₁) = {!!}




-- Restr-Type : {Γ : Ctx L} -> ∀(X : Γ ⊢Type) -> (v : Γ ⊢Var X) -> Restr Γ v ⊢Type


Dull-Var : {Γ : Ctx (+- , τ)} -> {A : Dull Γ ⊢Type} -> Γ ⊢Var (D⁻ A) -> Dull Γ ⊢Var A
Dull-Var = {!!}

-- postulate
--   σ-Dull-Restr : {Γ : Ctx (+- , τ)} -> {A : Dull Γ ⊢Type} -> {v : Γ ⊢Var (D⁻ A)} -> Dull (Restr Γ v) ≣ Restr-Ctx (Dull Γ) (Dull-Var v)

-- {-# REWRITE σ-Dull-Restr #-}

-- postulate
--   subst-D⁺ : ∀{σ : Δ ⇛ Γ} {A : Dull Γ ⊢Type} -> (D⁺ A) [ σ ] ≣ (D⁺ (A [ Dull-⇛ σ ]))
--   subst-D⁻ : ∀{σ : Δ ⇛ Γ} {A : Dull Γ ⊢Type} -> (D⁻ A) [ σ ] ≣ (D⁻ (A [ Dull-⇛ σ ]))
--   subst-NN : ∀{σ : Δ ⇛ Γ} -> NN [ σ ] ≣ NN
--   subst-End : ∀{σ : Δ ⇛ Γ} -> End [ σ ] ≣ End

--   β-Dull-D⁻ : ∀{Γ : Ctx (+- , τ)} -> ∀{A : Dull Γ ⊢Type} -> Dull {Γ = Γ} ((D⁻ A)) ≣ A

--   β-Restr-D⁻ : ∀{Γ : Ctx (+- , τ)} -> ∀{A : Dull Γ ⊢Type} -> ∀{v : Γ ⊢Var (D⁻ A)} -> Restr-Type ((D⁻ A)) v ≣ (D⁻ (Restr-Type A (Dull-Var v)))


-- {-# REWRITE subst-D⁺ subst-D⁻ subst-NN subst-End #-}
-- {-# REWRITE β-Dull-D⁻ #-}
-- {-# REWRITE β-Restr-D⁻ #-}





-- wk-Type : ∀{Γ : Ctx K} {A} -> Γ ⊢Type -> Γ ,[ A ] ⊢Type
-- wk-Type x = {!!}


-- inj : {X : Γ ⊢Type} -> {v : Γ ⊢Var X} -> ∀{x} -> Γ [ v ≔ x ] ⊢Type -> Γ ⊢Type
-- inj = {!!}


data _⊢Var_ where
  zero : ∀{A} -> Γ ,[ A ] ⊢Var (wk-Type A)
  suc : ∀{A B} -> Γ ⊢Var A -> Γ ,[ B ] ⊢Var (wk-Type A)

data _⊢Var : Ctx L -> 𝒰₀ where
  zero : Γ ,[ A ] ⊢Var
  suc : Γ ⊢Var -> Γ ,[ A ] ⊢Var

_⇂_ : (Γ : Ctx L) -> Γ ⊢Var -> Ctx L
(Γ ,[ A ]) ⇂ zero = Γ
(Γ ,[ A ]) ⇂ suc i = Γ ⇂ i

infixl 70 _⇂_

_＠_ : (Γ : Ctx L) -> (i : Γ ⊢Var) -> Γ ⇂ i ⊢Type
(Γ ,[ A ]) ＠ zero = A
(Γ ,[ A ]) ＠ suc i = Γ ＠ i

infixl 80 _＠_


_[_]-Ctx₊ : Δ ⊢Ctx₊ -> Γ ⇛♮ Δ -> Γ ⊢Ctx₊

_[lift_]-Type : ∀{E} -> ((Δ ⋆-Ctx₊ E) ⊢Type) -> (σ : Γ ⇛♮ Δ) -> (Γ ⋆-Ctx₊ (E [ σ ]-Ctx₊)) ⊢Type

-- _[_]-Ctx : Γ ⇛♮ Δ -> Δ ⊢Ctx -> Γ ⊢Ctx
-- _[_]-Ctx = {!!}


-- _⋆-⇛_ : (σ : Γ ⇛♮ Δ) -> (E : Δ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ (E [ σ ]-Ctx₊)) ⇛♮ (Δ ⋆-Ctx₊ E)

_[_]-Ctx₊ [] σ = []
_[_]-Ctx₊ (E ,[ x ]) σ = (E [ σ ]-Ctx₊) ,[ _[lift_]-Type {E = E} x σ ]

-- σ ⋆-⇛ [] = σ
-- σ ⋆-⇛ (E ,[ x ]) = {!!}

sub : ∀ i -> Γ ⇂ i ⊢ Γ ＠ i -> Γ ⇂ i ⇛♮ Γ ⇂ i ,[ Γ ＠ i ]
sub zero x = ♮-⇛ id , {!!}
sub (suc i) x = sub i x

_↾_ : (Γ : Ctx L) -> (i : Γ ⊢Var) -> Γ ⇂ i ,[ Γ ＠ i ] ⊢Ctx₊

η-⇂↾ : ∀{i} -> (Γ ⇂ i ,[ Γ ＠ i ]) ⋆-Ctx₊ (Γ ↾ i) ≣ Γ

(Γ ,[ A ]) ↾ zero = []
(Γ ,[ A ]) ↾ suc i = (Γ ↾ i) ,[ transp-≣ (cong-≣ (λ ξ -> ξ ⊢Type) (sym-≣ η-⇂↾)) A  ]

η-⇂↾ {Γ = Γ ,[ A ]} {i = zero} = refl-≣
η-⇂↾ {Γ = Γ ,[ A ]} {i = suc i} with ((Γ ⇂ i ,[ Γ ＠ i ]) ⋆-Ctx₊ (Γ ↾ i)) | η-⇂↾ {Γ = Γ} {i = i}
... | .Γ | refl-≣ = refl-≣

{-# REWRITE η-⇂↾ #-}

PP1 : {A : 𝒰 𝑖} {a : A} -> (p : a ≣ a) -> p ≣ refl-≣
PP1 refl-≣ = refl-≣

Test : ∀{Γ : Ctx L} {i} -> η-⇂↾ {Γ = Γ} {i = i} ≣ refl-≣
Test = PP1 η-⇂↾

{-# REWRITE Test #-}

-- Test {i = zero} = refl-≣
-- Test {Γ = Γ ,[ A ]} {i = suc i} = {!!}
-- with ((Γ ⇂ i ,[ Γ ＠ i ]) ⋆-Ctx₊ (Γ ↾ i))  | η-⇂↾ {Γ = Γ} {i = i}
-- ... | P | Q = {!!}


su-Type : ∀ i -> (x : Γ ⇂ i ⊢ Γ ＠ i) -> Γ ⊢Type -> ((Γ ⇂ i) ⋆-Ctx₊ ((Γ ↾ i) [ sub i x ]-Ctx₊)) ⊢Type
su-Type i x (Base x₁) = Base x₁
su-Type i x (⨉ c A B) = ⨉ c (su-Type i x A) let B' = su-Type (suc i) x B in {!!}
su-Type i x (D x₁ X) = {!!}
su-Type i x (Fam x₁) = {!!}

su-Type₂ : ∀{E} -> (x : Γ ⊢ A) -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ (E [ ♮-⇛ id , {!!} ]-Ctx₊)) ⊢Type
su-Type₂ x (Base x₁) = Base x₁
su-Type₂ {E = E} x (⨉ c A B) = ⨉ c (su-Type₂ {E = E} x A) let B' = su-Type₂ {E = E ,[ A ]} x B in {!!} 
su-Type₂ x (D x₁ X) = {!!}
su-Type₂ x (Fam x₁) = {!!}

_[lift_]-Type {E = E} X ε = {!!}
_[lift_]-Type {E = E} X (_,_ {A = A} σ x) =
  let -- E2 = [ A ]Ctx₊∷ E
      Y = _[lift_]-Type {E = [ A ]Ctx₊∷ E} X σ
  in {!!}

-- X [ ε ]-Type = {!!}
-- X [ σ , x ]-Type = {!let Y = su-Type zero !}

---------------------------------------------
-- rewriting for single substitution
-- postulate
-- ssubst-zero : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A} {x : Restr-Ctx (Γ ,[ A ]) zero ⊢ Restr-Type (wk-Type A) zero} -> (Γ ,[ A ]) [ zero ≔ x ] ≣ Γ --  & A wit x

--   -- ssubst-zero-End : ∀{τ}{Γ : Ctx (◌ , τ)} -> {x : Restr (Γ ,[ End ]) zero ⊢ Restr-Type (End) zero} -> (Γ ,[ End ]) [ zero ≔ x ] ≣ Γ
--   -- ssubst-suc : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A B v} {x : Γ ⊢ B} -> (Γ ,[ A ]) [ suc v ≔ x [ wk ]t ] ≣ (Γ [ v ≔ x ]) ,[ A [ σ-subst-Ctx ] ]

-- {-# REWRITE ssubst-zero #-}
-- {-# REWRITE ssubst-zero ssubst-suc #-}
--
---------------------------------------------




Restr-Ctx (Γ ,[ A ]) zero = Γ
Restr-Ctx (Γ ,[ A ]) (suc v) = Restr-Ctx Γ v

Restr-Type .(wk-Type A) (zero {A = A}) = A
Restr-Type .(wk-Type A) (suc {A = A} v) = Restr-Type A v

_[_≔_] (Γ ,[ A ]) (zero {A = A}) x = Γ
_[_≔_] (Γ ,[ B ]) {A} (suc v) x = (Γ [ v ≔ x ]) ,[ B [ ♮-⇛ σ-subst-Ctx ]-Type ]


  -- Dull-Var : ∀{A : Dull Γ ⊢Type} -> Γ ⊢Var (D⁻ A) -> Dull Γ ⊢Var A
-- Dull-Var v = {!!}


data _⊢_ where
  var : ∀{A} -> Γ ⊢Var A -> Γ ⊢ A
  -- γ_,_ : ∀(ϕ : K ⇌ L) {A}
  --     -> ⟨ ϕ ⦙ Γ ⊢ A
  --     -> Γ ⊢ A ⦙ ϕ ⟩
  Λ_ : ∀{X A} -> Γ ,[ X ] ⊢ A -> Γ ⊢ (⨇ X A)
  -- _,_ : ∀{A B} -> Γ ⊢ A -> Γ ,[ A ] ⊢ B -> Γ ⊢ ⨈ A B
  inv : ∀{X} -> Γ ⊢ (D⁺ X) -> Γ ⊢ (D⁻ X)
  -- [_≔_]_ : ∀{τ Γ} {X : Dull {τ = τ} Γ ⊢Type} -> (v : Γ ⊢Var (D⁻ X)) -> (x : Γ ⊢ (D⁺ X)) -> ∀{Y}
  --   -> (Γ [ v ≔ inv x ]) ⊢ Y
  --   -> Γ ⊢ (Y [ ι-subst-Ctx ])
  end : Γ ⊢ (D⁺ (Base End))
  n0 : Γ ⊢ Base NN

  -- WARNING: this is probably wrong because
  -- this means that we can use all negative
  -- things in Γ
  d⁺ : ∀{Γ : Ctx (+- , τ)} -> ∀{A} -> Dull Γ ⊢ A -> Γ ⊢ (D⁺ A)







{-
π₂ : ∀{A} -> (δ : Γ ⇛ (Δ ,[ A ])) -> Γ ⊢ (A [ ♮-⇛ (π₁ δ) ]-Type)
π₂ = {!!}

wk-⇛♮ : ∀{A} -> Γ ⇛♮ Δ -> Γ ,[ A ] ⇛♮ Δ
wk-⇛♮ = {!!}

_×-⇛♮_ : (σ : Γ ⇛♮ Δ) -> (A : Δ ⊢Type) -> Γ ,[ A [ σ ]-Type ] ⇛♮ Δ ,[ A ]
_×-⇛♮_ σ A = wk-⇛♮ σ , var {!zero!}

pb-Ctx : (σ : Γ ⇛♮ Δ) -> Δ ⊢Ctx -> Γ ⊢Ctx

-- pb-Type : (σ : Γ ⇛♮ Δ) -> {ΔE : Δ ⊢Ctx} -> (Δ ⋆-Ctx ΔE) ⊢Type -> (Γ ⋆-Ctx pb-Ctx σ ΔE) ⊢Type

pb-Ctx σ [] = []
pb-Ctx σ ([ A ]∷ Δ) = [ A [ σ ]-Type ]∷ pb-Ctx (σ ×-⇛♮ A) Δ


ext-⇛♮ : (σ : Γ ⇛♮ Δ) -> (ΔE : Δ ⊢Ctx) -> (Γ ⋆-Ctx pb-Ctx σ ΔE) ⇛♮ (Δ ⋆-Ctx ΔE)
ext-⇛♮ σ [] = {!!} -- σ
ext-⇛♮ σ ([ A ]∷ ΔE) = {!!} -- ext-⇛♮ (σ ×-⇛♮ A) ΔE

-- X [ σ ×-⇛♮ _ ]-Type

su-Type : ∀{A} -> (x : Γ ⊢ A) -> (Γ ,[ A ]) ⊢Type -> Γ ⊢Type
su-Type x X = {!!}

su-Ctx : Γ ⊢ A -> Γ ,[ A ] ⊢Ctx -> Γ ⊢Ctx
su-Ctx = {!!}

su-Ctx₊ : Γ ⊢ A -> Γ ,[ A ] ⊢Ctx₊ -> Γ ⊢Ctx₊
su-Ctx₊ = {!!}
-- su-Ctx {Γ = []} x E = {!!}
-- su-Ctx {Γ = Γ ,[ x₁ ]} x E = {!!}

-- su-Ctx+ : ∀{E} -> (x : Γ ⊢ A) -> (Γ ,[ A ] ⋆-Ctx E) ⊢Ctx -> (Γ ⋆-Ctx su-Ctx x E) ⊢Ctx

-- su-Ctx x [] = []
-- su-Ctx x ([ A ]∷ []) = [ su-Type x A ]∷ []
--   -- let ZZ = su-Ctx+ {E = [ _ ]∷ []} x E
--   -- in [ su-Type x A ]∷ {!!}
-- su-Ctx x ([ A ]∷ E@([ A2 ]∷ E2)) = -- su-Ctx+ {E = [ _ ]∷ []} x ([ A ]∷ E)
--   let ZZ = su-Ctx+ {E = [ _ ]∷ []} x E
--   in [ su-Type x A ]∷ ZZ

-- su-Ctx+ {E = []} x X = su-Ctx x X
-- su-Ctx+ {E = [ A ]∷ []} x X = {!!} -- su-Ctx+ {E = [ _ ]∷ _} x X
-- su-Ctx+ {E = [ A ]∷ ([ A₁ ]∷ E)} x X = {!!}


su-Type+ : ∀{A E} -> (x : Γ ⊢ A) -> (Γ ,[ A ] ⋆-Ctx E) ⊢Type -> (Γ ⋆-Ctx (su-Ctx x E)) ⊢Type
su-Type+ {Γ = []} x X = {!!}
su-Type+ {Γ = Γ ,[ x₁ ]} x X = {!!}

su-Type* : ∀{A E} -> (x : Γ ⊢ A) -> (Γ ,[ A ] ⋆-Ctx₊ E) ⊢Type -> (Γ ⋆-Ctx₊ (su-Ctx₊ x E)) ⊢Type
su-Type* {E = []} x X = {!!}
su-Type* {E = E ,[ x₁ ]} x X = {!!}

-- su-Type+ {E = []} x X = {!!}
-- su-Type+ {E = [ A ]∷ E} x X = {!!}

pb-Type : ∀{A} -> (σ : Γ ⇛♮ Δ) -> (Δ ,[ A ]) ⊢Type -> (Γ ,[ A [ σ ]-Type ]) ⊢Type

X [ ε ]-Type = {!!}
X [ σ , x ]-Type = {!!} -- su-Type x (pb-Type σ X)

pb-Type ε X = {!!}
pb-Type (σ , x) X = {!!}
-- X [ σ ×-⇛♮ A ]-Type = {!!}

_[_]-Ctx : Δ ⊢Ctx -> (σ : Γ ⇛♮ Δ) -> Γ ⊢Ctx
X [ ε ]-Ctx = {![]!}
X [ σ , x ]-Ctx = {!!}

pb-Type2 : (σ : Γ ⇛♮ Δ) -> {ΔE : Δ ⊢Ctx} -> (Δ ⋆-Ctx ΔE) ⊢Type -> (Γ ⋆-Ctx pb-Ctx σ ΔE) ⊢Type
pb-Type2 ε {ΔE} X = {!!}
pb-Type2 (σ , x) {ΔE} X =
  let X' = (pb-Type2 σ {[ _ ]∷ ΔE} X)
      X'' = su-Type+ {E = pb-Ctx (σ ×-⇛♮ _) ΔE} x X'
  in {!!}









wk-Term : ∀{A B} -> Γ ⊢ A -> Γ ,[ B ] ⊢ wk-Type A
wk-Term (var x) = {!!}
wk-Term (Λ t) = {!!}
wk-Term (inv t) = {!!}
wk-Term end = {!!}
wk-Term n0 = {!!}
-- wk-Term (π₂ δ) = {!!}
wk-Term (d⁺ t) = {!!}

_[_]-Term : ∀{Γ Δ : Ctx L} -> ∀{A : Γ ⊢Type} -> Γ ⊢ A -> (σ : Δ ⇛♮ Γ) -> Δ ⊢ (A [ σ ]-Type)
-- t [ id ]-Term = t
-- t [ π₁ σ ]-Term = wk-Term t [ σ ]-Term
-- t [ σ , x ]-Term = {!!}
-- t [ σ ◆-⇛ σ₁ ]-Term = {!!}
-- t [ ε ]-Term = {!!}



-- wk-⇛♮-≣ : {x : Δ ⊢Type} {σ : Γ ⇛♮ Δ ,[ x ]} {A : Γ ⊢Type} -> wk-Type {A = A} (wk-Type x [ σ ]-Type) ≣ x [ wk-⇛♮ (♮-⇛ (π₁ σ)) ]-Type
-- wk-⇛♮-≣ = {!!}

-- wk-⇛♮ {Δ = []} σ = ε
-- wk-⇛♮ {Γ = Γ} {Δ = Δ ,[ x ]} {A = A} σ = wk-⇛♮ (π₁ σ) ,
--   let P : wk-Type (wk-Type x [ σ ]-Type) ≣ x [ wk-⇛♮ (π₁ σ) ]-Type
--       P = wk-⇛♮-≣ {Δ = Δ}
--       Q : Γ ,[ A ] ⊢ ap₀ P ≣ Γ ,[ A ] ⊢ ap₁ P
--       Q = cong-≣ (λ ξ -> Γ ,[ A ] ⊢ ξ) P
--   in transp-≣ Q (π₂ σ [ π₁ id ]-Term)

σ-wk-⇛♮-wk-type : {x : Δ ⊢Type} {σ : Γ ⇛♮ Δ} {A : Γ ⊢Type} -> (wk-Type {A = A} (x [ σ ]-Type)) ≣ x [ wk-⇛♮ σ ]-Type
σ-wk-⇛♮-wk-type {fst₁ , snd₁} {Δ = []} = {!!}
σ-wk-⇛♮-wk-type {Δ = Δ ,[ x ]} = {!!}

-- (Γ ,[ A ]) [ zero ≔ x ] != Γ 
σ-subst-Ctx {v = zero {Γ = Γ}{A = A}} {x} = id , {!!}
σ-subst-Ctx {v = suc {Γ = Γ} {B = B} v} {x} = {!!}
  -- let P = σ-subst-Ctx {v = v} {x = x}
  --     X : ((Γ [ v ≔ x ]) ,[ B [ P ]-Type ]) ⇛♮ ((Γ [ v ≔ x ]) ,[ B [ P ]-Type ])
  --     X = id
  --     R : ((Γ [ v ≔ x ]) ,[ B [ P ]-Type ]) ⊢ (B [ wk-⇛♮ P ]-Type)
  --     R = π₂ {Δ = Γ [ v ≔ x ]} {A = B [ P ]-Type} {!X!}
  -- in wk-⇛♮ P , {!π₂ id!} -- wk-⇛♮ P , R -- (π₂ {Δ = Γ [ v ≔ x ]} {A = B [ P ]-Type} (id {Γ = (Γ [ v ≔ x ]) ,[ B [ P ]-Type ]}))

ssubst-zero = refl-≣

---------------------------------------------
-- rewriting for single substitution
-- postulate
--   ssubst-zero : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A} {x : Restr (Γ ,[ A ]) zero ⊢ Restr-Type (A [ wk ]) zero} -> (Γ ,[ A ]) [ zero ≔ x ] ≣ Γ --  & A wit x
--   -- ssubst-zero-End : ∀{τ}{Γ : Ctx (◌ , τ)} -> {x : Restr (Γ ,[ End ]) zero ⊢ Restr-Type (End) zero} -> (Γ ,[ End ]) [ zero ≔ x ] ≣ Γ
--   -- ssubst-suc : ∀{τ}{Γ : Ctx (+- , τ)} -> ∀{A B v} {x : Γ ⊢ B} -> (Γ ,[ A ]) [ suc v ≔ x [ wk ]t ] ≣ (Γ [ v ≔ x ]) ,[ A [ σ-subst-Ctx ] ]

-- {-# REWRITE ssubst-zero #-}
-- {-# REWRITE ssubst-zero ssubst-suc #-}
--
---------------------------------------------

-- {-# REWRITE subst-D⁺ #-}

---------------------------------------------
-- Special rewriting rules involving terms

-- postulate
--   subst-Fam : ∀{σ : Δ ⇛ Γ} {x : Γ ⊢ NN} -> (Fam x) [ σ ] ≣ (Fam (x [ σ ]t))

--
---------------------------------------------

-}

module Examples where
  emp : Ctx (+- , 𝟙)
  emp = []

  -- F1 : ε ⊢ (⨇ ((D⁺ (NN))) (⨇ ((D⁻ (NN))) (D⁺ (End))))
  -- F1 = Λ (Λ ([ zero ≔ var (suc zero) ] end) )

{-
  -- T1 : (ε ,[ (D⁻ (NN)) ]) [ zero ≔ inv (d⁺ n0) ] ≣ ε
  -- T1 = {!refl-≣!}

  -- F2 : ε ⊢ (⨇ ((D⁻ (NN))) (⨇ ((D⁺ ((Fam (var zero))))) (D⁺ ((Fam (n0))))))
  -- F2 = Λ (Λ ([ suc zero ≔ d⁺ n0 ] {!var zero!}) )

  -- Λ (Λ ([ zero ≔ var (suc zero) ] end))

-}
