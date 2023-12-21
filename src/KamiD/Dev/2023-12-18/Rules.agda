{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2023-12-18.Rules where

open import Agora.Conventions hiding (Σ ; Lift)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2023-12-18.Core

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

instance
  hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx L) (_⊢Ctx₊) (λ _ _ -> Ctx L)
  hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }

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

Dull-Ctx₊ : Γ ⊢Ctx₊ -> Dull-Ctx Γ ⊢Ctx₊

β-Dull-⋆ : ∀{E} -> Dull-Ctx (Γ ⋆-Ctx₊ E) ≣ Dull-Ctx Γ ⋆-Ctx₊ Dull-Ctx₊ E

Dull-Ctx₊ [] = []
Dull-Ctx₊ (E ,[ x ]) = Dull-Ctx₊ E ,[ transp-≣ (cong-≣ _⊢Type (β-Dull-⋆ {E = E})) (Dull-Type x) ]

β-Dull-⋆ {E = []} = refl-≣
β-Dull-⋆ {E = E ,[ x ]} =
  let X = J1 (β-Dull-⋆ {E = E}) _⊢Type _,[_] (Dull-Type x)
  in sym-≣ X

{-# REWRITE β-Dull-⋆ #-}




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


-- wk : ∀{Γ : Ctx L} {A : Γ ⊢Type} -> (Γ ,[ A ] ⇛ Γ)
-- wk = π₁ id

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

{-
_＠_ : (Γ : Ctx L) -> (i : Γ ⊢Var) -> Γ ⇂ i ⊢Type
(Γ ,[ A ]) ＠ zero = A
(Γ ,[ A ]) ＠ suc i = Γ ＠ i

infixl 80 _＠_
-}



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
  -- [_≔_]_ : ∀{E} -> (X : Dull Γ ⊢Type) -> (v : Γ ⋆-Ctx₊ E ⊢ D⁻ )

  -- [_≔_]_ : ∀{τ Γ} {X : Dull {τ = τ} Γ ⊢Type} -> (v : Γ ⊢Var (D⁻ X)) -> (x : Γ ⊢ (D⁺ X)) -> ∀{Y}
  --   -> (Γ [ v ≔ inv x ]) ⊢ Y
  --   -> Γ ⊢ (Y [ ι-subst-Ctx ])
  end : Γ ⊢ (D⁺ (Base End))
  n0 : Γ ⊢ Base NN

  -- WARNING: this is probably wrong because
  -- this means that we can use all negative
  -- things in Γ
  d⁺ : ∀{Γ : Ctx (+- , τ)} -> ∀{A} -> Dull Γ ⊢ A -> Γ ⊢ (D⁺ A)

Dull-Term : Γ ⊢ A -> Dull-Ctx Γ ⊢ Dull-Type A
Dull-Term = {!!}


⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx L) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

id-⇛♮ : Γ ⇛♮ Γ

-- {-# REWRITE β-id-Type #-}

_[_]-Ctx₊ : Δ ⊢Ctx₊ -> Γ ⇛♮ Δ -> Γ ⊢Ctx₊

under_by_[_]-Type : ∀ E -> ((Δ ⋆-Ctx₊ E) ⊢Type) -> (σ : Γ ⇛♮ Δ) -> (Γ ⋆-Ctx₊ (E [ σ ]-Ctx₊)) ⊢Type


-- This should be true (currently) because ...

{-
----------------------------------------------------------------
-- Trying to proof termination
-- data <Ctx₊Type : (E : Γ ⊢Ctx₊) -> Γ ⋆-Ctx₊ E ⊢Type -> 𝒰₀ where
data <Ctx₊ : (E : Γ ⊢Ctx₊) -> 𝒰₀ where
  add : ∀{E A} -> <Ctx₊ E -> <Ctx₊ (E ,[ A ])

wk-Ctx₊ : (E : Γ ⊢Ctx₊) -> <Ctx₊ E -> Γ ,[ A ] ⊢Ctx₊

wk-Type-ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Type) -> (P : <Ctx₊ E) -> (Q : <Ctx₊ (E ,[ Z ])) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E P ⊢Type

wk-Ctx₊ [] P = []
wk-Ctx₊ (E ,[ x ]) P = wk-Ctx₊ E {!!} ,[ wk-Type-ind E x {!!} {!P!} ]

wk-Type-ind E (Base x) P Q = Base x
wk-Type-ind E (⨉ c A B) P Q = ⨉ c (wk-Type-ind E A {!!} {!!}) (wk-Type-ind (E ,[ A ]) B {!!} {!!})
wk-Type-ind E (D x X) P Q = {!!}
wk-Type-ind E (Fam x) P Q = {!!}


wk-Type₊-ind : ∀ E -> Γ ⋆-Ctx₊ E ⊢Type -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E {!!} ⊢Type
wk-Type₊-ind = {!!}

wk-Term-ind : ∀ E -> (X : Γ ⋆-Ctx₊ E ⊢Type) -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E {!!} ⊢ wk-Type₊-ind E X
wk-Term-ind = {!!}
--
----------------------------------------------------------------
-}


{-# TERMINATING #-}
wk-Ctx₊ : (E : Γ ⊢Ctx₊) -> Γ ,[ A ] ⊢Ctx₊

wk-Type-ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Type) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Type

wk-Ctx₊ [] = []
wk-Ctx₊ (E ,[ x ]) = wk-Ctx₊ E ,[ wk-Type-ind E x ]

wk-Type-ind E (Base x) = Base x
wk-Type-ind E (⨉ c A B) = ⨉ c (wk-Type-ind E A ) (wk-Type-ind (E ,[ A ]) B)
wk-Type-ind E (D x X) = {!!}
wk-Type-ind E (Fam x) = {!!}

wk-Type X = wk-Type-ind [] X -- [ wk-⇛♮ id-⇛♮ ]-Type

wk-Term-ind : ∀ E -> (X : Γ ⋆-Ctx₊ E ⊢Type) -> Γ ⋆-Ctx₊ E ⊢ X -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢ wk-Type-ind E X
wk-Term-ind = {!!}

wk-Term : (X : Γ ⊢Type) -> Γ ⊢ X -> Γ ,[ A ] ⊢ wk-Type X
wk-Term X t = wk-Term-ind [] X t




wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ






_[_]-Ctx₊ [] σ = []
_[_]-Ctx₊ (E ,[ x ]) σ = (E [ σ ]-Ctx₊) ,[ under E by x [ σ ]-Type ]



_[_]-Type X σ = under [] by X [ σ ]-Type


β-wk-σ : ∀{Γ Δ : Ctx L} -> {A : Δ ⊢Type} -> (E : Γ ⊢Ctx₊) -> {B : Γ ⊢Type} -> {σ : Γ ⋆-Ctx₊ E ⇛♮ Δ} -> under [] by A [ wk-⇛♮-ind {A = B} E σ ]-Type  ≣ wk-Type-ind E (A [ σ ]-Type)
β-wk-σ = {!!}

β-wk-σ-[] : {B : Γ ⊢Type} -> {σ : Γ ⇛♮ Δ} -> under [] by A [ wk-⇛♮-ind {A = B} [] σ ]-Type ≣ wk-Type-ind [] (A [ σ ]-Type)
β-wk-σ-[] = β-wk-σ []

{-# REWRITE β-wk-σ β-wk-σ-[] #-}




wk-⇛♮-ind E ε = ε
wk-⇛♮-ind E (σ , x) = wk-⇛♮-ind E σ ,
  let XX = wk-Term-ind E _ x
  in ⟨ _ ⊢⇂ (sym-≣ (β-wk-σ E {σ = σ})) ⇃⟩ XX

wk-⇛♮ : ∀{A} -> Γ ⇛♮ Δ -> Γ ,[ A ] ⇛♮ Δ
wk-⇛♮ σ = wk-⇛♮-ind [] σ






β-id-Type : under [] by A [ id-⇛♮ ]-Type ≣ A
β-id-Type = {!!}

{-# REWRITE β-id-Type #-}

β⁻¹-id-Type : A ≣ A [ id-⇛♮ ]-Type
β⁻¹-id-Type = sym-≣ β-id-Type

id-⇛♮ {Γ = []} = ε
id-⇛♮ {Γ = Γ ,[ x ]} = wk-⇛♮ id-⇛♮ , var zero

-- This one comes from β-id-Type (and others?)
β-wk : ∀{B} -> A [ wk-⇛♮ {A = B} id-⇛♮ ]-Type ≣ wk-Type-ind [] A
β-wk = refl-≣




lift-sub : (σ : Γ ⇛♮ Δ) -> Γ ,[ A [ σ ]-Type ] ⇛♮ Δ ,[ A ]
lift-sub {Γ = Γ} {A = A} σ = wk-⇛♮ σ ,
  let X : (Γ ,[ A [ σ ]-Type ]) ⊢ (wk-Type (A [ σ ]-Type))
      X = var zero
  in X



-- {-# TERMINATING #-}
β-comp-Ctx₊ : {E : Δ ,[ A ] ⊢Ctx₊} -> {σ : Γ ⇛♮ Δ} {x : Γ ⊢ (A [ σ ]-Type)} -> ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊) ≣ E [ σ , x ]-Ctx₊
β-comp-Ctx₊ = {!!}


{-# REWRITE β-comp-Ctx₊ #-}


-- sub : ∀ i -> Γ ⇂ i ⊢ Γ ＠ i -> Γ ⇂ i ⇛♮ Γ ⇂ i ,[ Γ ＠ i ]
-- sub zero x = ♮-⇛ id , {!!}
-- sub (suc i) x = sub i x

{-
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

-}


split-front-Ctx₊ : {A : Γ ⊢Type} -> ∀{E} {σ : Δ ⇛♮ Γ} -> ([ A ]Ctx₊∷ E) [ σ ]-Ctx₊ ≣ [ A [ σ ]-Type ]Ctx₊∷ (E [ lift-sub σ ]-Ctx₊)
split-front-Ctx₊ = {!!}

{-# REWRITE split-front-Ctx₊ #-}




-- su-Type : ∀ i -> (x : Γ ⇂ i ⊢ Γ ＠ i) -> Γ ⊢Type -> ((Γ ⇂ i) ⋆-Ctx₊ ((Γ ↾ i) [ sub i x ]-Ctx₊)) ⊢Type
-- su-Type i x (Base x₁) = Base x₁
-- su-Type i x (⨉ c A B) = ⨉ c (su-Type i x A) let B' = su-Type (suc i) x B in {!!}
-- su-Type i x (D x₁ X) = {!!}
-- su-Type i x (Fam x₁) = {!!}

-- 2Type⦅_∣_⦆_ : ∀ E -> (x : Γ ⋆-Ctx₊ wk-Ctx₊ A E ⊢ ?) -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ (Ctx⦅ x ⦆ E)) ⊢Type


Ctx⦅_⦆_ : (x : Γ ⊢ A) -> (Γ ,[ A ]) ⊢Ctx₊ -> Γ ⊢Ctx₊

β-comp-Ctx₊₂ : {E : Δ ,[ A ] ⊢Ctx₊} -> {σ : Γ ⇛♮ Δ} {x : Γ ⊢ (A [ σ ]-Type)} -> Ctx⦅ x ⦆ (E [ lift-sub σ ]-Ctx₊) ≣ E [ σ , x ]-Ctx₊

Type⦅_∣_⦆_ : (x : Γ ⊢ A) -> ∀ E -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ (Ctx⦅ x ⦆ E)) ⊢Type

su-Type₂ : ∀{E} -> (x : Γ ⊢ A) -> (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type -> (Γ ⋆-Ctx₊ Ctx⦅ x ⦆ E) ⊢Type
su-Type₂ {E = E} x T = Type⦅_∣_⦆_ x E T


infixr 90 Type⦅_∣_⦆_ Type⦅_∣_⦆_ Ctx⦅_⦆_

Term⦅_∣_⦆_ : (x : Γ ⊢ A) -> ∀ E -> {A : (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type} -> (t : _ ⊢ A) -> _ ⊢ Type⦅ x ∣ E ⦆ A

Ctx⦅ x ⦆ [] = []
Ctx⦅ x ⦆ (E ,[ A ]) = Ctx⦅ x ⦆ E ,[ Type⦅ x ∣ E ⦆ A ]

β-Dull-Ctx₊ : ∀{x : Γ ⊢ A} {E} -> Dull-Ctx₊ (Ctx⦅ x ⦆ E) ≣ Ctx⦅ Dull-Term x ⦆ (Dull-Ctx₊ E)
β-Dull-Ctx₊ {E = []} = refl-≣
β-Dull-Ctx₊ {E = E ,[ x ]} = {!!}

{-# REWRITE β-Dull-Ctx₊ #-}


Type⦅_∣_⦆_ x E (Base x₁) = Base x₁
Type⦅_∣_⦆_ x E (⨉ c A B) = ⨉ c (su-Type₂ {E = E} x A) let B' = su-Type₂ {E = E ,[ A ]} x B in B'
Type⦅_∣_⦆_ x E (D c A) = D c (Type⦅ Dull-Term x ∣ Dull-Ctx₊ E ⦆ A)
Type⦅_∣_⦆_ x E (Fam n) = Fam (Term⦅ x ∣ E ⦆ n)


β-comp-Ctx₊₂ = {!!}

-- σ-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{E B} -> Type⦅ x ∣ E ,[ B ] ⦆ (wk-Type B) ≣ wk-Type (Type⦅ x ∣ E ⦆ B)
σ-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{E X B} -> Type⦅ x ∣ E ,[ X ] ⦆ (wk-Type B) ≣ wk-Type (Type⦅ x ∣ E ⦆ B)
σ-su-wk-Type = {!!}

β-su-wk-Type : ∀{x : Γ ⊢ A} -> ∀{B} -> Type⦅ x ∣ [] ⦆ (wk-Type B) ≣ B
β-su-wk-Type = {!!}

{-# REWRITE β-comp-Ctx₊₂ σ-su-wk-Type β-su-wk-Type #-}

Var⦅_∣_⦆_ : (x : Γ ⊢ A) -> ∀ E -> {A : (Γ ,[ A ]) ⋆-Ctx₊ E ⊢Type} -> (v : _ ⊢Var A) -> _ ⊢ Type⦅ x ∣ E ⦆ A
Var⦅ x ∣ [] ⦆ zero = x
Var⦅ x ∣ [] ⦆ suc v = var v
Var⦅_∣_⦆_ {Γ = Γ} x (E ,[ B ]) zero = var zero
Var⦅ x ∣ E ,[ B ] ⦆ suc v = wk-Term _ (Var⦅ x ∣ E ⦆ v)

Term⦅ x ∣ E ⦆ var v = Var⦅ x ∣ E ⦆ v
Term⦅ x ∣ E ⦆ (Λ t) = Λ (Term⦅ x ∣ E ,[ _ ] ⦆ t)
Term⦅ x ∣ E ⦆ inv t = let tt = Term⦅ x ∣ E ⦆ t in inv tt
Term⦅ x ∣ E ⦆ end = end
Term⦅ x ∣ E ⦆ n0 = n0
Term⦅ x ∣ E ⦆ d⁺ t = {!!}



under_by_[_]-Type E X ε = {!!}
under_by_[_]-Type {Γ = Γ} E X (_,_ {A = A} σ x) =
  let Y = under_by_[_]-Type ([ A ]Ctx₊∷ E) X σ

      -- X2 : (Γ ⋆-Ctx₊ ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊)) ⊢Type
      -- X2 = {!!} -- su-Type₂ {E = (E [ lift-sub σ ]-Ctx₊)} x Y

      X3 = su-Type₂ {E = (E [ lift-sub σ ]-Ctx₊)} x Y

      -- p : (Γ ⋆-Ctx₊ ((E [ lift-sub σ ]-Ctx₊) [ id-⇛♮ , x ]-Ctx₊)) ⊢Type ≣ (Γ ⋆-Ctx₊ (E [ σ , x ]-Ctx₊)) ⊢Type
      -- p = cong-≣ (λ ξ -> Γ ⋆-Ctx₊ ξ ⊢Type) (β-comp-Ctx₊ {E = E} {σ = σ} {x = x})

      -- Res : (Γ ⋆-Ctx₊ (E [ σ , x ]-Ctx₊)) ⊢Type
      -- Res = transp-≣ p X2
  in X3



module Examples where
  emp : Ctx (+- , 𝟙)
  emp = []

  -- F1 : ε ⊢ (⨇ ((D⁺ (NN))) (⨇ ((D⁻ (NN))) (D⁺ (End))))
  -- F1 = Λ (Λ ([ zero ≔ var (suc zero) ] end) )

{-
  -- T1 : (ε ,[ (D⁻ (NN)) ]) [ zero ≔ inv (d⁺ n0) ] ≣ ε
  -- T1 = {!refl-≣!}

-}

  -- F2 : ε ⊢ (⨇ ((D⁻ (NN))) (⨇ ((D⁺ ((Fam (var zero))))) (D⁺ ((Fam (n0))))))
  -- F2 = Λ (Λ ([ suc zero ≔ d⁺ n0 ] {!var zero!}) )

  -- Λ (Λ ([ zero ≔ var (suc zero) ] end))





