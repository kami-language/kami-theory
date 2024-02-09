{-# OPTIONS --allow-unsolved-metas #-}

module KamiD.Dev.2023-11-19.Rules where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-19.Core

Name = ℕ

--------------------------------------------------------------------
-- Plan: we need two contexts: one for shapes, one for types!
--
-- Reason: types exist sometimes in a role-restricted context,
-- i.e., to build this type, only variables existing at some
-- role are allowed. In order to restrict a context in the _⊢Type_
-- signature, we need to speak about roles here. This is only
-- possible if we don't define them as types of kind 𝑆.
--
-- Additionally: every type in the type context has a role at which it
-- lives, while a role does not have such an annotation...
--


data Shapes : 𝒰₀

private variable
  Σ : Shapes
data _⊢Shape : Shapes -> 𝒰₀
data _⊢NodeVar : Shapes -> 𝒰₀
data _⊢Node : Shapes -> 𝒰₀
data _⊢Nodes : Shapes -> 𝒰₀
data _<-NodeVar_ : (a b : Σ ⊢NodeVar) -> 𝒰₀
data _≤-Node_ : (a b : Σ ⊢Node) -> 𝒰₀
-- data ⊢_isNode : (Γ : Shapes) -> (i : Fin ∣ Γ ∣) -> 𝒰₀

data _⊢Ctx : Shapes -> 𝒰₀

private variable
  Γ : Σ ⊢Ctx

-- record RCtx Σ : 𝒰₀ where
--   inductive
--   constructor _at_
--   field fst : Ctx Σ
--   field snd : Σ ⊢Node

-- data _⊢Shapes : (Γ : Ctx) -> 𝒰₀
-- data _⊢Kind : (Γ : Ctx) -> 𝒰₀
data _⨾_at_⊢Type : ∀ Σ -> Σ ⊢Ctx -> Σ ⊢Node -> 𝒰₀
-- data _⊢Type : (Γ : Ctx) -> 𝒰₀
-- data _⊢Var!_ : (Γ : Ctx) ->  -> 𝒰₀
data _⨾_at_⊢_ : ∀ Σ Γ i -> Σ ⨾ Γ at i ⊢Type -> 𝒰₀
-- data _⊇_ : (Γ : Ctx) (Δ : Ctx) -> 𝒰₀

-- infixl 40 _⊇_


data _⊢Nodes where
  [] : Σ ⊢Nodes
  _&_ : Σ ⊢Nodes -> Σ ⊢NodeVar -> Σ ⊢Nodes

infixl 30 _&_

data _⊢Shape where
  𝒮 : Σ ⊢Nodes -> Σ ⊢Shape

data Shapes where
  [] : Shapes
  _,[_∶_] : (Σ : Shapes) -> Name -> Σ ⊢Shape -> Shapes

data _⊢NodeVar where
  zero : ∀{i S} -> Σ ,[ i ∶ S ] ⊢NodeVar
  suc : ∀{i S} -> Σ ⊢NodeVar -> Σ ,[ i ∶ S ] ⊢NodeVar

data _⊢Node where
  var : Σ ⊢NodeVar -> Σ ⊢Node
  ∅ : Σ ⊢Node
  ⩝_∶_,_ : ∀(x : Name) -> (S : Σ ⊢Shape) -> Σ ,[ x ∶ S ] ⊢Node -> Σ ⊢Node



data _<-NodeVar_ where
  -- base : 

data _≤-Node_ where
  refl-≤-Node : ∀{a : Σ ⊢Node} -> a ≤-Node a

data _⊢Ctx where
  [] : Σ ⊢Ctx
  _,[_at_∶_] : (Γ : Σ ⊢Ctx) -> Name -> ∀ i -> Σ ⨾ Γ at i ⊢Type -> Σ ⊢Ctx
  _↑ : Σ ⊢Ctx -> ∀{i S} -> (Σ ,[ i ∶ S ]) ⊢Ctx

infixl 50 _,[_at_∶_]

data _⨾_at_⊢Type where
  ⩝_∶_,_ :  (x : Name) -> (S : Σ ⊢Shape)
         -> ∀{i} -> Σ ,[ x ∶ S ] ⨾ Γ ↑ at i ⊢Type
         -> Σ ⨾ Γ at (⩝ x ∶ S , i) ⊢Type

  ⨇[_≤_][_∶_]_ : (a p : Σ ⊢Node) -> {{_ : a ≤-Node p}}
                -> (x : Name) -> (A : Σ ⨾ Γ at a ⊢Type)
                -> Σ ⨾ (Γ ,[ x at a ∶ A ]) at p ⊢Type
                -> Σ ⨾ Γ at p ⊢Type


pattern ⨇[_≤_by_][_∶_]_ a b x y z W = ⨇[_≤_][_∶_]_ a b {{x}} y z W
-- pattern ⨇[ a ≤ b by x ][ y ∶ z ] W = ⨇[_≤_][_∶_]_ a b {{x}} y z W

  -- var : ∀{Γ i k} -> Γ ⊢ i isKind k -> Γ ⊢Type k
  -- Shape : [] ⊢Type
  -- 𝒮 : ∀{Γ} -> Γ ⊢Shapes -> Γ ⊢Type 𝑆
  -- 𝟘 : ∀{Γ} -> Γ ⊢Type 𝑆
  -- Unit : ∀{Γ} -> Γ ⊢Type 𝑇
  -- ⩝_∶_,_ : ∀{Γ} -> (x : Name) -> (S : Γ ⊢Type 𝑆) -> ∀{k} -> Γ ,[ x ∶ S ] ⊢Type k -> Γ ⊢Type (⩝ x ∶ S , k)

data _⨾_at_⊢_ where


_⇒_ : ∀{a b x}
      -> (A : Σ ⨾ Γ at (var a) ⊢Type)
      -> (B : Σ ⨾ Γ at (var b) ⊢Type)
      -> Σ ,[ x ∶ 𝒮 ([] & a & b) ] ⨾ Γ ↑ at var zero ⊢Type
_⇒_ {a = a} {b} {x} A B = ⨇[ var (suc a) ≤ var zero by {!!} ][ 9 ∶ {!!} ] {!!}

-- _⇒_ : ∀{a b x}
--       -> (A : Σ ⨾ Γ at (var a) ⊢Type)
--       -> (B : Σ ⨾ Γ at (var b) ⊢Type)
--       -> Σ ⨾ Γ at (⩝ x ∶ 𝒮 ([] & a & b) , var zero) ⊢Type
-- _⇒_ {a = a} {b} {x} A B = ⩝ _ ∶ 𝒮 _ , {!⨇[ a ≤ zero by ? ][ ? ∶ ? ] ?!}
-- ⨇[ a ≤ p by ? ][ ? ∶ ? ] ?

module Example where
  Pt : Σ ⊢Shape
  Pt = 𝒮 []

  NN : [] ,[ 0 ∶ Pt ] ⨾ [] at {!!} ⊢Type
  NN = {!!}

  NN2 : [] ⨾ [] at ⩝ 0 ∶ Pt , ⩝ 1 ∶ 𝒮 ([] & zero) , var zero ⊢Type
  NN2 = ⩝ 0 ∶ Pt , (⩝ 1 ∶ _ , {!⨇[ ? ≤ ? ][ ? ∶ ? ] ?!} )



{-

-- data _⊢Kind where
--   𝑆 : ∀{Γ} -> Γ ⊢Kind
--   𝑇 : ∀{Γ} -> Γ ⊢Shapes -> Γ ⊢Kind
--   ⩝_∶_,_ : ∀{Γ} -> ∀ x -> {k : Γ ⊢Kind} -> (A : Γ ⊢Type k) -> Γ ,[ x ∶ A ] ⊢Kind -> Γ ⊢Kind
--   weak : ∀{Γ} -> ∀ {x} -> {k : Γ ⊢Kind} -> {A : Γ ⊢Type k} -> Γ ⊢Kind -> Γ ,[ x ∶ A ] ⊢Kind


len-Ctx : Ctx Σ -> ℕ
len-Ctx [] = 0
len-Ctx (Γ ,[ x atr i ∶ x₁ ]) = suc (len-Ctx Γ)

instance
  Notation-Absolute-Ctx : Notation-Absolute (Ctx Σ) ℕ
  Notation-Absolute-Ctx = record { ∣_∣ = len-Ctx }

-- data _⊢_isShape : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Set where
--   zero : ∀{Γ x} -> {A : Γ ⊢Type 𝑆} -> Γ ,[ x ∶ A ] ⊢ zero isShape
--   suc : ∀{Γ x k i₀} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isShape) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isShape

-- data _⊢_isKind_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (k : Γ ⊢Kind) -> Set where
--   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind weak k
--   suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isKind j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isKind (weak j)

-- data _⊢_isName_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (x : Name) -> Set where
--   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isName x
--   suc : ∀{Γ x k i₀ j} -> {A : Γ ⊢Type k} -> (i : Γ ⊢ i₀ isName j) -> Γ ,[ x ∶ A ] ⊢ suc i₀ isName j



{-
data _⊢Shapes where
  [] : ∀{Γ} -> Γ ⊢Shapes
  -- _&_ : ∀{Γ} -> Γ ⊢Shapes -> ∀ i -> {{_ : Γ ⊢ i isKind 𝑆}} -> Γ ⊢Shapes
  _&_ : ∀{Γ i} -> Γ ⊢Shapes -> Γ ⊢ i isKind 𝑆 -> Γ ⊢Shapes

  -- _&_ : ∀{Γ Δ Ε} -- -> {{_ : Γ ⊇ Δ}}
  --       -> Δ ⊢Shapes
  --       -> {A : Ε ⊢Type 𝑆}
  --       -> {x : Name}
  --       -> ∀ i -> {{z : Γ ⊢ i isType A}}
  --       -> {{_ : Γ ⊢ i isName x}}
  --       -- -> {{X : Γ ⊇ (x ∶! A)}}
  --       -- -> let instance _ = to-⊇-⊢Type-Var it it
  --       --    in {{_ : Γ ↤ Δ ∪ (x ∶! A)}}
  --          -- in {{_ : Γ ↤ Δ ∪ (_ ∶! A)}}
  --       -- -> {{_ : Γ ↤ Δ ∪ Ε}}
        -- -> Γ ⊢Shapes

infixl 40 _&_

data _⊢_ where
  -- ℧ : ∀{Γ} -> Γ ⊢ 
  -- 𝒮 : ∀


{-


{-
record _⊢Type_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
  inductive
  pattern
  constructor _⊩_
  field ctx : Ctx
  field {{jni}} : Γ ⊇ ctx
  field typ : ctx ⊢Type k

infixl 50 _⊩_

open _⊢Type_ public

instance
  hasNotation-!:⊢Type : ∀{Γ k} -> hasNotation-! (Γ ⊢Type k) (λ x -> x .ctx ⊢Type k)
  hasNotation-!:⊢Type = record { _! = λ a → a .typ }




data _⊇_ where
  empty : [] ⊇ []
  take : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ ,[ x ∶ Ε ⊩ A ]
  skip : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type k} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> Γ ,[ x ∶ Ε ⊩ A ] ⊇ Δ

isTop-⊇-[] : ∀{Γ} -> Γ ⊇ []
isTop-⊇-[] {[]} = empty
isTop-⊇-[] {Γ ,[ x ∶ Ε ⊩ A ]} = skip {{isTop-⊇-[]}} {{it}}

id-⊇ : ∀{Γ} -> Γ ⊇ Γ
id-⊇ {[]} = empty
id-⊇ {Γ ,[ x ∶ Ε ⊩ A ]} = take {{id-⊇}} {{it}}


pattern _⊩⁺_ Ε A = _⊩_ Ε {{skip}} A

-- module isKindInstances where
--   instance
--     isKind:zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isKind k
--     isKind:zero = _⊢_isKind_.zero

--     isKind:suc : ∀{Γ x k i j} -> {A : Γ ⊢Type k} -> {{_ : Γ ⊢ i isKind j}} -> Γ ,[ x ∶ A ] ⊢ suc i isKind j
--     isKind:suc = suc

module _ where
  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> Γ ⊢Type k -> Set where
  --   zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType (_⊩⁺_ Ε A)
  --   suc : ∀{Γ Ε Η x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (Ε ⊩ A))
  --               -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType (Ε ⊩⁺ A)

  -- data _⊢_isType_ : (Γ : Ctx) -> ∀{i k} -> (Γ ⊢ i isKind k) -> ∀{Ε} -> Ε ⊢Type k -> Set where
  --   zero : ∀{Γ x k} -> {A : Γ ⊢Type k} -> Γ ,[ x ∶ A ] ⊢ zero isType typ A
  --   suc : ∀{Γ Ε x k j i₀} -> {i : Γ ⊢ i₀ isKind k} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (A))
  --               -> {B : Γ ⊢Type j} -> Γ ,[ x ∶ B ] ⊢ (suc i) isType (A)

  data _⊢_isType_ : (Γ : Ctx) -> ∀{k} -> (i : Fin ∣ Γ ∣) -> ∀{Ε} -> Ε ⊢Type k -> Set where
    zero : ∀{Γ Ε x k} -> {{_ : Γ ⊇ Ε}} -> {A : Ε ⊢Type k} -> Γ ,[ x ∶ Ε ⊩ A ] ⊢ zero isType A
    suc : ∀{Γ Ε Η x k j i} -> {A : Ε ⊢Type k} -> (Γ ⊢ i isType (A))
                -> {{_ : Γ ⊇ Η}} -> {B : Η ⊢Type j} -> Γ ,[ x ∶ Η ⊩ B ] ⊢ (suc i) isType A


module _ where
  private instance
    _ = isTop-⊇-[]
    _ = id-⊇
  data _↤_∪_ : (Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> 𝒰₀ where
    emptyleft : ∀{Γ} -> Γ ↤ Γ ∪ []
    emptyright : ∀{Γ} -> Γ ↤ [] ∪ Γ
    takeleft : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) Ε {{take}} {{skip}}
    takeright : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) Δ (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{skip}} {{take}}
    takeboth : ∀{Γ Γ₀ Δ Ε k x} -> {A : Γ₀ ⊢Type k}
     -> {{_ : Γ ⊇ Ε}} -> {{_ : Γ ⊇ Δ}}
     -> {{_ : Ε ⊇ Γ₀}} -> {{_ : Δ ⊇ Γ₀}} -> {{_ : Γ ⊇ Γ₀}}
     -> {{_ : Γ ↤ Δ ∪ Ε}}
     -> _↤_∪_ (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ x ∶ Γ₀ ⊩ A ]) (Ε ,[ x ∶ Γ₀ ⊩ A ]) {{take}} {{take}}

-- record WithVar {Ε k} (A : Ε ⊢Type k) : 𝒰₀ where
--   field name : Name

--   private instance _ = id-⊇

--   getCtxWithVar : Ctx
--   getCtxWithVar = Ε ,[ name ∶ Ε ⊩ A ]

-- open WithVar public

-- instance
--   Notation-Absolute-WithVar : ∀{Ε k} -> {A : Ε ⊢Type k} -> Notation-Absolute (WithVar A) Ctx
--   Notation-Absolute-WithVar = record { ∣_∣ = getCtxWithVar }


_∶!_ : ∀ x -> ∀ {Ε k} (A : Ε ⊢Type k) -> Ctx
_∶!_ x {Ε} A = Ε ,[ x ∶ Ε ⊩ A ]
  where instance _ = id-⊇

-- mergeType : ∀{Γ k} -> (A : Γ ⊢Type k) -> Ctx
-- mergeType (Ε ⊩ A) = (_ ∶! A)

record _⊢Var_∶_ {k} (Γ : Ctx) (i : Fin ∣ Γ ∣) {Ε : Ctx} (A : Ε ⊢Type k) : Set where
  constructor var_by_and_
  inductive
  pattern
  field name : Name
  field isType:var : Γ ⊢ i isType A
  field isName:var : Γ ⊢ i isName name

open _⊢Var_∶_ public

to-⊇-⊢Type : ∀{Γ i k Ε} -> {A : Ε ⊢Type k} -> Γ ⊢ i isType A -> Γ ⊇ Ε
to-⊇-⊢Type zero = skip
to-⊇-⊢Type (suc x) = skip {{to-⊇-⊢Type x}}

module _ where
  instance _ = id-⊇
  to-⊇-⊢Type-Var : ∀{Γ i k x Ε} -> {A : Ε ⊢Type k} -> Γ ⊢ i isType A -> Γ ⊢ i isName x -> Γ ⊇ (Ε ,[ x ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var zero zero = take
  to-⊇-⊢Type-Var (suc x) (suc y) = skip {{to-⊇-⊢Type-Var x y}}

  to-⊇-⊢Type-Var2 : ∀{Γ i k Ε} -> {A : Ε ⊢Type k} -> (z : Γ ⊢Var i ∶ A) -> Γ ⊇ (Ε ,[ name z ∶ Ε ⊩ A ])
  to-⊇-⊢Type-Var2 (var name₁ by P1 and P2) = to-⊇-⊢Type-Var P1 P2



--------------------------------------------------------------------

wk₀-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
wk₀-⊢Type (Ε ⊩ B) = _⊩_ Ε {{skip }} B

-}
-}
-}
-}
