
{-# OPTIONS --rewriting #-}

module KamiD.Dev.2023-11-10.Utils where

open import Agda.Builtin.Equality.Rewrite
open import Agora.Conventions hiding (Σ ; toℕ)
open import Agora.Data.Power.Definition
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_!)
open import Data.List using (List ; [] ; _∷_)
open import Data.String hiding (_≈_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2023-11-10.Core
open import KamiD.Dev.2023-11-10.Rules
open import KamiD.Dev.2023-11-10.Utils.Context

{-# REWRITE +-suc +-zero #-}


----------------------------------------------------
-- Splitting contexts

data _⊢Ctx_ : (Γ : Ctx) -> (m : ℕ) -> 𝒰₀ where
  [] : ∀{Γ} -> Γ ⊢Ctx 0
  [_∶_]∷_ : ∀{Γ k m} -> (x : Name) -> (A : Γ ⊢Type k) -> (Γ ,[ x ∶ A ]) ⊢Ctx m -> Γ ⊢Ctx (suc m)

infixl 60 [_∶_]∷_

_⋆_ : ∀{m} -> (Γ : Ctx) -> (Δ : Γ ⊢Ctx m) -> Ctx
Γ ⋆ [] = Γ
Γ ⋆ [ x ∶ A ]∷ Δ = Γ ,[ x ∶ A ] ⋆ Δ

infixl 30 _⋆_

data _≈_⋆_ : ∀{m} -> (Γ : Ctx) -> (Γ₀ : Ctx)-> (Γ₁ : Γ₀ ⊢Ctx m) -> 𝒰₀ where
  zero : ∀{Γ} -> Γ ≈ Γ ⋆ []
  suc : ∀{Γ Γ₀ m k x} -> {A : Γ₀ ⊢Type k} -> ∀{Γ₁ : Γ₀ ,[ x ∶ A ] ⊢Ctx m} -> Γ ≈ Γ₀ ,[ x ∶ A ] ⋆ Γ₁ -> Γ ≈ Γ₀ ⋆ [ x ∶ A ]∷ Γ₁

id-≅⋆ : ∀{Γ} {Δ : Γ ⊢Ctx m} -> Γ ⋆ Δ ≈ Γ ⋆ Δ
id-≅⋆ {m} {Γ} {[]} = zero
id-≅⋆ {m} {Γ} {[ x ∶ A ]∷ Δ} = suc id-≅⋆

cutCtx : ∀{m} -> (Γ : Ctx) -> (i : Fin (suc ∣ Γ ∣)) -> (Δ : Γ ⊢Ctx m) -> ∑ λ Γ₀ -> ∑ λ (Γ₁ : Γ₀ ⊢Ctx (toℕ i + m)) -> (Γ ⋆ Δ) ≈ Γ₀ ⋆ Γ₁
cutCtx Γ zero Δ = Γ , Δ , id-≅⋆
cutCtx (Γ ,[ x ∶ A ]) (suc i) Δ = cutCtx Γ i ([ x ∶ A ]∷ Δ)

_©ₗ_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Ctx
_©ₗ_ Γ i = fst (cutCtx Γ (suc i) [])

_©ᵣ_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (Γ ©ₗ i) ⊢Ctx _
_©ᵣ_ Γ i = fst $ snd (cutCtx Γ (suc i) [])

infixl 70 _©ₗ_ _©ᵣ_

head-Kind : ∀{Γ} -> (Δ : Γ ⊢Ctx (suc m)) -> Kind
head-Kind ([_∶_]∷_ {k = k} x A Δ) = k

head-⊢Type : ∀{Γ} -> (Δ : Γ ⊢Ctx (suc m)) -> Γ ⊢Type head-Kind Δ
head-⊢Type ([ x ∶ A ]∷ Δ) = A

cast-≈⋆,⊇ : ∀{Γ Γ₀} -> {Γ₁ : Γ₀ ⊢Ctx m} -> Γ ≈ Γ₀ ⋆ Γ₁ -> Γ ⊇ Γ₀
cast-≈⋆,⊇ zero = id-⊇
cast-≈⋆,⊇ (suc X) =
  let instance X = cast-≈⋆,⊇ X
      instance _ = id-⊇
  in compose-⊇ _ _ _ {{X}} {{skip}}

proj-©ₗ : ∀ Γ i -> Γ ⊇ Γ ©ₗ i
proj-©ₗ Γ i =
  let Γ₀ , Γ₁ , P = (cutCtx Γ (suc i) [])
  in cast-≈⋆,⊇ P



--------------------------------------------------------------------
-- various ＠ notation

_＠-Kind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Kind
Γ ＠-Kind i = head-Kind (Γ ©ᵣ i)
-- (_,[_∶_] Γ x {k = k} A) ＠-Kind zero = k
-- (Γ ,[ x ∶ x₁ ]) ＠-Kind suc i = Γ ＠-Kind i

instance
  hasNotation-＠:Kind : hasNotation-＠ Ctx (λ Γ -> Fin ∣ Γ ∣) (λ _ _ -> Kind)
  hasNotation-＠:Kind = record { _＠_ = λ Γ i -> Γ ＠-Kind i }

-- _＠-⊢Varkind_ : ∀(Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Γ ⊢Varkind (Γ ＠ i)
-- -- Γ ＠-⊢Varkind i = 
-- (Γ ,[ x ∶ x₁ ]) ＠-⊢Varkind zero = zero
-- (Γ ,[ x ∶ x₁ ]) ＠-⊢Varkind suc i =
--   let P = (Γ ＠-⊢Varkind i)
--   in suc {!!} -- 


-- instance
--   hasNotation:＠-⊢Varkind : hasNotation-＠ Ctx (λ Γ -> Fin ∣ Γ ∣) (λ Γ i -> Γ ⊢Varkind (Γ ＠ i))
--   hasNotation:＠-⊢Varkind = record { _＠_ = λ Γ i -> Γ ＠-⊢Varkind i }

wk-⊢Type : ∀{Γ Δ j} -> {{_ : Δ ⊇ Γ}} -> (B : Γ ⊢Type j) -> Δ ⊢Type j
wk-⊢Type {Γ = Γ} {Δ = Δ} (Ε ⊩ B) = Ε ⊩ B
  where
    instance _ = compose-⊇ Δ Γ Ε


-- wk-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
-- wk-⊢Type (Ε ⊩ B) = Ε ⊩ B

-- instance
--   hasNotation-wk:⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> hasNotation-wk (Γ ⊢Type j) (const $ Γ ,[ x ∶ A ] ⊢Type j)
--   hasNotation-wk:⊢Type = record { wk = wk-⊢Type }

-- wk-⊢Var : ∀{Γ k j Ε x} -> {i : Γ ⊢Varkind k} {A : Ε ⊢Type! k} {B : Γ ⊢Type j} -> Γ ⊢Var i ∶ A -> Γ ,[ x ∶ B ] ⊢Var (suc i) ∶ A
-- wk-⊢Var (var x by X) = var x by skip {{X}} {{it}}

-- instance
--   hasNotation-wk:⊢Var : ∀{Γ k j Ε x} -> {i : Γ ⊢Varkind k} {A : Ε ⊢Type! k} {B : Γ ⊢Type j} -> hasNotation-wk (Γ ⊢Var i ∶ A) (const $ Γ ,[ x ∶ B ] ⊢Var (suc i) ∶ A)
--   hasNotation-wk:⊢Var = record { wk = λ x -> wk-⊢Var x }

_＠ₗ-⊢Type_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> (Γ ©ₗ i) ⊢Type (Γ ＠ i)
_＠ₗ-⊢Type_ Γ i = head-⊢Type (Γ ©ᵣ i)

_＠-⊢Type_ : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Γ ⊢Type (Γ ＠ i)
_＠-⊢Type_ Γ i = wk-⊢Type (Γ ＠ₗ-⊢Type i)
  where
    instance _ = proj-©ₗ Γ i

-- _＠-⊢Type_ : (Γ : Ctx) -> ∀{k} -> Γ ⊢Varkind k -> Γ ⊢Type k
-- (Γ ,[ x ∶ A ]) ＠-⊢Type zero = wk A
-- (Γ ,[ x ∶ A ]) ＠-⊢Type suc i = wk (Γ ＠-⊢Type i)

instance
  hasNotation-＠:⊢Type : hasNotation-＠ Ctx (λ Γ -> Fin ∣ Γ ∣) (λ Γ i -> Γ ⊢Type (Γ ＠ i))
  hasNotation-＠:⊢Type = record { _＠_ = λ Γ i -> Γ ＠-⊢Type i }


{-
_＠-⊢Var_ : ∀{k} -> ∀(Γ) -> (i : Γ ⊢Varkind k) -> Γ ⊢Var i ∶ (Γ ＠ i)!
_＠-⊢Var_ (Γ ,[ x ∶ Ε ⊩ A ]) zero = var x by (take {{it}} {{id-⊇}})
_＠-⊢Var_ (Γ ,[ x ∶ x₁ ]) (suc i) = wk (Γ ＠-⊢Var i)

instance
  hasNotation-＠:⊢Var : ∀{k} -> hasNotation-＠ Ctx (λ Γ -> Γ ⊢Varkind k) (λ Γ i -> Γ ⊢Var i ∶ (Γ ＠ i)!)
  hasNotation-＠:⊢Var = record { _＠_ = λ Γ i -> Γ ＠-⊢Var i }

instance
  Derive:⊢Var : ∀{k Γ} -> {i : Γ ⊢Varkind k} -> Γ ⊢Var i ∶ (Γ ＠ i)!
  Derive:⊢Var {k} {Γ} {i} = Γ ＠ i


findVar : (Γ : Ctx) -> (x : Name) -> Maybe (Fin ∣ Γ ∣)
findVar [] x = nothing
findVar (Γ ,[ y ∶ x₂ ]) x with (Data.String._≟_ x y).does
... | false = map-Maybe suc (findVar Γ x)
... | true = just zero

varByIndex : (Γ : Ctx) -> Fin ∣ Γ ∣ -> ∑ (Γ ⊢Varkind_)
varByIndex (Γ ,[ x ∶ x₁ ]) zero = (_ , zero)
varByIndex (Γ ,[ x ∶ x₁ ]) (suc i) =
  let (k , i) = varByIndex Γ i
  in (k , suc i)

varByName : (Γ : Ctx) -> Name -> Maybe (∑ (Γ ⊢Varkind_))
varByName Γ x = map-Maybe (varByIndex Γ) (findVar Γ x)




‵ : ∀{k} -> {Γ : Ctx} -> (x : Name)
     -> {{_ : map-Maybe fst (varByName Γ x) ≣ just k }}
     -> Γ ⊢Varkind k
‵ {Γ = Γ} x {{P}} with varByName Γ x | P
... | just (k , i) | refl-≣ = i




----------------------------------------------------
-- Derivation for ⊇

-- Derive:⊇ : ∀{Γ Δ} -> Γ ⊇ Δ





----------------------------------------------------
-- Old Var Ctxs





-- getVarCtx' : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> Γ ≈ ((Γ ©ₗ (suc i)) ,[ {!!} ∶ {!!} ]) ⋆ {!!}
-- getVarCtx' = {!!}

-- getVarCtx' : (Γ : Ctx) -> (i : Fin ∣ Γ ∣) -> ∑ λ Γ₀ -> ∑ λ x -> ∑ λ (A : Γ₀ ⊢Type (Γ ＠ i)) -> ∑ λ Γ₁ -> Γ ≈ (Γ₀ ,[ x ∶ A ]) ⋆ Γ₁
-- getVarCtx' = {!!}





-- _©ᵣ_ : (Γ)





data _⋖_ : (Γ Δ : Ctx) -> 𝒰₀ where
  id-⋖ : ∀{Γ} -> Γ ⋖ Γ
  _,[_∶_] : ∀{Γ x k} -> (A : Γ ⊢Type k) -> Γ ⋖ Γ ,[ x ∶ A ]


record Result-cutCtx {Γ k} (i : Γ ⊢Varkind k) : 𝒰₀ where
  field prefix : Ctx
  field isPrefix : prefix ⋖ Γ
  field varctx : Ctx
  field hasvarctx : prefix ⊇ varctx
  field vartype : varctx ⊢Type! k
  -- field subvarctx : prefix ⊢Var i ∶ 

open Result-cutCtx public

-- cutCtx : ∀{Γ k} -> (i : Γ ⊢Varkind k) -> Result-cutCtx i
-- cutCtx {Γ ,[ x ∶ Ε ⊩ A ]} zero = record
--   { prefix = Γ
--   ; isPrefix = {!!}
--   ; varctx = Ε
--   ; hasvarctx = it
--   ; vartype = A
--   }
-- cutCtx {Γ ,[ x ∶ x₁ ]} (suc i) = {!!}


getVarCtx : (Γ : Ctx) -> Fin ∣ Γ ∣ -> ∑ Γ ⊇_
getVarCtx (Γ ,[ x ∶ Ε ⊩ A ]) zero = (Ε ,[ x ∶ Ε ⊩ A ]) , take
  where
    instance _ = id-⊇
getVarCtx (Γ ,[ x ∶ x₁ ]) (suc i) =
  let Γ' , P' = getVarCtx Γ i
  in Γ' , skip {{P'}}




getVarsCtx : (Γ : Ctx) -> List Name -> Maybe (∑ Γ ⊇_)
getVarsCtx Γ [] = just ([] , it)
  where instance _ = isTop-⊇-[]
getVarsCtx Γ (x ∷ xs) = do
  i <- findVar Γ x
  let x = cutCtx Γ (suc i) []
  {! !}


  -- Δ₀ , P <- map-Maybe (getVarCtx Γ) (findVar Γ x)
  -- {!!}
  -- Δ₁ , Q <- getVarsCtx Γ xs
  -- let instance _ = P
  -- let instance _ = Q
  -- let Δ , _ ,ₕ _ ,ₕ _ ,ₕ _ = joinCtx Γ Δ₀ Δ₁
  -- just (Δ , it)

  where _>>=_ = bind-Maybe


_?⊩_ : ∀{Γ Δ k} -> {X : Γ ⊇ Δ} -> (xs : List Name) -> {{_ : getVarsCtx Γ xs ≣ just (Δ , X)}} -> Δ ⊢Type! k -> Γ ⊢Type k
_?⊩_ {Δ = Δ} {X = X} xs tp =
  let instance _ = X
  in Δ ⊩ tp


-}

