
module KamiD.Dev.2023-11-10.Utils where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Data.List using (List ; [] ; _∷_)
open import Data.String
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2023-11-10.Core
open import KamiD.Dev.2023-11-10.Rules
open import KamiD.Dev.2023-11-10.Utils.Context


wk-⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> (B : Γ ⊢Type j) -> Γ ,[ x ∶ A ] ⊢Type j
wk-⊢Type (Ε ⊩ B) = Ε ⊩ B

instance
  hasNotation-wk:⊢Type : ∀{Γ k j x} -> {A : Γ ⊢Type k} -> hasNotation-wk (Γ ⊢Type j) (const $ Γ ,[ x ∶ A ] ⊢Type j)
  hasNotation-wk:⊢Type = record { wk = wk-⊢Type }

wk-⊢Var : ∀{Γ k j Ε x} -> {i : Γ ⊢Varkind k} {A : Ε ⊢Type! k} {B : Γ ⊢Type j} -> Γ ⊢Var i ∶ A -> Γ ,[ x ∶ B ] ⊢Var (suc i) ∶ A
wk-⊢Var (var x by X) = var x by skip {{X}} {{it}}

instance
  hasNotation-wk:⊢Var : ∀{Γ k j Ε x} -> {i : Γ ⊢Varkind k} {A : Ε ⊢Type! k} {B : Γ ⊢Type j} -> hasNotation-wk (Γ ⊢Var i ∶ A) (const $ Γ ,[ x ∶ B ] ⊢Var (suc i) ∶ A)
  hasNotation-wk:⊢Var = record { wk = λ x -> wk-⊢Var x }

_＠-⊢Type_ : (Γ : Ctx) -> ∀{k} -> Γ ⊢Varkind k -> Γ ⊢Type k
(Γ ,[ x ∶ A ]) ＠-⊢Type zero = wk A
(Γ ,[ x ∶ A ]) ＠-⊢Type suc i = wk (Γ ＠-⊢Type i)

instance
  hasNotation-＠:⊢Type : ∀{k} -> hasNotation-＠ Ctx (λ Γ -> Γ ⊢Varkind k) (λ Γ i -> Γ ⊢Type k)
  hasNotation-＠:⊢Type = record { _＠_ = λ Γ i -> Γ ＠-⊢Type i }


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
  Δ₀ , P <- map-Maybe (getVarCtx Γ) (findVar Γ x)
  Δ₁ , Q <- getVarsCtx Γ xs
  let instance _ = P
  let instance _ = Q
  let Δ , _ ,ₕ _ ,ₕ _ ,ₕ _ = joinCtx Γ Δ₀ Δ₁
  just (Δ , it)

  where _>>=_ = bind-Maybe


_?⊩_ : ∀{Γ Δ k} -> {X : Γ ⊇ Δ} -> (xs : List Name) -> {{_ : getVarsCtx Γ xs ≣ just (Δ , X)}} -> Δ ⊢Type! k -> Γ ⊢Type k
_?⊩_ {Δ = Δ} {X = X} xs tp =
  let instance _ = X
  in Δ ⊩ tp




