
module KamiD.Dev.2023-11-10.Utils where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Data.List using (List ; [] ; _∷_)
open import Data.String
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-10.Rules

record ∑ₕ {A : 𝒰 𝑖} (B : {{_ : A}} -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make∑ₕ
  field {{fst}} : A
  field snd : B {{fst}}
open ∑ₕ public

pattern _,ₕ_ f s = make∑ₕ {{f}} s
infixr 30 _,ₕ_


len-Ctx : Ctx -> ℕ
len-Ctx [] = 0
len-Ctx (Γ ,[ x ∶ x₁ ]) = suc (len-Ctx Γ)

instance
  _ : Notation-Absolute Ctx ℕ
  _ = record { ∣_∣ = len-Ctx }


getVarCtx : (Γ : Ctx) -> Fin ∣ Γ ∣ -> ∑ Γ ⊇_
getVarCtx (Γ ,[ x ∶ Ε ⊩ A ]) zero = (Ε ,[ x ∶ Ε ⊩ A ]) , take
  where
    instance _ = id-⊇
getVarCtx (Γ ,[ x ∶ x₁ ]) (suc i) =
  let Γ' , P' = getVarCtx Γ i
  in Γ' , skip {{P'}}

findVar : (Γ : Ctx) -> (x : Name) -> Maybe (Fin ∣ Γ ∣)
findVar [] x = nothing
findVar (Γ ,[ y ∶ x₂ ]) x with (Data.String._≟_ x y).does
... | false = map-Maybe suc (findVar Γ x)
... | true = just zero

skip-right : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Δ ⊇ Ε}}
           -> Γ ⊇ Δ ,[ x ∶ Ε ⊩ A ] -> Γ ⊇ Δ
skip-right take = skip {{it}} {{it}}
skip-right skip = skip {{skip-right it}} {{it}}

compose-⊇ : ∀(Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> Γ ⊇ Ε
compose-⊇ .[] .[] Ε ⦃ empty ⦄ ⦃ B ⦄ = B
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ take ⦄ ⦃ take ⦄ =
  let instance _ = compose-⊇ Γ Δ Ε
  in take
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) Ε ⦃ take ⦄ ⦃ skip ⦄ =
  let instance _ = compose-⊇ Γ Δ Ε
  in skip
compose-⊇ .(_ ,[ _ ∶ _ ⊩ _ ]) .[] .[] ⦃ skip ⦄ ⦃ empty ⦄ = it
compose-⊇ (Γ ,[ x₀ ∶ Γ₀ ⊩ A₀ ]) (Δ ,[ x₁ ∶ Γ₁ ⊩ A₁ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ skip ⦄ ⦃ take ⦄ =
  let A : Γ ⊇ (Ε ,[ _ ∶ _ ⊩ _ ])
      A = compose-⊇ Γ (Δ ,[ x₁ ∶ Γ₁ ⊩ A₁ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) {{it}} {{take}}
  in skip {{A}} {{it}}
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) Ε ⦃ skip ⦄ ⦃ skip ⦄ =
  let X = compose-⊇ Γ Δ Ε {{skip-right it}}
  in skip {{X}} {{it}}


joinCtx : ∀(Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}}
          -> ∑ λ Ρ -> ∑ₕ λ {{_ : Γ ⊇ Ρ}} -> ∑ₕ λ {{_ : Ρ ⊇ Δ}} -> ∑ₕ λ {{_ : Ρ ⊇ Ε}} -> Ρ ↤ Δ ∪ Ε
-- joinCtx .(_ ,[ _ ∶ _ ⊩ _ ]) [] Ε ⦃ skip ⦄ ⦃ Y ⦄ = {!!}
-- joinCtx .(_ ,[ x ∶ ctx₁ ⊩ typ₁ ]) (Δ ,[ x ∶ ctx₁ ⊩ typ₁ ]) [] ⦃ take ⦄ ⦃ Y ⦄ = {!!}
-- joinCtx .(_ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ x ∶ x₁ ]) [] ⦃ skip ⦄ ⦃ Y ⦄ = {!!}
-- joinCtx Γ (Δ ,[ x ∶ x₁ ]) (Ε ,[ x₂ ∶ x₃ ]) ⦃ X ⦄ ⦃ Y ⦄ = {!!}


joinCtx .[] .[] Ε ⦃ empty ⦄ ⦃ Y ⦄ = Ε , Y ,ₕ isTop-⊇-[] ,ₕ id-⊇ ,ₕ emptyright
joinCtx (Γ ,[ x ∶ Γ₀ ⊩ A ]) Δ@(_ ,[ .x ∶ .Γ₀ ⊩ .A ]) Ε@[] ⦃ take ⦄ ⦃ skip ⦄ = Δ , take ,ₕ id-⊇ ,ₕ isTop-⊇-[] ,ₕ emptyleft
joinCtx (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ _ ∶ _ ⊩ _ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ take ⦄ ⦃ take ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
      instance _ = compose-⊇ Ρ Ε Γ₀
      instance _ = Ρ↤Δ∪Ε
  in Ρ ,[ x ∶ Γ₀ ⊩ A ] , take ,ₕ take ,ₕ take ,ₕ takeboth

joinCtx (Γ ,[ x ∶ Γ₀ ⊩ A ]) (Δ ,[ .x ∶ .Γ₀ ⊩ .A ]) Ε@(_ ,[ _ ∶ _ ]) ⦃ take ⦄ ⦃ skip ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
      instance _ = compose-⊇ Ρ Δ Γ₀
      instance _ = Ρ↤Δ∪Ε
  in Ρ ,[ x ∶ Γ₀ ⊩ A ] , take ,ₕ take ,ₕ skip ,ₕ takeleft

joinCtx (Γ ,[ x ∶ Γ₀ ⊩ A ]) Δ (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ skip ⦄ ⦃ take ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
      instance _ = compose-⊇ Ρ Ε Γ₀
      instance _ = Ρ↤Δ∪Ε
  in Ρ ,[ x ∶ Γ₀ ⊩ A ] , take ,ₕ skip ,ₕ take ,ₕ takeright
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@[] Ε@[] ⦃ skip ⦄ ⦃ skip ⦄ = [] , isTop-⊇-[] ,ₕ id-⊇ ,ₕ id-⊇ ,ₕ emptyleft
  -- let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  -- in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@[] Ε@(_ ,[ x ∶ x₁ ]) ⦃ skip ⦄ ⦃ skip ⦄ = -- Ε , skip {{skip-right it}} ,ₕ isTop-⊇-[] ,ₕ {!!} ,ₕ {!!}
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@(_ ,[ x ∶ x₁ ]) Ε@[] ⦃ skip ⦄ ⦃ skip ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@(_ ,[ x ∶ x₁ ]) Ε@(_ ,[ x₂ ∶ x₃ ]) ⦃ skip ⦄ ⦃ skip ⦄ =
-- joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ x ∶ x₁ ]) Ε ⦃ skip ⦄ ⦃ skip ⦄ = {!!}
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε



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

