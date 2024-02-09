
module KamiD.Dev.2023-11-27.Utils.Context where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Data.List using (List ; [] ; _∷_)
open import Data.String
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2023-11-27.Core
open import KamiD.Dev.2023-11-27.Rules


skip-right : ∀{Γ Δ Ε k x} -> {A : Ε ⊢Type! k} -> {{_ : Δ ⊇ Ε}}
           -> Γ ⊇ Δ ,[ x ∶ Ε ⊩ A ] -> Γ ⊇ Δ
skip-right take = skip {{it}} {{it}}
skip-right skip = skip {{skip-right it}} {{it}}

compose-⊇ : ∀(Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Δ ⊇ Ε}} -> Γ ⊇ Ε
compose-⊇ .[] .[] Ε ⦃ empty ⦄ ⦃ B ⦄ = B
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ take ⦄ ⦃ take ⦄ =
  let instance _ = compose-⊇ Γ Δ Ε
  in take
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) Ε@[] ⦃ take ⦄ ⦃ skip ⦄ =
  let instance _ = compose-⊇ Γ Δ Ε
  in skip
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) Ε@(_ ,[ x ∶ x₁ ]) ⦃ take ⦄ ⦃ skip ⦄ =
  let instance _ = compose-⊇ Γ Δ Ε
  in skip
compose-⊇ .(_ ,[ _ ∶ _ ⊩ _ ]) .[] .[] ⦃ skip ⦄ ⦃ empty ⦄ = isTop-⊇-[]
compose-⊇ (Γ ,[ x₀ ∶ Γ₀ ⊩ A₀ ]) (Δ ,[ x₁ ∶ Γ₁ ⊩ A₁ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) ⦃ skip ⦄ ⦃ take ⦄ =
  let A : Γ ⊇ (Ε ,[ _ ∶ _ ⊩ _ ])
      A = compose-⊇ Γ (Δ ,[ x₁ ∶ Γ₁ ⊩ A₁ ]) (Ε ,[ _ ∶ _ ⊩ _ ]) {{it}} {{take}}
  in skip {{A}} {{it}}
compose-⊇ (Γ ,[ _ ∶ _ ⊩ _ ]) (Δ ,[ _ ∶ _ ⊩ _ ]) Ε ⦃ skip ⦄ ⦃ skip ⦄ =
  let X = compose-⊇ Γ Δ Ε {{skip-right it}}
  in skip {{X}} {{it}}


joinCtx : ∀(Γ Δ Ε : Ctx) -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}}
          -> ∑ λ Ρ -> ∑ₕ λ {{_ : Γ ⊇ Ρ}} -> ∑ₕ λ {{_ : Ρ ⊇ Δ}} -> ∑ₕ λ {{_ : Ρ ⊇ Ε}} -> Ρ ↤ Δ ∪ Ε
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
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@[] Ε@(_ ,[ x ∶ x₁ ]) ⦃ skip ⦄ ⦃ skip ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@(_ ,[ x ∶ x₁ ]) Ε@[] ⦃ skip ⦄ ⦃ skip ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε
joinCtx (Γ ,[ _ ∶ _ ⊩ _ ]) Δ@(_ ,[ x ∶ x₁ ]) Ε@(_ ,[ x₂ ∶ x₃ ]) ⦃ skip ⦄ ⦃ skip ⦄ =
  let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
  in Ρ , skip ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε


instance
  -- Derive-↤∪ : ∀{Γ Δ Ε} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}} -> {{P : fst (joinCtx Γ Δ Ε) ≣ Γ}} -> Γ ↤ Δ ∪ Ε
  -- Derive-↤∪ {Γ} {Δ} {Ε} {{P = P}} with joinCtx Γ Δ Ε | P
  -- ... | _ , _ ,ₕ _ ,ₕ _ ,ₕ Γ↤Δ∪Ε  | refl-≣ = Γ↤Δ∪Ε

  Derive-↤∪ : ∀{Γ Δ Ε} -> {{_ : Γ ⊇ Δ}} -> {{_ : Γ ⊇ Ε}}
    -> let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
       in Ρ ↤ Δ ∪ Ε
  Derive-↤∪ {Γ} {Δ} {Ε} =
    let Ρ , _ ,ₕ _ ,ₕ _ ,ₕ Ρ↤Δ∪Ε = joinCtx Γ Δ Ε
    in Ρ↤Δ∪Ε

