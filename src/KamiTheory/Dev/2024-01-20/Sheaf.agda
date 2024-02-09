
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2024-01-20.Sheaf where

open import Agora.Conventions hiding (Σ ; Lift ; k)

open import KamiTheory.Dev.2024-01-20.Core hiding (_＠_)
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base
open import KamiTheory.Dev.2024-01-20.UniqueSortedList
open import KamiTheory.Dev.2024-01-20.StrictOrder.Instances.List
open import KamiTheory.Dev.2024-01-20.Basics
open import KamiTheory.Dev.2024-01-20.Open

open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition



module _ {X : 𝒰 _} {{_ : X is Lattice 𝑖}} where
  record isSheaf {𝑗} (F : X -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field _↷_ : ∀{U V : X} -> (ϕ : U ≤ V) -> F V -> F U
    field id-↷ : ∀{U} -> ∀{x : F U} -> refl-≤ ↷ x ≡ x
    field comp-↷ : ∀{U V W} -> {ϕ : U ≤ V} {ψ : V ≤ W} -> {x : F W} -> (ϕ ⟡ ψ) ↷ x ≡ ϕ ↷ (ψ ↷ x)
    field glue : ∀{U V} -> (x : F U) -> (y : F V) -> π₀-∧ ↷ x ≡ π₁-∧ ↷ y -> F (U ∨ V)
    field glue-π₀ : ∀{U V} -> (x : F U) -> (y : F V) -> (p : π₀-∧ ↷ x ≡ π₁-∧ ↷ y) -> ι₀-∨ ↷ (glue x y p) ≡ x
    field glue-π₁ : ∀{U V} -> (x : F U) -> (y : F V) -> (p : π₀-∧ ↷ x ≡ π₁-∧ ↷ y) -> ι₁-∨ ↷ (glue x y p) ≡ y

    infixr 30 _↷_

  open isSheaf {{...}} public


  instance
    isSheaf:const : ∀{A : 𝒰 𝑗} -> isSheaf (const A)
    isSheaf:const = record
      { _↷_ = λ _ x -> x
      ; id-↷ = refl-≡
      ; comp-↷ = refl-≡
      ; glue = λ x _ _ -> x
      ; glue-π₀ = λ x y p -> refl-≡
      ; glue-π₁ = λ {x y refl-≡ -> refl-≡}
      }


  restr : (X -> 𝒰 𝑗) -> X -> (X -> 𝒰 _)
  restr F U V = ¬ (U ∧ V ≤ ⊥) -> F V

  instance
    isSheaf:restr : ∀ {F U} -> {{_ : isSheaf {𝑗} F}} -> isSheaf (restr F U)
    isSheaf:restr {F = F} {U} = record
      { _↷_ = λ ϕ f P -> ϕ ↷ f λ ψ⊥ -> P (map-∧ refl-≤ ϕ ⟡ ψ⊥)
      ; id-↷ = {!!}
      ; comp-↷ = {!!}
      ; glue = λ f g p P -> glue (f (λ ψ⊥ -> P ({!!}))) {!!} {!!}
  -- map-∧ refl-≤ {!!} ⟡ ψ⊥
      ; glue-π₀ = {!!}
      ; glue-π₁ = {!!}
      }

  instance
    isSheaf:× : ∀ {F G} -> {{_ : isSheaf {𝑗} F}} {{_ : isSheaf {𝑘} G}} -> isSheaf (λ x -> F x ×-𝒰 G x)
    isSheaf:× = record
                 { _↷_ = λ ϕ (a , b) -> ϕ ↷ a , ϕ ↷ b
                 ; id-↷ = {!!}
                 ; comp-↷ = {!!}
                 ; glue = {!!}
                 ; glue-π₀ = {!!}
                 ; glue-π₁ = {!!}
                 }


Sheaf : Lattice 𝑖 -> ∀ 𝑗 -> _
Sheaf X 𝑗 = (⟨ X ⟩ -> 𝒰 𝑗) :& isSheaf

macro
  Restr : ∀{L : Lattice 𝑖} -> Sheaf L 𝑗 -> ⟨ L ⟩ -> _
  Restr F U = #structureOn (restr ⟨ F ⟩ U)

macro
  Const : ∀{B : 𝒰 𝑘} (A : 𝒰 𝑗) -> _
  Const {B = B} A = #structureOn (const {A = B} A)

_×-Sheaf_ : ∀{X : Lattice 𝑖} -> Sheaf X 𝑗 -> Sheaf X 𝑘 -> Sheaf X _
_×-Sheaf_ F G = (λ x -> ⟨ F ⟩ x ×-𝒰 ⟨ G ⟩ x) since it


