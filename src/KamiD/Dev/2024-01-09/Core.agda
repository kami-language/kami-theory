{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-09.Core where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat hiding (_!)
open import Data.List using (List ; [] ; _∷_)
open import Data.String
open import Relation.Nullary.Decidable.Core


record ∑ₕ {A : 𝒰 𝑖} (B : {{_ : A}} -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make∑ₕ
  field {{fst}} : A
  field snd : B {{fst}}
open ∑ₕ public

pattern _,ₕ_ f s = make∑ₕ {{f}} s
infixr 30 _,ₕ_

record hasNotation-! (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field _! : (a : A) -> B a
  infixl 200 _!

open hasNotation-! {{...}} public

record hasNotation-wk (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field wk : (a : A) -> B a

open hasNotation-wk {{...}} public

record hasNotation-𝕠 (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field 𝕠 : (a : A) -> B a

open hasNotation-𝕠 {{...}} public

record hasNotation-＠ (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) (C : ∀(a : A) -> B a -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field _＠_ : (a : A) -> (b : B a) -> C a b

open hasNotation-＠ {{...}} public


record hasNotation-refine (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field refine : (a : A) -> B a

open hasNotation-refine {{...}} public

record hasNotation-⋆ (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) (C : ∀(a : A) -> B a -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field _⋆_ : (a : A) -> (b : B a) -> C a b

  infixl 40 _⋆_

open hasNotation-⋆ {{...}} public


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
