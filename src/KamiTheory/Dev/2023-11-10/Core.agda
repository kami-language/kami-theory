
module KamiD.Dev.2023-11-10.Core where

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

record hasNotation-＠ (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) (C : ∀(a : A) -> B a -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field _＠_ : (a : A) -> (b : B a) -> C a b

open hasNotation-＠ {{...}} public


record hasNotation-refine (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field refine : (a : A) -> B a

open hasNotation-refine {{...}} public

