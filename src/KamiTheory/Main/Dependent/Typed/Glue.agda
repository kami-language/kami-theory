
module KamiTheory.Main.Dependent.Typed.Glue where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.RestrictionRelation



module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}}
       {{_ : isDecidablePreorder ′ P ′}}
       {{_ : hasDecidableEquality P}} where

  private variable
    W : P
    bs : List ℕ

  glue-GenTs : ∀{t₀ t₁ u : GenTs (Term P) n bs}
            -> t₀ [ W ]⤇s u -> t₁ [ W ]⤇s u -> GenTs (Term P) n bs
  glue-Term : ∀{t₀ t₁ u : Term P n}
            -> t₀ [ W ]⤇ u -> t₁ [ W ]⤇ u -> Term P n

  glue-GenTs [] [] = []
  glue-GenTs (t ∷ ts) (u ∷ us) = glue-Term t u ∷ glue-GenTs ts us

  glue-Term (var v) (var .v) = var v
  glue-Term (constₜ c) (constₜ .c) = constₜ c
  glue-Term (gen k kp ts) (gen .k kp' us) = gen k (glue-GenTs ts us)
  glue-Term (gen k kp ts) (gen-loc-keep U t ϕ α) = ⊥-elim (↯-isNot-𝓀-loc kp)
  glue-Term (gen k kp ts) (gen-loc-remove U t x₂) = loc U t
  glue-Term (gen-loc-keep U t ϕ α) (gen k kp x₂) = ⊥-elim (↯-isNot-𝓀-loc kp)
  glue-Term (gen-loc-keep U t ϕ α) (gen-loc-keep .U s ψ β) = loc U (glue-Term α β)
  glue-Term (gen-loc-remove U t ¬ϕ) (gen k kp x₂) = loc U t
  glue-Term (gen-loc-remove U t ¬ϕ) (gen-loc-remove V s ¬ψ) = loc U t -- This case should be impossible for well-typed terms... Here we just take the term of one side



