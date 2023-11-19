
{-# OPTIONS --rewriting #-}

module KamiD.Dev.2023-11-19.Example where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-19.Core
open import KamiD.Dev.2023-11-19.Rules
open import KamiD.Dev.2023-11-19.Utils2
-- open import KamiD.Dev.2023-11-19.Utils.Context

-- instance _ = Derive:⊇

-- a b c d p q r : String
-- a = "a"
-- b = "b"
-- c = "c"
-- d = "d"
-- p = "p"
-- q = "q"
-- r = "r"

a b c d p q r : ℕ
a = 1
b = 2
c = 3
d = 4
p = 5
q = 6
r = 7

-- Pt : ∀{Γ} -> _⊢Type_ Γ 𝑆
-- Pt = [] ⊩ 𝒮 []

pattern Pt = 𝒮 []

pt : Ctx
pt = [] ,[ a ∶ Pt ]

twopt : Ctx
twopt = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ]

line : Ctx
line = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ] ,[ p ∶ 𝒮 ([] & {!!} & {!!}) ]

Nat : [] ⊢Type (⩝ a ∶ Pt , {!!})
Nat = ⩝ a ∶ Pt , {!!}





