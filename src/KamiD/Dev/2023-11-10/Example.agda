
module KamiD.Dev.2023-11-10.Example where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-10.Rules
open import KamiD.Dev.2023-11-10.Utils

a b c d p q r : String
a = "a"
b = "b"
c = "c"
d = "d"
p = "p"
q = "q"
r = "r"

Pt : ∀{Γ} -> {{_ : Γ ⊇ []}} -> _⊢Type_ Γ 𝑆
Pt = [] ⊩ 𝒮 []

pt : Ctx
pt = [] ,[ a ∶ Pt ]

twopt : Ctx
twopt = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ]

line : Ctx
line = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ] ,[ p ∶ (a ∷ b ∷ []) ?⊩ 𝒮 ({!!} , {!!}) ]

