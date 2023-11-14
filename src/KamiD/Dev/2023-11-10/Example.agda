
{-# OPTIONS --rewriting #-}

module KamiD.Dev.2023-11-10.Example where

open import Agora.Conventions hiding (Σ)
open import Agora.Data.Power.Definition
open import Data.Fin
open import Data.Nat
open import Relation.Nullary.Decidable.Core
open import KamiD.Dev.2023-11-10.Core
open import KamiD.Dev.2023-11-10.Rules
open import KamiD.Dev.2023-11-10.Utils
open import KamiD.Dev.2023-11-10.Utils.Context

instance _ = Derive:⊇

a b c d p q r : String
a = "a"
b = "b"
c = "c"
d = "d"
p = "p"
q = "q"
r = "r"

Pt : ∀{Γ} -> _⊢Type_ Γ 𝑆
Pt = [] ⊩ 𝒮 []

pt : Ctx
pt = [] ,[ a ∶ Pt ]

twopt : Ctx
twopt = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ]

line : Ctx
line = [] ,[ a ∶ Pt ] ,[ b ∶ Pt ] ,[ p ∶ (a ∷ b ∷ []) ?⊩ 𝒮 ([] & ‵ a & ‵ b) ]



-- 2023-11-14
-- As next steps we need to do:
--  - Think about how situations should be dealt with where a single
--    channel (at a point) is used by more than two higher processes.
--    Because composition (gluing) along channels makes sense as long as
--    there is a +A and a -A. But how can we deal with more than two?
--    Crazy thought: do we want that the "sum" has to be zero??
--  - Putting datatypes into the context, e.g. the natural numbers.



