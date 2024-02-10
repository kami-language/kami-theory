
module KamiTheory.Main.Dependent.Typed.Restriction where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Typed.Instances

open import KamiTheory.Data.Open.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Order.StrictOrder.Base


-- data isLoc


