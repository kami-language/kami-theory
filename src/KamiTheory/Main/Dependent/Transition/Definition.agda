
module KamiTheory.Main.Dependent.Transition.Definition where

open import Agora.Conventions
open import KamiTheory.Main.Dependent.Modality.Definition


-- We have some kind of semiring structure with operators
--  - `_≫_` (composition)
--  - `_∥_` (parallel computation)
--
-- With, e.g., distributivity:
--
-- a ≫ (b ∥ c) ＝ (a ≫ b) ∥ (a ≫ c)
--
-- But currently we ignore parallel computatio and only give
-- the composition structure.
--

-- We generate the space of transitions from a type of basic
-- transitions, T. It is currently modelled by lists.

open import Data.List using (_++_)
Transitions : (T : Set) -> Set
Transitions T = List T

private variable
  T : Set

_≫-Transitions_ : List T -> List T -> List T
_≫-Transitions_ = _++_


