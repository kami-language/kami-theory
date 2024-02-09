
{-# OPTIONS --cubical --rewriting #-}

module KamiTheory.Dev.2023-12-13.RewriteTest where

-- open import Agora.Conventions hiding (Σ ; Lift)
-- open import Agora.Data.Power.Definition
-- open import Data.Fin
-- open import Data.Nat hiding (_!)
-- open import Relation.Nullary.Decidable.Core

open import Cubical.Core.Primitives
-- open import KamiTheory.Dev.2023-12-05.Core

{-# BUILTIN REWRITE _≡_ #-}

data TEST : Set where
  aa bb : TEST

postulate
  cc : aa ≡ bb

{-# REWRITE cc #-}


