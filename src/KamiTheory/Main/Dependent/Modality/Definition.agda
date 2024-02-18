
{-# OPTIONS --allow-unsolved-metas #-}

module KamiTheory.Main.Dependent.Modality.Definition where

open import Agora.Conventions


------------------------------------------------------------------------
-- The new modality system




-- -- in general, modalities are concatenations
-- -- of base modalities
-- data ModeHom P : (m n : Mode) -> Set where
--   id : ∀{m} -> ModeHom P m m
--   _⨾_ : ∀{m n o} -> BaseModeHom P m n  -> ModeHom P n o -> ModeHom P m o





---------------------------------------------
-- mode transformations

open import Agora.Order.Preorder
open import Agora.Order.Lattice


module _ {P : 𝒰 _} {{_ : Preorder (ℓ₀ , ℓ₀ , ℓ₀) on P }} where

  private variable
    U V : P



  module _ {{_ : isDecidablePreorder ′ P ′}} where

    derive-ModeTrans : {m n : Mode} {v : Visibility} (μs ηs : ModeHom P m n)
                      -> Maybe (ModeTrans μs ηs v)
    derive-ModeTrans = {!!}
    -- derive-ModeTrans id id = yes id
    -- derive-ModeTrans id (x ⨾ q) = nothing
    -- derive-ModeTrans (x ⨾ p) id = nothing
    -- derive-ModeTrans (`＠` U ⨾ p) (`＠` V ⨾ q) with decide-≤ U V
    -- ... | no x = nothing
    -- ... | yes ϕ with derive-ModeTrans p q
    -- ... | no x = nothing
    -- ... | yes ξ = yes (base (narrow ϕ) ⨾ ξ)
    -- derive-ModeTrans (`[]` ⨾ p) (`[]` ⨾ q) with derive-ModeTrans p q
    -- ... | nothing = nothing
    -- ... | yes ξ = yes (id ⨾ ξ)



