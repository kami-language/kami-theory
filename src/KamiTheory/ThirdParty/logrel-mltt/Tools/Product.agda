-- SPDX-FileCopyrightText: 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--
-- SPDX-License-Identifier: MIT

-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

{-# OPTIONS --without-K --safe #-}

module KamiTheory.ThirdParty.logrel-mltt.Tools.Product where

open import Data.Product public using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂)
