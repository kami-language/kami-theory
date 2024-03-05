-- SPDX-FileCopyrightText: 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--
-- SPDX-License-Identifier: MIT

-- The unit type; also used as proposition ``Truth''.

{-# OPTIONS --without-K --safe #-}

module KamiTheory.ThirdParty.logrel-mltt.Tools.Unit where

-- We reexport Agda's built-in unit type.

open import Agda.Builtin.Unit public using (⊤; tt)
