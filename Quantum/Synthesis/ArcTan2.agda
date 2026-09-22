-- This module is an Agda port of the module Quantum.Synthesis.ArcTan2
-- of the Haskell package newsynth.
--
-- It provides a replacement for Haskell's atan2. The problem is that
-- Haskell's standard implementation of atan2 depends on the RealFloat
-- class, which limits its applicability. So we provide a new ArcTan2
-- class with an arctan2 function.
--
-- Unlike Haskell's atan2, the arctan2 function may not take signed
-- zeros and signed infinities into account. But it works at
-- fixed-precision types such as FixedPrec.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.ArcTan2 where

open import Data.Bool.Base using (_∧_ ; if_then_else_)
open import Data.Float.Base as Float using (Float)

open import Instances
open import Literals
open import Data.Number.FixedPrec

-- ----------------------------------------------------------------------
-- * The arctan2 function

-- A replacement for Haskell's atan2: arctan2 y x is the angle of the
-- point (x, y), in (-π, π].
record ArcTan2 (A : Set) : Set where
  field
    arctan2 : A -> A -> A
open ArcTan2 {{...}} public

instance
  -- Haskell's Double (and Float) instance: atan2.
  ArcTan2Float : ArcTan2 Float
  ArcTan2Float .arctan2 = Float.atan2

  ArcTan2FixedPrec : {e : Precision} -> ArcTan2 (FixedPrec e)
  ArcTan2FixedPrec .arctan2 y x =
    if (x == 0) ∧ (y == 0) then 0
    else if abs y ≤ᵇ x then atan (y / x)
    else if abs x ≤ᵇ y then pi / 2 - atan (x / y)
    else if abs x ≤ᵇ - y then - (pi / 2) - atan (x / y)
    else if 0 ≤ᵇ y then pi + atan (y / x)
    else - pi + atan (y / x)
