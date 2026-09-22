-- This module is an Agda port of the module
-- Quantum.Synthesis.Ring.FixedPrec of the Haskell package newsynth.
--
-- It provides ring instances for Data.Number.FixedPrec. The
-- homomorphisms from ℤ[½], ℤ[√2] and ℤ[1/√2] are computed precisely
-- (without underflow or amplified rounding errors), as in Haskell.
--
-- The Floor instance of Haskell's module is FloorFixedPrec in
-- Data.Number.FixedPrec (floor-of = floor, ceiling-of = ceiling),
-- where it is defined together with the other instances.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.FixedPrec where

open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ ; +_)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (divi ; powℤ ; pow10)

module _ {e : Precision} where

  -- Haskell: fromDyadic x = fromInteger a / 2^n for x = a/2ⁿ. The
  -- result is a⋅10ᵉ/2ⁿ rounded to the closest, which we compute
  -- directly on the scaled integers (same value).
  fromℤ/2^-FixedPrec : ℤ -> ℕ -> FixedPrec e
  fromℤ/2^-FixedPrec a n = F (divi (a Int.* pow10 e) (powℤ 2 n))

  instance
    HalfRingFixedPrec : HalfRing (FixedPrec e)
    HalfRingFixedPrec .half = fromRat 1 2
    HalfRingFixedPrec .fromℤ/2^ = fromℤ/2^-FixedPrec

    -- fromℤ[√2] x y = x + sign(y)⋅√(2y²).
    RootTwoRingFixedPrec : RootTwoRing (FixedPrec e)
    RootTwoRingFixedPrec .roottwo = sqrt 2
    RootTwoRingFixedPrec .fromℤ[√2] x y =
      if 0 ≤ᵇ y then fromℤ x + sqrt (fromℤ (2 * y ^2))
      else fromℤ x - sqrt (fromℤ (2 * y ^2))

    -- fromD[√2] (a/2ⁿ) (b/2ᵐ) = a/2ⁿ + sign(b)⋅√(2b²/2²ᵐ).
    RootHalfRingFixedPrec : RootHalfRing (FixedPrec e)
    RootHalfRingFixedPrec .roothalf = sqrt (fromRat 1 2)
    RootHalfRingFixedPrec .fromD[√2] a n b m =
      if 0 ≤ᵇ b then fromℤ/2^-FixedPrec a n + sqrt (fromℤ/2^-FixedPrec (2 * b ^2) (2 * m))
      else fromℤ/2^-FixedPrec a n - sqrt (fromℤ/2^-FixedPrec (2 * b ^2) (2 * m))

    AdjointFixedPrec : Adjoint (FixedPrec e)
    AdjointFixedPrec .adj x = x

    Adjoint2FixedPrec : Adjoint2 (FixedPrec e)
    Adjoint2FixedPrec .adj2 x = x
