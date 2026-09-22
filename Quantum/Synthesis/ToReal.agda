-- This module is an Agda port of the module Quantum.Synthesis.ToReal
-- of the Haskell package newsynth.
--
-- It provides a type class of things that can be converted to
-- arbitrary precision real numbers.
--
-- In Haskell, Quantum.Synthesis.SymReal defines a second, identical
-- copy of the class ToReal (with extra instances for SymReal and
-- String) and of dynamic_fixedprec. In the Agda port there is only
-- this class; Quantum.Synthesis.SymReal adds its instances to it and
-- re-exports this module.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.ToReal where

open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_,_)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (toℕ⁺)
open import Quantum.Synthesis.ArcTan2

-- ----------------------------------------------------------------------
-- * Conversion to real number types

-- The type classes a real number type r must have to be a target of
-- to-real. Haskell requires (Floating r, ArcTan2 r); the framework
-- splits Haskell's Floating into Ring, Fractional and Floating,
-- and abs/signum need DecOrd.
record RealTarget (R : Set) : Set₁ where
  field
    {{rt-ring}} : Ring R
    {{rt-decord}} : DecOrd R
    {{rt-fractional}} : Fractional R
    {{rt-floating}} : Floating R
    {{rt-arctan2}} : ArcTan2 R

instance
  RealTargetFloat : RealTarget Float
  RealTargetFloat = record {}

  RealTargetFixedPrec : {e : Precision} -> RealTarget (FixedPrec e)
  RealTargetFixedPrec = record {}

-- A type class for things that can be converted to a real number at
-- arbitrary precision.
record ToReal (A : Set) : Set₁ where
  field
    to-real : {R : Set} {{_ : RealTarget R}} -> A -> R
open ToReal {{...}} public

instance
  ToRealℚ : ToReal ℚ
  ToRealℚ .to-real q = fromℚ q

  ToRealℤ : ToReal ℤ
  ToRealℤ .to-real n = fromℤ n

  -- Haskell's Int instance.
  ToRealℕ : ToReal ℕ
  ToRealℕ .to-real n = fromℕ n

  -- Haskell's Double and Float instances: fromRational . toRational.
  ToRealFloat : ToReal Float
  ToRealFloat .to-real x = fromℚ (toℚ-Float x)

  ToRealFixedPrec : {e : Precision} -> ToReal (FixedPrec e)
  ToRealFixedPrec .to-real x = fromℚ (toℚ x)

-- ----------------------------------------------------------------------
-- ** Dynamic conversion to FixedPrec

-- In Haskell, the precision of FixedPrec is a type, so a function
-- converting to a precision given by a term needs a trick
-- (dynamic_fixedprec). In Agda the precision is a term, so
--
--   dynamic-fixedprec d f x = f (to-fixedprec d x)
--
-- where d digits (d ≤ 0 means 0 digits) are used.
to-fixedprec : {A : Set} {{_ : ToReal A}} -> (e : Precision) -> A -> FixedPrec e
to-fixedprec e x = to-real x

dynamic-fixedprec : {A B : Set} {{_ : ToReal A}} -> ℤ -> ({e : Precision} -> FixedPrec e -> B) -> A -> B
dynamic-fixedprec d f x = f (to-fixedprec (toℕ⁺ d) x)

-- Like dynamic-fixedprec, but take two real number arguments:
--
--   dynamic-fixedprec2 d f x y = f (to-fixedprec d x) (to-fixedprec d y).
dynamic-fixedprec2 : {A A' B : Set} {{_ : ToReal A}} {{_ : ToReal A'}} -> ℤ -> ({e : Precision} -> FixedPrec e -> FixedPrec e -> B) -> A -> A' -> B
dynamic-fixedprec2 d f x y = f (to-fixedprec (toℕ⁺ d) x) (to-fixedprec (toℕ⁺ d) y)
