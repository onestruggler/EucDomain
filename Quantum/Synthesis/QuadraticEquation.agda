-- This module is an Agda port of the module
-- Quantum.Synthesis.QuadraticEquation of the Haskell package
-- newsynth.
--
-- It provides a type class Quadratic, for solving quadratic
-- equations.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.QuadraticEquation where

open import Data.Bool.Base using (Bool ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (divide ; pow10 ; intsqrt)
open import Quantum.Synthesis.ToReal

-- This type class provides a primitive method for solving quadratic
-- equations. For many floating-point or fixed-precision
-- representations of real numbers, using the usual "quadratic
-- formula" results in a significant loss of precision. Instances of
-- the Quadratic class should provide an efficient high-precision
-- method when possible.
record Quadratic (T A : Set) : Set where
  field
    -- quadratic a b c: solve the quadratic equation ax² + bx + c = 0.
    -- Return the pair of solutions (x₁, x₂) with x₁ ≤ x₂, or nothing
    -- if no solution exists. Note that the coefficients a, b, and c
    -- can be taken to be of an exact type; therefore instances have
    -- the opportunity to work with infinite precision.
    quadratic : T -> T -> T -> Maybe (A × A)
open Quadratic {{...}} public

-- ----------------------------------------------------------------------
-- FixedPrec instance

module _ {T : Set} {{_ : Ring T}} {{_ : Fractional T}} {{_ : Floor T}} {{_ : DecOrd T}} where
  open LiteralsFor T

  -- Given b, c ∈ T (e.g. ℚ[√2]), consider the quadratic function
  -- f(t) = t² + bt + c.
  --
  -- * If f(t) = 0 has no real solutions, return nothing.
  --
  -- * If f(t) = 0 has real solutions t₀ ≤ t₁, return t'₀, t'₁ ∈ ℤ
  --   such that t'₀ ≤ t₀, t₁ ≤ t'₁, and |t'₀ - t₀|, |t'₁ - t₁| ≤ 1.
  int-quadratic : T -> T -> Maybe (ℤ × ℤ)
  --
  -- (Performance: where-bound values are not shared in compiled Agda
  -- code, so the intermediate values radix, tm, ⌊√radix⌋, t'₀, t'₁
  -- and x' are passed as arguments of helper functions.)
  int-quadratic b c = with-radix (divide (b ^2) 4 - c)
    where
      f : T -> T
      f x = x ^2 + b * x + c

      solutions : T -> ℤ -> Maybe (ℤ × ℤ)
      solutions tm rootradix' = just (t0 (ceiling-of tm - rootradix') , t1 (floor-of tm + rootradix'))
        where
          is-solution1 is-solution0 : ℤ -> Bool
          is-solution1 x = test (fromℤ x)
            where
              test : T -> Bool
              test x' = (0 ≤ᵇ f x') ∧ ((f (x' - 1) <ᵇ 0) ∨ (x' - 1 <ᵇ tm))
          is-solution0 x = test (fromℤ x)
            where
              test : T -> Bool
              test x' = (0 ≤ᵇ f x') ∧ ((f (x' + 1) <ᵇ 0) ∨ (tm <ᵇ x' - 1))
          t0 t1 : ℤ -> ℤ
          t1 t1' = if is-solution1 (t1' + 2) then t1' + 2
                   else if is-solution1 (t1' + 1) then t1' + 1
                   else t1'
          t0 t0' = if is-solution0 (t0' - 2) then t0' - 2
                   else if is-solution0 (t0' - 1) then t0' - 1
                   else t0'

      with-radix : T -> Maybe (ℤ × ℤ)
      with-radix radix =
        if radix <ᵇ 0 then nothing else solutions (divide (- b) 2) (intsqrt (floor-of radix))

  -- Given a, b, c ∈ T with a > 0, consider the quadratic function
  -- f(t) = at² + bt + c.
  --
  -- * If f(t) = 0 has no real solutions, return nothing.
  --
  -- * If f(t) = 0 has real solutions t₀ ≤ t₁, return (t'₀, t'₁) such
  --   that t'₀ ≤ t₀, t₁ ≤ t'₁, and |t'₀ - t₀|, |t'₁ - t₁| ≤ 10⁻ᵈ,
  --   where d is the precision of the fixed-point real number type.
  --
  -- Haskell computes prec' = 10^d in T and prec = 10^d in FixedPrec;
  -- we use fromℤ (10ᵈ), which is the same value.
  quadratic-fixedprec : {e : Precision} -> T -> T -> T -> Maybe (FixedPrec e × FixedPrec e)
  -- (prec' and prec are passed as arguments, since where-bound
  -- values are not shared in compiled code.)
  quadratic-fixedprec {e} a b c = with-prec' (fromℤ (pow10 e))
    where
      result : FixedPrec e -> Maybe (ℤ × ℤ) -> Maybe (FixedPrec e × FixedPrec e)
      result prec nothing = nothing
      result prec (just (x0 , x1)) = just (fromℤ x0 / prec , fromℤ x1 / prec)
      with-prec' : T -> Maybe (FixedPrec e × FixedPrec e)
      with-prec' prec' =
        result (fromℤ (pow10 e)) (int-quadratic (divide (prec' * b) a) (divide (prec' ^2 * c) a))

  instance
    QuadraticFixedPrec : {e : Precision} -> Quadratic T (FixedPrec e)
    QuadraticFixedPrec .quadratic = quadratic-fixedprec

-- ----------------------------------------------------------------------
-- Double instance

-- The quadratic formula, in the numerically stable form (for Float,
-- i.e. Haskell's Double).
quadratic-Float : {T : Set} {{_ : ToReal T}} -> T -> T -> T -> Maybe (Float × Float)
quadratic-Float a' b' c' =
  if radix <ᵇ 0 then nothing
  else if 0 ≤ᵇ b then just (t1 , t2)
  else just (t1' , t2')
  where
    a b c : Float
    a = to-real a'
    b = to-real b'
    c = to-real c'
    radix = b ^2 - 4 * a * c
    s1 = - b - sqrt radix
    s2 = - b + sqrt radix
    t1 = s1 / (2 * a)
    t2 = (2 * c) / s1
    t1' = (2 * c) / s2
    t2' = s2 / (2 * a)

instance
  QuadraticFloat : {T : Set} {{_ : ToReal T}} -> Quadratic T Float
  QuadraticFloat .quadratic = quadratic-Float
