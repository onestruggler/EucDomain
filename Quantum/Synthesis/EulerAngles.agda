-- This module is an Agda port of the module
-- Quantum.Synthesis.EulerAngles of the Haskell package newsynth (by
-- N. J. Ross and P. Selinger).
--
-- It provides functions for converting between matrices in U(2) and
-- their Euler angle representation.
--
-- The functions are generic over a "real" type A (Haskell: Floating a,
-- ArcTan2 a); they are meant for Float (Haskell Double) and FixedPrec e.
-- The arithmetic is done in exactly the same order as in Haskell
-- (including Haskell's parsing of unary minus, e.g. -x/2 = -(x/2)), so
-- that the rounding of inexact types agrees with Haskell.
--
-- Differences from the Haskell version:
--
-- * Haskell's Floating class implies Fractional; here the instance
--   arguments Ring A, Fractional A and Floating A are separate.
--   Division x / y is written x ÷ y, a total division that does not
--   need a NonZero proof (for Float and FixedPrec it is the ordinary
--   division, since their NonZero predicate is trivial; for types with
--   a non-trivial NonZero predicate, division by zero gives 0).
--
-- * The local bindings beta_plus_delta_over_2 and
--   beta_minus_delta_over_2 of Haskell's euler_angles are unused there
--   and are omitted.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.EulerAngles where

open import Data.Product.Base using (_×_ ; _,_)
open import Data.Rational.Base as Rat using ()
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.ArcTan2

-- ----------------------------------------------------------------------
-- * Auxiliary functions

infixl 7 _÷_

-- Total division: x ÷ y = x / y if y is non-zero, and 0 otherwise.
-- For approximate types (Float, FixedPrec) this is just x / y.
_÷_ : {A : Set} {{_ : Fractional A}} {{_ : SemiRing A}} -> A -> A -> A
x ÷ y with nonZero? y
... | yes nz = _/_ x y {{nz}}
... | no _ = 0#

module _ {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : Floating A}} where
  open LiteralsFor A

  private
    -- The magnitude of a complex number.
    mag : A [i] -> A
    mag (Cplx a b) = sqrt (a ^ 2 + b ^ 2)

    -- exp(ix).
    cis : A -> A [i]
    cis x = Cplx (cos x) (sin x)

    -- Complex conjugation (without an Adjoint A instance).
    conj : A [i] -> A [i]
    conj (Cplx x y) = Cplx x (- y)

    module _ {{_ : ArcTan2 A}} where
      -- The argument of a complex number.
      phase : A [i] -> A
      phase (Cplx a b) = arctan2 b a

      -- (Values used more than once are passed as arguments, so that
      -- they are computed only once in compiled code.)
      angles3 : A [i] -> A [i] -> A -> A -> A -> A × A × A × A
      angles3 c d alpha gamma delta = alpha , beta , gamma , delta
        where
          beta : A
          beta = 2 * phase (d * cis (- alpha - delta ÷ 2) + c * cis (- alpha + delta ÷ 2) * i)

      angles2 : A [i] -> A [i] -> A [i] -> A [i] -> A [i] -> A × A × A × A
      angles2 a b c d det =
        angles3 c d (phase det ÷ 2) (2 * arctan2 (mag b) (mag a)) (phase (b * d * i * conj det))

      euler-angles' : A [i] -> A [i] -> A [i] -> A [i] -> A × A × A × A
      euler-angles' a b c d = angles2 a b c d (a * d - b * c)

  -- ----------------------------------------------------------------------
  -- * Euler angles

  -- Decompose a unitary operator U into Euler angles (α, β, γ, δ).
  -- These angles are computed so that
  --
  -- * U = [exp iα] R_z(β) R_x(γ) R_z(δ).
  euler-angles : {{_ : ArcTan2 A}} -> Matrix Two Two (A [i]) -> A × A × A × A
  euler-angles op with from-matrix2x2 op
  ... | (a , b) , (c , d) = euler-angles' a b c d

  -- Compute the operator
  --
  -- * U = [exp iα] R_z(β) R_x(γ) R_z(δ)
  --
  -- from the given Euler angles.
  matrix-of-euler-angles : A × A × A × A -> Matrix Two Two (A [i])
  matrix-of-euler-angles (alpha , beta , gamma , delta) = op
    where
      cplx-cis : A -> A [i]
      cplx-cis theta = Cplx (cos theta) (sin theta)

      hadamard : Matrix Two Two (A [i])
      hadamard = Cplx (sqrt (fromℚ Rat.½)) 0 scalarmult matrix2x2 (1 , 1) (1 , -1)

      zrot' : A -> Matrix Two Two (A [i])
      zrot' g = matrix2x2 (cplx-cis (- (g ÷ 2)) , 0) (0 , cplx-cis (g ÷ 2))

      opa opb opc opd op : Matrix Two Two (A [i])
      opa = cplx-cis alpha scalarmult 1
      opb = zrot' beta
      opc = hadamard * zrot' gamma * hadamard
      opd = zrot' delta
      op = opa * opb * opc * opd
