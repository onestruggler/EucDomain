-- This module is an Agda port of the module
-- Quantum.Synthesis.GridProblems of the Haskell package newsynth (by
-- N. J. Ross and P. Selinger).
--
-- It provides functions for solving one- and two-dimensional grid
-- problems. Haskell names are translated from snake_case to
-- kebab-case (gridpoints_scaled ↦ gridpoints-scaled, to_upright ↦
-- to-upright, ...).
--
-- ----------------------------------------------------------------------
-- The real number type R
--
-- The functions are generic over a type R of (approximate) real
-- numbers, given by instance arguments. Haskell's classes map as
-- follows:
--
--   Num, Fractional   ↦ Ring R, Fractional R      (literals via LiteralsFor)
--   Ord               ↦ DecOrd R
--   Floor, RealFrac   ↦ Floor R                   (floor-of, ceiling-of)
--   RootTwoRing, RootHalfRing, Adjoint, Floating ↦ the same classes
--   Real (toRational) ↦ ToRational R
--   Quadratic QRootTwo r ↦ Quadratic QRootTwo R   (only unitdisk, disk)
--
-- Everything works for R = FixedPrec e (what gridsynth uses) and for
-- R = Float, except unitdisk and disk at Float (as in Haskell, where
-- there is no instance Quadratic QRootTwo Double). This module
-- defines the instance ToRational Float, which is needed for the
-- two-dimensional functions at Float (to be moved to Instances).
--
-- ----------------------------------------------------------------------
-- Laziness and the API for GridSynth
--
-- * All lists are ordinary (finite) Agda lists, with exactly the same
--   elements in the same order as in Haskell. In compiled code
--   (MAlonzo) they are lazy Haskell lists, so taking a prefix of a
--   long list (e.g. "take 1" in gridpoints2-scaled-with-gridop, or
--   the head in gridpoint-random) only computes that prefix, as in
--   Haskell.
--
-- * The infinite list [(0, l0), (1, l1), (2, l2), ...] of Haskell's
--   gridpoints2_increasing(_with_gridop) is a coinductive stream
--
--     gridpoints2-increasing : ConvexSet R → ConvexSet R → Stream (ℕ × List DOmega)
--
--   (Codata.Guarded.Stream, hence the --guardedness option). The
--   precomputation (grid operator, transformed sets, bounding boxes)
--   is done once, and the entries are computed lazily when the stream
--   is inspected. Consumers use it with fuel, for example
--
--     stream-take n s             -- the first n entries, as a List
--     stream-candidates n s       -- the flattened list [(k, u) | (k, us) ← first n entries, u ← us]
--
--   or directly with Stream.head / Stream.tail. The function
--   gridpoints2-increasing-fun gives the k-th entry directly.
--   GridSynth consumes the candidates for k = 0, 1, 2, ... in order
--   until a solvable one is found; for gridsynth with ε = 2^-b the
--   number of needed levels is roughly 3b + O(1), so a bound of a few
--   hundred levels plus b·4 is ample.
--
-- * Performance note for users defining convex sets (e.g. GridSynth's
--   epsilon_region): where-bound values are not shared in compiled
--   Agda code, so constants used by a characteristic function or line
--   intersector (like cos(-θ/2), sin(-θ/2), 1-ε²/2) must be passed as
--   arguments of a helper that builds the set; otherwise they are
--   recomputed on every call (the characteristic functions are called
--   once per candidate).
--
-- ----------------------------------------------------------------------
-- Deviations from Haskell
--
-- * Integers k ≥ 0 (the scaling exponents, the k of
--   gridpoints2_increasing) are ℕ. The k of gridpoints-scaled-parity
--   must be ≥ 1 (Haskell: error for k = 0, where we return []).
-- * The recursions that are not structural take fuel:
--   gridpoints-internal (rescaling steps, gridpoints-internal-fuel =
--   64; one or two steps are needed in practice), step-lemma (nested
--   wlog/shift steps, step-lemma-fuel = 64; at most about 5 are
--   needed) and reduction (number of Step Lemma applications,
--   reduction-fuel = 1000000). When the fuel runs out, the
--   gridpoints-internal recursion enumerates directly, step-lemma
--   returns nothing (stop), and reduction returns the identity.
-- * floorlog x for x ≤ 0 (Haskell: error) returns (0, x).
-- * Division by zero (never happens for legal inputs) gives 0 for exact
--   types; at Float and FixedPrec division is total anyway.
-- * The test "x == 0" of rectangle is done with the order (x ≤ 0 and
--   0 ≤ x), which is IEEE equality at Float, as in Haskell.
-- * Haskell's data types Ellipse and ConvexSet have constructors
--   Ellipse' and ConvexSet' here (Agda does not allow a constructor
--   with the name of its type).
-- * Show (Ellipse R) prints the matrix with the generic matrix
--   printer (Haskell would use the overlapping instance for
--   DRootTwo matrices when R = DRootTwo).

{-# OPTIONS --without-K --safe --guardedness #-}

module Quantum.Synthesis.GridProblems where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Data.Vec.Base using ([] ; _∷_)
open import Codata.Guarded.Stream using (Stream)
open Codata.Guarded.Stream.Stream using (head ; tail)

open import Instances
open import Literals
open import Data.Number.FixedPrec using (float-of-ℚ)
import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (divide ; divℤ ; modℤ)
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.QuadraticEquation
open import Quantum.Synthesis.Random using (RandomGen ; randomR)

-- ----------------------------------------------------------------------
-- * Missing instances


-- ----------------------------------------------------------------------
-- * Auxiliary functions

private
  infixl 7 _÷_
  -- Division that does not require a NonZero proof (x ÷ 0 = 0 for
  -- exact types; Float and FixedPrec divide as usual).
  _÷_ : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} -> A -> A -> A
  x ÷ y = divide x y

  -- The rational constant a/d in a field.
  q : {A : Set} {{_ : Fractional A}} -> ℤ -> (d : ℕ) .{{_ : Nat.NonZero d}} -> A
  q a d = fromℚ (a Rat./ d)

  -- The list [lo .. hi] of integers (Haskell's enumFromTo).
  range : ℤ -> ℤ -> List ℤ
  range lo hi = if hi <ᵇ lo then [] else go lo (Int.∣ hi - lo ∣ Nat.+ 1)
    where
      go : ℤ -> ℕ -> List ℤ
      go a zero = []
      go a (suc n) = a ∷ go (a + 1) n

  -- Haskell's round at Double (to the nearest integer, ties to even).
  round-double : Float -> ℤ
  round-double x with Float.round x
  ... | just n = n
  ... | nothing = 0

-- We write x `within` (a,b) for a ≤ x ≤ b, or equivalently, x ∈ [a, b].
within : {A : Set} {{_ : DecOrd A}} -> A -> A × A -> Bool
within x (a , b) = (a ≤ᵇ x) ∧ (x ≤ᵇ b)

-- Given an interval, return a slightly bigger one.
fatten-interval : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} -> A × A -> A × A
fatten-interval {A} (x , y) = fatten (q 1 10000 * (y - x))
  where
    fatten : A -> A × A
    fatten epsilon = x - epsilon , y + epsilon

-- The constant λ = 1 + √2.
lambda : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> A
lambda = 1# + roottwo

-- The constant λ⁻¹ = √2 - 1.
lambda-inv : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> A
lambda-inv = roottwo - 1#

-- Return λᵏ, where k ∈ ℤ. This works in any RootTwoRing.
lambdapower : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> A
lambdapower (+ n) = lambda ^ n
lambdapower -[1+ n ] = lambda-inv ^ suc n

-- Return (-1)ᵏ, where k ∈ ℤ.
signpower : {A : Set} {{_ : Ring A}} -> ℤ -> A
signpower k = if evenℤ k then 1# else - 1#

-- Given positive numbers b and x, return (n, r) such that x = r bⁿ
-- and 1 ≤ r < b. In other words, let n = ⌊log_b x⌋ and r = x b⁻ⁿ.
-- This also works for exact types such as ℚ and ℚ[√2]. For x ≤ 0
-- (Haskell: error) return (0, x).
floorlog : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : DecOrd A}} -> A -> A -> ℤ × A
floorlog = Data.Number.FixedPrec.Aux.floorlog

-- A version of the logarithm to base b that returns a Float
-- (Haskell: Double). The logarithm of just about any value can fit
-- into a Float; so if not a lot of precision is required in the
-- mantissa, this function is often faster than logBase.
logBase-double : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : DecOrd A}} {{_ : ToRational A}} -> A -> A -> Float
logBase-double {A} b x =
  if 1# <ᵇ b then pos b
  else if b ≤ᵇ 0# then 0.0 Float.÷ 0.0      -- NaN
  else if 1# ≤ᵇ b then 1.0 Float.÷ 0.0      -- b == 1: Infinity
  else Float.- pos (1# ÷ b)
  where
    to-double : A -> Float
    to-double y = float-of-ℚ (toℚ y)

    combine : A -> ℤ × A -> Float
    combine b' (n , r) = Float.fromℤ n Float.+ logBase (to-double b') (to-double r)

    pos : A -> Float
    pos b' = combine b' (floorlog b' x)

-- ----------------------------------------------------------------------
-- * Points and operators

-- A point in the plane.
Point : Set -> Set
Point A = A × A

-- The inner product of two points.
iprod : {A : Set} {{_ : Ring A}} -> Point A -> Point A -> A
iprod (x , y) (a , b) = x * a + y * b

-- Subtract two points.
point-sub : {A : Set} {{_ : Ring A}} -> Point A -> Point A -> Point A
point-sub (x , y) (a , b) = x - a , y - b

-- Convert a point with coordinates in DRootTwo to a point with
-- coordinates in any RootHalfRing.
point-fromDRootTwo : {A : Set} {{_ : RootHalfRing A}} -> Point DRootTwo -> Point A
point-fromDRootTwo (x , y) = fromDRootTwo x , fromDRootTwo y

-- An operator is a real 2×2-matrix.
Operator : Set -> Set
Operator A = Matrix Two Two A

-- A 2×2-matrix, by rows.
pattern Op a b c d = Matrix' ((a ∷ c ∷ []) ∷ (b ∷ d ∷ []) ∷ [])

-- Construct a 2×2-matrix, by rows.
toOperator : {A : Set} -> (A × A) × (A × A) -> Operator A
toOperator ((a , b) , (c , d)) = matrix2x2 (a , b) (c , d)

-- Extract the entries of a 2×2-matrix, by rows.
fromOperator : {A : Set} -> Operator A -> (A × A) × (A × A)
fromOperator = from-matrix2x2

-- Convert an operator with entries in DRootTwo to an operator with
-- entries in any RootHalfRing.
op-fromDRootTwo : {A : Set} {{_ : RootHalfRing A}} -> Operator DRootTwo -> Operator A
op-fromDRootTwo m = matrix-map fromDRootTwo m

-- The determinant of a 2×2-matrix.
det : {A : Set} {{_ : Ring A}} -> Operator A -> A
det (Op a b c d) = a * d - b * c

-- Compute the skew of a positive operator of determinant 1: the
-- product of the off-diagonal entries.
operator-skew : {A : Set} {{_ : Ring A}} -> Operator A -> A
operator-skew (Op a b c d) = b * c

-- Apply a linear transformation G to a point p.
point-transform : {A : Set} {{_ : Ring A}} -> Operator A -> Point A -> Point A
point-transform (Op a b c d) (x , y) = a * x + b * y , c * x + d * y

-- Calculate the inverse of an operator of determinant 1. Note: this
-- does not work correctly for operators whose determinant is not 1.
special-inverse : {A : Set} {{_ : Ring A}} -> Operator A -> Operator A
special-inverse opG@(Op a b c d) = det opG scalarmult toOperator ((d , - b) , (- c , a))

-- A state is a pair (D, Δ) of real positive definite matrices of
-- determinant 1. It encodes a pair of ellipses.
OperatorPair : Set -> Set
OperatorPair A = Operator A × Operator A

-- The skew of a state is the sum of the skews of the two operators.
skew : {A : Set} {{_ : Ring A}} -> OperatorPair A -> A
skew (m1 , m2) = operator-skew m1 + operator-skew m2

-- ----------------------------------------------------------------------
-- * Grid operators

-- The special grid operator R: a clockwise rotation by 45°.
opR : {A : Set} {{_ : Ring A}} {{_ : RootHalfRing A}} -> Operator A
opR = roothalf * toOperator ((1# , - 1#) , (1# , 1#))

-- The special grid operator A: a clockwise shearing with offset 2,
-- parallel to the x-axis.
opA : {A : Set} {{_ : Ring A}} -> Operator A
opA = matrix2x2 (1# , - fromℕ 2) (0# , 1#)

-- The special grid operator A⁻¹.
opA-inv : {A : Set} {{_ : Ring A}} -> Operator A
opA-inv = matrix2x2 (1# , fromℕ 2) (0# , 1#)

-- The operator Aᵏ.
opA-power : {A : Set} {{_ : Ring A}} -> ℤ -> Operator A
opA-power (+ n) = opA ^ n
opA-power -[1+ n ] = opA-inv ^ suc n

-- The special grid operator B: a clockwise shearing with offset √2,
-- parallel to the x-axis.
opB : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> Operator A
opB = matrix2x2 (1# , roottwo) (0# , 1#)

-- The special grid operator B⁻¹.
opB-inv : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> Operator A
opB-inv = matrix2x2 (1# , - roottwo) (0# , 1#)

-- The operator Bᵏ.
opB-power : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> Operator A
opB-power (+ n) = opB ^ n
opB-power -[1+ n ] = opB-inv ^ suc n

-- The special grid operator K.
opK : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} {{_ : RootHalfRing A}} -> Operator A
opK = roothalf * matrix2x2 (- lambda-inv , - 1#) (lambda , 1#)

-- The Pauli X operator is a special grid operator.
opX : {A : Set} {{_ : Ring A}} -> Operator A
opX = matrix2x2 (0# , 1#) (1# , 0#)

-- The Pauli Z operator is a special grid operator.
opZ : {A : Set} {{_ : Ring A}} -> Operator A
opZ = matrix2x2 (1# , 0#) (0# , - 1#)

-- The special grid operator S: a scaling by λ = 1+√2 in the
-- x-direction, and by λ⁻¹ = -1+√2 in the y-direction.
opS : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> Operator A
opS = toOperator ((lambda , 0#) , (0# , lambda-inv))

-- The special grid operator S⁻¹.
opS-inv : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> Operator A
opS-inv = matrix2x2 (lambda-inv , 0#) (0# , lambda)

-- Return Sᵏ.
opS-power : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> Operator A
opS-power (+ n) = opS ^ n
opS-power -[1+ n ] = opS-inv ^ suc n

-- ----------------------------------------------------------------------
-- * Shifts

-- Given an operator D, compute σᵏDσᵏ.
shift-sigma : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> Operator A -> Operator A
shift-sigma k (Op a b c d) = matrix2x2 (lambdapower k * a , b) (c , lambdapower (- k) * d)

-- Given an operator Δ, compute τᵏΔτᵏ.
shift-tau : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> Operator A -> Operator A
shift-tau k (Op a b c d) =
  matrix2x2 (lambdapower (- k) * a , signpower k * b) (c * signpower k , lambdapower k * d)

-- Compute the k-shift of a state (D,Δ).
shift-state : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> ℤ -> OperatorPair A -> OperatorPair A
shift-state k (d , delta) = shift-sigma k d , shift-tau k delta

-- ----------------------------------------------------------------------
-- * Ellipses and convex sets

-- An ellipse is given by an operator D and a center p; the ellipse in
-- this case is A = { v | (v-p)† D (v-p) ≤ 1}.
record Ellipse (R : Set) : Set where
  constructor Ellipse'
  field
    ellipse-operator : Operator R
    ellipse-center : Point R
open Ellipse public

-- The characteristic function of a set A inputs a point p, and
-- outputs true if p ∈ A and false otherwise. The point p is given of
-- an exact type, so characteristic functions have the opportunity to
-- use infinite precision.
CharFun : Set
CharFun = Point DRootTwo -> Bool

-- A line intersector knows about some compact convex set A. Given a
-- straight line L, given as a parametric equation p(t) = v + tw, where
-- v and w ≠ 0 are vectors, the line intersector returns (an
-- approximation of) t₀ and t₁ such that p(t) ∈ A iff t ∈ [t₀, t₁]
-- (or nothing if the intersection is empty).
LineIntersector : Set -> Set
LineIntersector R = Point DRootTwo -> Point DRootTwo -> Maybe (R × R)

-- A compact convex set is given by a bounding ellipse, a
-- characteristic function, and a line intersector.
record ConvexSet (R : Set) : Set where
  constructor ConvexSet'
  field
    convex-ellipse : Ellipse R
    convex-charfun : CharFun
    convex-intersector : LineIntersector R
open ConvexSet public

-- Printing, as Haskell's derived Show instance for Ellipse, e.g.
-- "Ellipse (matrix [[1.0,0.0],[0.0,1.0]]) (0.0,0.0)".
showsPrec-Ellipse : {R : Set} -> (ℕ -> R -> String) -> ℕ -> Ellipse R -> String
showsPrec-Ellipse sp d (Ellipse' m (x , y)) =
  showParen d 10 ("Ellipse " ++ showsPrec-Matrix sp 11 m ++ " (" ++ sp 0 x ++ "," ++ sp 0 y ++ ")")

instance
  ShowEllipse : {R : Set} {{_ : Show R}} -> Show (Ellipse R)
  ShowEllipse .showsPrec = showsPrec-Ellipse showsPrec

  ShowConvexSet : {R : Set} {{_ : Show R}} -> Show (ConvexSet R)
  ShowConvexSet .showsPrec _ (ConvexSet' ell _ _) = "ConvexSet (" ++ show ell ++ ", ..., ...)"

-- ----------------------------------------------------------------------
-- * Generic real number functions

module _ {R : Set} {{_ : Ring R}} {{_ : DecOrd R}} {{_ : Fractional R}} where
  open LiteralsFor R

  -- ----------------------------------------------------------------------
  -- ** 1-dimensional grid problems

  -- The 1-dimensional grid problem is the following: given closed
  -- intervals A and B of the real numbers, find all α ∈ ℤ[√2] such
  -- that α ∈ A and α• ∈ B.

  module _ {{_ : Floor R}} {{_ : RootTwoRing R}} where

    -- The fuel of gridpoints-internal: the maximal number of rescaling
    -- steps (one or two are needed).
    gridpoints-internal-fuel : ℕ
    gridpoints-internal-fuel = 64

    -- Similar to gridpoints, except: (1) assume that x0 and y0 are not
    -- too far from the origin (say, between -10 and 10); (2) the
    -- function potentially returns some non-solutions, so the caller
    -- should test for accuracy.
    gridpoints-internal : R × R -> R × R -> List ZRootTwo
    gridpoints-internal = go gridpoints-internal-fuel
      where
        enumerate : R × R -> R × R -> List ZRootTwo
        enumerate (x0 , x1) (y0 , y1) =
          List.concatMap (λ a -> List.map (RootTwo a) (range (bmin a) (bmax a))) (range amin amax)
          where
            amin = ceiling-of ((x0 + y0) ÷ 2)
            amax = floor-of ((x1 + y1) ÷ 2)
            bmin bmax : ℤ -> ℤ
            bmin a = ceiling-of ((fromℤ a - y1) ÷ roottwo)
            bmax a = floor-of ((fromℤ a - y0) ÷ roottwo)

        -- (Performance: where-bound values are not shared in compiled
        -- Agda code, so dx, dy, n and the powers of λ are computed by
        -- helper functions and passed on as arguments; they are then
        -- computed at most once, and only when needed.)
        go : ℕ -> R × R -> R × R -> List ZRootTwo
        go zero xs ys = enumerate xs ys
        go (suc f) (x0 , x1) (y0 , y1) = with-d (x1 - x0) (y1 - y0)
          where
            -- The rescaled problem, given the factor c for the solutions,
            -- the factor sx for the x-interval, and the new y-interval.
            rescale : ZRootTwo -> R -> R × R -> List ZRootTwo
            rescale c sx ys = List.map (c *_) (go f (sx * x0 , sx * x1) ys)

            -- n = ⌊log_λ dy⌋ (even-n = evenℤ n), and nn = |n|.
            with-n : R -> Bool -> ℕ -> List ZRootTwo
            with-n dy even-n nn =
              if (lambda ≤ᵇ dy) ∧ even-n then
                big (lambda-inv ^ nn) (lambda ^ nn) ((- lambda-inv) ^ nn) false
              else if lambda ≤ᵇ dy then
                big (lambda-inv ^ nn) (lambda ^ nn) ((- lambda-inv) ^ nn) true
              else if (0 <ᵇ dy) ∧ (dy <ᵇ 1) ∧ even-n then
                big (lambda ^ nn) (lambda-inv ^ nn) ((- lambda) ^ nn) false
              else if (0 <ᵇ dy) ∧ (dy <ᵇ 1) then
                big (lambda ^ nn) (lambda-inv ^ nn) ((- lambda) ^ nn) true
              else
                enumerate (x0 , x1) (y0 , y1)
              where
                -- the scaled problem, with y-factor sy (lambda-bul-n or
                -- lambda-bul-inv-m); swap: whether the y-interval is
                -- reversed.
                big : ZRootTwo -> R -> R -> Bool -> List ZRootTwo
                big c sx sy swap =
                  rescale c sx (if swap then (sy * y1 , sy * y0) else (sy * y0 , sy * y1))

            with-floorlog : R -> ℤ -> List ZRootTwo
            with-floorlog dy n = with-n dy (evenℤ n) Int.∣ n ∣

            with-d : R -> R -> List ZRootTwo
            with-d dx dy =
              if (dy ≤ᵇ 0) ∧ (0 <ᵇ dx) then
                List.map adj2 (go f (y0 , y1) (x0 , x1))
              else with-floorlog dy (proj₁ (floorlog lambda dy))

    -- ** General solutions

    -- Given two intervals A = [x₀, x₁] and B = [y₀, y₁] of real
    -- numbers, output all solutions α ∈ ℤ[√2] of the 1-dimensional
    -- grid problem for A and B. The list is sorted in order of
    -- increasing α.
    gridpoints : R × R -> R × R -> List ZRootTwo
    -- (alpha and the offsets are passed as arguments, since
    -- where-bound values are not shared in compiled code.)
    gridpoints (x0 , x1) (y0 , y1) =
      with-alpha (RootTwo (divℤ (floor-of (x0 + y0)) 2) (divℤ (floor-of (roottwo * (x0 - y0))) 4))
      where
        test : ZRootTwo -> Bool
        test x = within (fromZRootTwo x) (x0 , x1) ∧ within (fromZRootTwo (adj2 x)) (y0 , y1)
        with-offsets : ZRootTwo -> R -> R -> List ZRootTwo
        with-offsets alpha xoff yoff =
          List.filterᵇ test (List.map (_+ alpha) (gridpoints-internal (x0 - xoff , x1 - xoff) (y0 - yoff , y1 - yoff)))
        with-alpha : ZRootTwo -> List ZRootTwo
        with-alpha alpha = with-offsets alpha (fromZRootTwo alpha) (fromZRootTwo (adj2 alpha))

    -- Like gridpoints, but only produce solutions a + b√2 where a has
    -- the same parity as the given integer.
    gridpoints-parity : ℤ -> R × R -> R × R -> List ZRootTwo
    gridpoints-parity e (x0 , x1) (y0 , y1) =
      List.map (λ z' -> roottwo * z' + fromℤ e2) (gridpoints (x0' , x1') (- y1' , - y0'))
      where
        e2 = modℤ e 2
        e' : R
        e' = fromℤ e2
        x0' = (x0 - e') ÷ roottwo
        x1' = (x1 - e') ÷ roottwo
        y0' = (y0 - e') ÷ roottwo
        y1' = (y1 - e') ÷ roottwo

    -- ** Randomized solutions

    -- Given two intervals A = [x₀, x₁] and B = [y₀, y₁] of real
    -- numbers, and a source of randomness, output a random solution α
    -- ∈ ℤ[√2] of the 1-dimensional grid problem for A and B.
    --
    -- Note: the randomness is not uniform. To ensure that the set of
    -- solutions is non-empty, we must have ΔxΔy ≥ (1 + √2)², where Δx
    -- = x₁ − x₀ ≥ 0 and Δy = y₁ − y₀ ≥ 0. If there are no solutions
    -- at all, the function returns nothing.
    gridpoint-random : {G : Set} {{_ : RandomGen G}} -> R × R -> R × R -> G -> Maybe ZRootTwo
    gridpoint-random (x0 , x1) (y0 , y1) g =
      first (gridpoints (x0 + r * dx , x1) (y0 , y1) List.++ gridpoints (x0 , x1) (y0 , y1))
      where
        dx = max 0 (x1 - x0)
        dy = max 0 (y1 - y0)
        area = dx * dy
        n = floor-of (area + 1)
        i' : ℤ
        i' = proj₁ (randomR (0 , n - 1) g)
        r = fromℤ i' ÷ fromℤ n
        first : List ZRootTwo -> Maybe ZRootTwo
        first [] = nothing
        first (h ∷ _) = just h

    -- Like gridpoint-random, but only produce solutions a + b√2 where
    -- a has the same parity as the given integer.
    gridpoint-random-parity : {G : Set} {{_ : RandomGen G}} -> ℤ -> R × R -> R × R -> G -> Maybe ZRootTwo
    gridpoint-random-parity e (x0 , x1) (y0 , y1) g = result (gridpoint-random (x0' , x1') (- y1' , - y0') g)
      where
        e2 = modℤ e 2
        e' : R
        e' = fromℤ e2
        x0' = (x0 - e') ÷ roottwo
        x1' = (x1 - e') ÷ roottwo
        y0' = (y0 - e') ÷ roottwo
        y1' = (y1 - e') ÷ roottwo
        result : Maybe ZRootTwo -> Maybe ZRootTwo
        result (just z') = just (roottwo * z' + fromℤ e2)
        result nothing = nothing

    -- ** Scaled solutions

    -- The scaled version of the 1-dimensional grid problem is the
    -- following: given closed intervals A and B of the real numbers,
    -- and k ≥ 0, find all α ∈ ℤ[√2] / √2ᵏ such that α ∈ A and α• ∈ B.

    -- Given intervals A = [x₀, x₁] and B = [y₀, y₁], and an integer k
    -- ≥ 0, output all solutions α ∈ ℤ[√2] / √2ᵏ of the scaled
    -- 1-dimensional grid problem for A, B, and k. The list is sorted
    -- in order of increasing α.
    gridpoints-scaled : R × R -> R × R -> ℕ -> List DRootTwo
    -- (scale and scale-inv are passed as arguments, since where-bound
    -- values are not shared in compiled code.)
    gridpoints-scaled (x0 , x1) (y0 , y1) k = go (roothalf ^ k) (roottwo ^ k)
      where
        go : DRootTwo -> R -> List DRootTwo
        go scale scale-inv =
          List.map (λ w -> scale * fromZRootTwo w) (gridpoints (scale-inv * x0 , scale-inv * x1) ys)
          where
            ys : R × R
            ys = if evenℕ k then (scale-inv * y0 , scale-inv * y1)
                 else (- (scale-inv * y1) , - (scale-inv * y0))

    -- Like gridpoints-scaled, but assume k ≥ 1, take an additional
    -- parameter β ∈ ℤ[√2] / √2ᵏ, and return only those α such that
    -- β − α ∈ ℤ[√2] / √2ᵏ⁻¹. For k = 0 (Haskell: error) return [].
    gridpoints-scaled-parity : {{_ : RootHalfRing R}} -> DRootTwo -> R × R -> R × R -> ℕ -> List DRootTwo
    gridpoints-scaled-parity beta (x0 , x1) (y0 , y1) zero = []
    gridpoints-scaled-parity beta (x0 , x1) (y0 , y1) k@(suc k-1) =
      if denomexp beta Nat.≤ᵇ k-1 then gridpoints-scaled (x0 , x1) (y0 , y1) k-1
      else with-offs (roothalf ^ k)
      where
        -- (the offsets are passed as arguments, since where-bound
        -- values are not shared in compiled code.)
        go : DRootTwo -> R -> R -> List DRootTwo
        go offs offs' offs-bul' =
          List.map (λ z' -> z' - offs)
            (gridpoints-scaled (x0 + offs' , x1 + offs') (y0 + offs-bul' , y1 + offs-bul') k-1)
        with-offs : DRootTwo -> List DRootTwo
        with-offs offs = go offs (fromDRootTwo offs) (fromDRootTwo (adj2 offs))

  -- ----------------------------------------------------------------------
  -- ** Operators on real numbers

  module _ {{_ : Floating R}} where

    -- The (b,z)-representation of a positive operator with
    -- determinant 1 is [[e λ⁻ᶻ, b], [b, e λᶻ]], where b, z ∈ ℝ and e >
    -- 0 with e² = b² + 1. Create such an operator from parameters b
    -- and z.
    operator-from-bz : {{_ : RootTwoRing R}} -> R -> R -> Operator R
    operator-from-bz b z = toOperator ((e ÷ lambda-z , b) , (b , e * lambda-z))
      where
        lambda-z = lambda ** z
        e = sqrt (1 + b ^ 2)

    -- Compute the uprightness of a positive operator D: the ratio of
    -- the area of the ellipse E = {v | v†Dv ≤ 1} to the area of its
    -- bounding box, π/4 √(det D / (ad)).
    uprightness : Operator R -> R
    uprightness m@(Op a b c d) = pi ÷ 4 * sqrt (det m ÷ (a * d))

    -- Calculate the bounding box for an ellipse.
    boundingbox-ellipse : Ellipse R -> (R × R) × (R × R)
    boundingbox-ellipse (Ellipse' matA (x , y)) = box (sqrt (det matA)) matA
      where
        box : R -> Operator R -> (R × R) × (R × R)
        box sqrt-det (Op a b c d) = (x - w , x + w) , (y - h , y + h)
          where
            w = sqrt d ÷ sqrt-det
            h = sqrt a ÷ sqrt-det

    -- Calculate a bounding box for a convex set. Returns ((x₀, x₁),
    -- (y₀, y₁)).
    boundingbox : ConvexSet R -> (R × R) × (R × R)
    boundingbox (ConvexSet' ell _ _) = boundingbox-ellipse ell

  module _ {{_ : RootTwoRing R}} {{_ : ToRational R}} where

    -- Conversely, given a positive definite real operator of
    -- determinant 1, return the parameters (b, z). This is the inverse
    -- of operator-from-bz. For efficiency reasons, the parameter z,
    -- which is a logarithm, is modeled as a Float.
    operator-to-bz : Operator R -> R × Float
    operator-to-bz (Op a b c d) = b , 0.5 Float.* logBase-double lambda (d ÷ a)

    -- The bias of a state is ζ - z.
    bias : OperatorPair R -> Float
    bias (matA , matB) = proj₂ (operator-to-bz matB) Float.- proj₂ (operator-to-bz matA)

  -- A version of operator-to-bz that returns (b, λ²ᶻ) instead of (b, z).
  operator-to-bl2z : Operator R -> R × R
  operator-to-bl2z (Op a b c d) = b , d ÷ a

  -- ----------------------------------------------------------------------
  -- ** Skew reduction

  module _ {{_ : Floor R}} {{_ : RootTwoRing R}} where

    -- An implementation of the A-Lemma. Given z and ζ, compute the
    -- integer m such that the operator Aᵐ reduces the skew.
    lemma-A : {{_ : Floating R}} -> R -> R -> ℤ
    lemma-A z zeta = max 1 (floor-of (lambda ** min z zeta ÷ 2))

    -- An implementation of the B-Lemma. Given z and ζ, compute the
    -- integer m such that the operator Bᵐ reduces the skew.
    lemma-B : {{_ : Floating R}} -> R -> R -> ℤ
    lemma-B z zeta = max 1 (floor-of (lambda ** min z zeta ÷ roottwo))

    -- A version of lemma-A that inputs λ²ᶻ instead of z and λ²ᶻᵉᵗᵃ
    -- instead of ζ.
    lemma-A-l2 : R -> R -> ℤ
    lemma-A-l2 l2z l2zeta = max 1 (intsqrt (floor-of (min l2z l2zeta ÷ 4)))

    -- A version of lemma-B that inputs λ²ᶻ instead of z and λ²ᶻᵉᵗᵃ
    -- instead of ζ.
    lemma-B-l2 : R -> R -> ℤ
    lemma-B-l2 l2z l2zeta = max 1 (intsqrt (floor-of (min l2z l2zeta ÷ 2)))

-- ----------------------------------------------------------------------
-- * Two-dimensional grid problems

module _ {R : Set} {{_ : Ring R}} {{_ : DecOrd R}} {{_ : Fractional R}} {{_ : RootHalfRing R}} where
  open LiteralsFor R

  -- ----------------------------------------------------------------------
  -- ** Specific convex sets

  module _ {{_ : Quadratic QRootTwo R}} where

    -- The line intersector of the closed disk of radius √s centered
    -- at the origin.
    private
      disk-intersector : DRootTwo -> LineIntersector R
      disk-intersector s p v = quadratic (fromDRootTwo {QRootTwo} a) (fromDRootTwo b) (fromDRootTwo c)
        where
          a b c : DRootTwo
          a = iprod v v
          b = 2 * iprod v p
          c = iprod p p - s

    -- The closed unit disk.
    unitdisk : ConvexSet R
    unitdisk = ConvexSet' (Ellipse' 1 (0 , 0)) tst (disk-intersector 1)
      where
        tst : CharFun
        tst (x , y) = x ^ 2 + y ^ 2 ≤ᵇ 1

    -- A closed disk of radius √s, centered at the origin. Assume s > 0.
    disk : DRootTwo -> ConvexSet R
    disk s = ConvexSet' (Ellipse' ((1 ÷ fromDRootTwo s) scalarmult 1) (0 , 0)) tst (disk-intersector s)
      where
        tst : CharFun
        tst (x , y) = x ^ 2 + y ^ 2 ≤ᵇ s

  -- A closed rectangle with the given dimensions.
  rectangle : R × R -> R × R -> ConvexSet R
  rectangle (x0 , x1) (y0 , y1) = ConvexSet' ell tst int
    where
      w = x1 - x0
      h = y1 - y0
      center : Point R
      center = (x0 + x1) ÷ 2 , (y0 + y1) ÷ 2
      mat : Operator R
      mat = toOperator ((2 ÷ w ^ 2 , 0) , (0 , 2 ÷ h ^ 2))
      ell = Ellipse' mat center
      tst : CharFun
      tst (x , y) = within (fromDRootTwo x) (x0 , x1) ∧ within (fromDRootTwo y) (y0 , y1)
      is-zero : R -> Bool
      is-zero x = (x ≤ᵇ 0) ∧ (0 ≤ᵇ x)
      int-internal : Point R -> Point R -> Maybe (R × R)
      int-internal (px , py) (vx , vy) =
        if is-zero vx ∧ within px (x0 , x1) then just (min t0y t1y , max t0y t1y)
        else if is-zero vx then nothing
        else if is-zero vy ∧ within py (y0 , y1) then just (min t0x t1x , max t0x t1x)
        else if is-zero vy then nothing
        else just (max (min t0x t1x) (min t0y t1y) , min (max t0x t1x) (max t0y t1y))
        where
          t0x = (x0 - px) ÷ vx
          t1x = (x1 - px) ÷ vx
          t0y = (y0 - py) ÷ vy
          t1y = (y1 - py) ÷ vy
      int : LineIntersector R
      int p v = int-internal (point-fromDRootTwo p) (point-fromDRootTwo v)

-- ----------------------------------------------------------------------
-- ** Action of grid operators

module _ {R : Set} {{_ : Ring R}} {{_ : Adjoint R}} where

  -- Compute the right action of a grid operator G on a state (D, Δ).
  -- This is defined as: (D, Δ) ⋅ G := (G†DG, G•†ΔG•).
  action : {{_ : RootHalfRing R}} -> OperatorPair R -> Operator DRootTwo -> OperatorPair R
  action (a , b) g = act a (op-fromDRootTwo g) , act b (op-fromDRootTwo (adj2 g))
    where
      act : Operator R -> Operator R -> Operator R
      act m g' = adj g' * m * g'

  -- Apply a special linear transformation G to an ellipse A. This
  -- results in the new ellipse G(A) = { G(z) | z ∈ A }.
  ellipse-transform : Operator R -> Ellipse R -> Ellipse R
  ellipse-transform opG (Ellipse' matA ctrA) = go (special-inverse opG)
    where
      go : Operator R -> Ellipse R
      go opG-inv = Ellipse' (adj opG-inv * matA * opG-inv) (point-transform opG ctrA)

-- Apply a special grid operator G to a characteristic function.
charfun-transform : Operator DRootTwo -> CharFun -> CharFun
charfun-transform opG f = go (special-inverse opG)
  where
    go : Operator DRootTwo -> CharFun
    go opG-inv p = f (point-transform opG-inv p)

-- Apply a special linear transformation G to a line intersector. If
-- the input line intersector was for a convex set A, then the output
-- line intersector is for the set G(A) = { G(z) | z ∈ A }.
lineintersector-transform : {R : Set} -> Operator DRootTwo -> LineIntersector R -> LineIntersector R
lineintersector-transform opG intA = go (special-inverse opG)
  where
    go : Operator DRootTwo -> LineIntersector _
    go opG-inv v' w' = intA (point-transform opG-inv v') (point-transform opG-inv w')

-- Apply a special linear transformation G to a convex set A. This
-- results in the new convex set G(A) = { G(z) | z ∈ A }.
convex-transform : {R : Set} {{_ : Ring R}} {{_ : Adjoint R}} {{_ : RootHalfRing R}} -> Operator DRootTwo -> ConvexSet R -> ConvexSet R
convex-transform opG (ConvexSet' ellA tstA intA) =
  ConvexSet' (ellipse-transform (op-fromDRootTwo opG) ellA) (charfun-transform opG tstA) (lineintersector-transform opG intA)

-- The data that gridpoints2-scaled-with-gridop precomputes from the
-- sets A and B and the grid operator G (it is computed once and
-- shared by all k): G, the characteristic functions of A and B, the
-- line intersectors and bounding boxes of G⁻¹(A) and G•⁻¹(B).
record GridPrecomp (R : Set) : Set where
  constructor GridPrecomp'
  field
    pc-opG : Operator DRootTwo
    pc-tstA pc-tstB : CharFun
    pc-intA' pc-intB' : LineIntersector R
    pc-bboxA' pc-bboxB' : (R × R) × (R × R)

-- ----------------------------------------------------------------------
-- ** The Step Lemma and gridpoints2

module _ {R : Set} {{_ : Ring R}} {{_ : DecOrd R}} {{_ : Fractional R}} {{_ : Floor R}}
         {{_ : RootTwoRing R}} {{_ : RootHalfRing R}} {{_ : Floating R}} {{_ : Adjoint R}}
         {{_ : ToRational R}} where
  open LiteralsFor R

  -- The fuel of step-lemma: the maximal nesting of the "without loss
  -- of generality" and shift steps (at most about 5 are needed).
  step-lemma-fuel : ℕ
  step-lemma-fuel = 64

  -- The fuel of reduction: the maximal number of applications of the
  -- Step Lemma.
  reduction-fuel : ℕ
  reduction-fuel = 1000000

  -- An implementation of the Step Lemma. Input a state (D,Δ). If the
  -- skew is > 15, produce a special grid operator whose action reduces
  -- Skew(D,Δ) by at least 5%. If the skew is ≤ 15 and β ≥ 0 and z + ζ ≥
  -- 0, do nothing. Otherwise, produce a special grid operator that
  -- ensures β ≥ 0 and z + ζ ≥ 0. The first argument is fuel.
  step-lemma' : ℕ -> OperatorPair R -> Maybe (Operator DRootTwo)
  step-lemma' zero _ = nothing
  step-lemma' (suc fuel) (matA , matB) = with-bl2z (operator-to-bl2z matA) (operator-to-bl2z matB)
    where
      logLambda : R -> Float
      logLambda a = logBase-double lambda a

      wlog-using : Operator DRootTwo -> Maybe (Operator DRootTwo)
      wlog-using op = compose op (step-lemma' fuel (action (matA , matB) op))
        where
          compose : Operator DRootTwo -> Maybe (Operator DRootTwo) -> Maybe (Operator DRootTwo)
          compose op nothing = just op
          compose op (just op2) = just (op * op2)

      with-shift : ℤ -> Maybe (Operator DRootTwo)
      with-shift k = unshift (step-lemma' fuel (shift-state k (matA , matB)))
        where
          unshift : Maybe (Operator DRootTwo) -> Maybe (Operator DRootTwo)
          unshift nothing = nothing
          unshift (just op2) = just (shift-sigma k op2)

      -- The decision, given b, λ²ᶻ, β, λ²ᶻᵉᵗᵃ and l2z-minus-zeta =
      -- λ^(2(z-ζ)). (They are passed as arguments, since where-bound
      -- values are not shared in compiled code.)
      decide : R -> R -> R -> R -> R -> Maybe (Operator DRootTwo)
      decide b l2z beta l2zeta l2z-minus-zeta =
        -- First ensure that β ≥ 0, by applying Z if necessary.
        if beta <ᵇ 0 then wlog-using opZ
        -- Then ensure that z + ζ ≥ 0, by applying X if necessary.
        else if l2z * l2zeta <ᵇ 1 then wlog-using opX
        -- If the bias is greater than 2, use the grid operator S.
        else if (q 33971 1000 <ᵇ l2z-minus-zeta) ∨ (l2z-minus-zeta <ᵇ q 29437 1000000)
          then wlog-using (opS-power (round-double (logLambda l2z-minus-zeta Float.÷ 8.0)))
        -- If the skew is below threshold, stop.
        else if skew (matA , matB) ≤ᵇ 15 then nothing
        -- If the bias is greater than 1, apply a shift.
        else if (q 58285 10000 <ᵇ l2z-minus-zeta) ∨ (l2z-minus-zeta <ᵇ q 17157 100000)
          then with-shift (round-double (logLambda l2z-minus-zeta Float.÷ 4.0))
        -- Region R: z ∈ [-0.8, 0.8] and ζ ∈ [-0.8, 0.8].
        else if within l2z (q 24410 100000 , q 40968 10000) ∧ within l2zeta (q 24410 100000 , q 40968 10000)
          then just opR
        -- Region K: b ≥ 0 and z ≤ 0.3 and ζ ≥ 0.8.
        else if (0 ≤ᵇ b) ∧ (l2z ≤ᵇ q 16969 10000) then just opK
        -- Region K•: b ≥ 0 and z ≥ 0.8 and ζ ≤ 0.3.
        else if (0 ≤ᵇ b) ∧ (l2zeta ≤ᵇ q 16969 10000) then just (adj2 opK)
        -- Region Aᵐ: b ≥ 0 and z ≥ 0.3 and ζ ≥ 0.3.
        else if 0 ≤ᵇ b then just (opA-power (lemma-A-l2 l2z l2zeta))
        -- Region Bᵐ: b ≤ 0 and z ≥ -0.2 and ζ ≥ -0.2.
        else just (opB-power (lemma-B-l2 l2z l2zeta))

      with-bl2z : R × R -> R × R -> Maybe (Operator DRootTwo)
      with-bl2z (b , l2z) (beta , l2zeta) = decide b l2z beta l2zeta (l2z ÷ l2zeta)

  step-lemma : OperatorPair R -> Maybe (Operator DRootTwo)
  step-lemma = step-lemma' step-lemma-fuel

  -- Repeatedly apply the Step Lemma to the given state, until the skew
  -- is 15 or less.
  reduction : OperatorPair R -> Operator DRootTwo
  reduction = go reduction-fuel
    where
      go : ℕ -> OperatorPair R -> Operator DRootTwo
      go zero st = 1
      go (suc f) st = next (step-lemma st)
        where
          next : Maybe (Operator DRootTwo) -> Operator DRootTwo
          next nothing = 1
          next (just opG) = opG * go f (action st opG)

  -- Given a pair of ellipses, return a grid operator G such that the
  -- uprightness of each ellipse is greater than 1/6. This is
  -- essentially the same as reduction, except we do not assume that
  -- the input operators have determinant 1.
  to-upright : OperatorPair R -> Operator DRootTwo
  to-upright (a , b) = reduction (scalardiv' a (sqrt (det a)) , scalardiv' b (sqrt (det b)))
    where
      scalardiv' : Operator R -> R -> Operator R
      scalardiv' m x = matrix-map (_÷ x) m

  -- Given a pair of convex sets, return a grid operator G making both
  -- sets upright.
  to-upright-sets : ConvexSet R -> ConvexSet R -> Operator DRootTwo
  to-upright-sets setA setB =
    to-upright (ellipse-operator (convex-ellipse setA) , ellipse-operator (convex-ellipse setB))

  -- ----------------------------------------------------------------------
  -- ** Two-dimensional grid problems: solutions

  -- The 2-dimensional grid problem is the following: given bounded
  -- convex subsets A and B of ℂ with non-empty interior, find all
  -- u ∈ ℤ[ω] such that u ∈ A and u• ∈ B. The scaled version: given
  -- also k ≥ 0, find all u ∈ ℤ[ω] / √2ᵏ such that u ∈ A and u• ∈ B.

  gridprecomp : ConvexSet R -> ConvexSet R -> Operator DRootTwo -> GridPrecomp R
  gridprecomp setA setB opG = mk (special-inverse opG)
    where
      mk2 : ConvexSet R -> ConvexSet R -> GridPrecomp R
      mk2 setA' setB' = GridPrecomp' opG (convex-charfun setA) (convex-charfun setB)
        (convex-intersector setA') (convex-intersector setB') (boundingbox setA') (boundingbox setB')
      mk : Operator DRootTwo -> GridPrecomp R
      mk opG-inv = mk2 (convex-transform opG-inv setA) (convex-transform (adj2 opG-inv) setB)

  -- The solutions of the scaled 2-dimensional grid problem for k,
  -- given the precomputed data.
  gridprecomp-solutions : GridPrecomp R -> ℕ -> List DOmega
  --
  -- (Performance: where-bound values are not shared in compiled Agda
  -- code, so the constants dx = 1/√2ᵏ, dx•, √2ᵏ and 2ᵏ, and the
  -- offsets dtA, dtB are passed as arguments of helper functions.)
  gridprecomp-solutions (GridPrecomp' opG tstA tstB intA' intB' ((x0A , x1A) , (y0A , y1A)) ((x0B , x1B) , (y0B , y1B))) k =
    with-dx (roothalf ^ k)
    where
      with-constants : DRootTwo -> DRootTwo -> DRootTwo -> R -> List DOmega
      with-constants dx dx-bul sqrt2-k two-k =
        for-x0s (List.take 1 (gridpoints-scaled (x0A , x1A + lambda) (x0B , x1B + lambda) (suc k)))
        where
          -- Enumerate the solutions in the x-coordinate, for given β' and x0.
          for-beta' : DRootTwo -> DRootTwo -> List DOmega
          for-beta' beta' x0 = intersect (intA' (x0 , beta') (dx , 0)) (intB' (adj2 x0 , adj2 beta') (dx-bul , 0))
            where
              candidate : DRootTwo -> List DOmega
              candidate alpha'-offs = check (point-transform opG (alpha'-offs * dx + x0 , beta'))
                where
                  -- Convert back to the original coordinate system
                  check : Point DRootTwo -> List DOmega
                  check (alpha , beta) =
                    if tstA (alpha , beta) ∧ tstB (adj2 alpha , adj2 beta)
                    then (fromDRootTwo alpha + i * fromDRootTwo beta) ∷ []
                    else []

              -- dtA, dtB: offsets for slightly fattening the intervals,
              -- in a way that does not add more than a small constant
              -- number of candidates alpha' on both sides of the
              -- interval.
              with-dt : R × R -> R × R -> R -> R -> List DOmega
              with-dt (t0A , t1A) (t0B , t1B) dtA dtB =
                List.concatMap candidate
                  (gridpoints-scaled-parity ((beta' - x0) * sqrt2-k) (t0A - dtA , t1A + dtA) (t0B - dtB , t1B + dtB) 1)

              intersect : Maybe (R × R) -> Maybe (R × R) -> List DOmega
              intersect (just (t0A , t1A)) (just (t0B , t1B)) =
                with-dt (t0A , t1A) (t0B , t1B) (10 ÷ max 10 (two-k * (t1B - t0B))) (10 ÷ max 10 (two-k * (t1A - t0A)))
              intersect _ _ = []

          for-x0s : List DRootTwo -> List DOmega
          for-x0s x0s =
            List.concatMap (λ beta' -> List.concatMap (for-beta' beta') x0s)
              (gridpoints-scaled (fatten-interval (y0A , y1A)) (fatten-interval (y0B , y1B)) (suc k))

      with-dx : DRootTwo -> List DOmega
      with-dx dx = with-constants dx (adj2 dx) (roottwo ^ k) (2 ^ k)

  -- Like gridpoints2-scaled, except that instead of performing a
  -- precomputation, we input the desired grid operator. It must make
  -- the two given sets upright.
  gridpoints2-scaled-with-gridop : ConvexSet R -> ConvexSet R -> Operator DRootTwo -> ℕ -> List DOmega
  gridpoints2-scaled-with-gridop setA setB opG = gridprecomp-solutions (gridprecomp setA setB opG)

  -- Given bounded convex sets A and B, return a function that can
  -- input a k and enumerate all solutions of the two-dimensional
  -- scaled grid problem for A, B, and k. The gridpoints are computed
  -- in some deterministic (but unspecified) order; it is the same
  -- order as in Haskell. A large amount of precomputation is done on
  -- the sets A and B, so use it as: let solver = gridpoints2-scaled A B.
  gridpoints2-scaled : ConvexSet R -> ConvexSet R -> ℕ -> List DOmega
  gridpoints2-scaled setA setB = gridpoints2-scaled-with-gridop setA setB (to-upright-sets setA setB)

  -- Given bounded convex sets A and B, enumerate all solutions u ∈
  -- ℤ[ω] of the 2-dimensional grid problem for A and B.
  gridpoints2 : ConvexSet R -> ConvexSet R -> List DOmega
  gridpoints2 setA setB = gridpoints2-scaled setA setB 0

  -- The k-th entry of gridpoints2-increasing: the solutions for k
  -- (for k ≥ 1 only those with least denominator exponent k).
  gridprecomp-increasing : GridPrecomp R -> ℕ -> List DOmega
  gridprecomp-increasing pc zero = gridprecomp-solutions pc 0
  gridprecomp-increasing pc k@(suc _) = List.filterᵇ (λ z -> denomexp z == k) (gridprecomp-solutions pc k)

  private
    increasing-from : GridPrecomp R -> ℕ -> Stream (ℕ × List DOmega)
    increasing-from pc k .head = k , gridprecomp-increasing pc k
    increasing-from pc k .tail = increasing-from pc (suc k)

  -- Like gridpoints2-increasing, except that instead of performing a
  -- precomputation, we input the desired grid operator. It must make
  -- the two given sets upright.
  gridpoints2-increasing-with-gridop : ConvexSet R -> ConvexSet R -> Operator DRootTwo -> Stream (ℕ × List DOmega)
  gridpoints2-increasing-with-gridop setA setB opG = increasing-from (gridprecomp setA setB opG) 0

  -- Given bounded convex sets A and B, enumerate all solutions of the
  -- two-dimensional scaled grid problem for all k ≥ 0. Each solution
  -- is only enumerated once, and the solutions are enumerated in order
  -- of increasing k. The result is the infinite stream
  --
  --   (0, l0) ∷ (1, l1) ∷ (2, l2) ∷ ...
  --
  -- where l0 is a list of solutions for k=0, l1 is a list of solutions
  -- for k=1, and so on.
  gridpoints2-increasing : ConvexSet R -> ConvexSet R -> Stream (ℕ × List DOmega)
  gridpoints2-increasing setA setB = gridpoints2-increasing-with-gridop setA setB (to-upright-sets setA setB)

  -- The same as a function: gridpoints2-increasing-fun A B k is the
  -- list of the k-th entry of gridpoints2-increasing A B. Partially
  -- apply it to A and B to share the precomputation.
  gridpoints2-increasing-fun : ConvexSet R -> ConvexSet R -> ℕ -> List DOmega
  gridpoints2-increasing-fun setA setB =
    gridprecomp-increasing (gridprecomp setA setB (to-upright-sets setA setB))

-- ----------------------------------------------------------------------
-- * Consuming streams with fuel

-- The first n elements of a stream.
stream-take : {A : Set} -> ℕ -> Stream A -> List A
stream-take zero s = []
stream-take (suc n) s = head s ∷ stream-take n (tail s)

-- The flattened list of candidates [(k, u) | (k, us) ← first n
-- entries, u ← us] of a stream as returned by gridpoints2-increasing.
-- In compiled code the list is computed lazily.
stream-candidates : {A : Set} -> ℕ -> Stream (ℕ × List A) -> List (ℕ × A)
stream-candidates n s = List.concatMap (λ { (k , us) -> List.map (k ,_) us }) (stream-take n s)
