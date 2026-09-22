-- This module is an Agda port of the module
-- Quantum.Synthesis.EuclideanDomain of the Haskell package newsynth
-- (by N. J. Ross and P. Selinger). It provides generic functions for
-- Euclidean domains: division with remainder, and therefore greatest
-- common divisors.
--
-- The Haskell class
--
--   class (Eq a, Ring a) => EuclideanDomain a where
--     rank :: a -> Integer
--     divmod :: a -> a -> (a,a)
--
-- is represented by the classes of the framework (see Typeclasses):
-- Ring, DecEq, Rank (rank : A → ℕ) and DivMod (_/_ and _%_, taking a
-- proof .{{NonZero d}} that the divisor is non-zero). We do not define
-- a bundling record, since its instance fields would overlap with the
-- Ring/DecEq/DivMod/Rank instances. Generic code takes the four
-- instances as separate instance arguments (see the module parameters
-- below).
--
-- Instances:
--
--  * ℤ: DMℤ and Rankℤ from Instances. Note that DMℤ is the Euclidean
--    division of the standard library (remainder ≥ 0), whereas Haskell's
--    divMod rounds the quotient towards -∞ (remainder has the sign of
--    the divisor), and newsynth's rank on Integer is the identity
--    (rank x = x) whereas Rankℤ is ∣x∣. The two divisions agree when
--    the divisor is positive, which is the only case occurring in
--    newsynth's algorithms on integers (in Diophantine, all integer
--    Euclidean computations are on positive numbers); with negative
--    divisors euclid-gcd etc. may differ from newsynth by a sign
--    (i.e. by a unit). Haskell-compatible integer operations _div_,
--    _mod_ and _quot_ are provided below, and are used where results
--    must match (rounddiv, and Diophantine).
--
--  * ℤ[i] = ZComplex = 𝔾: the proven instances of the GauInt modules
--    (g-divmod from GauInt.EucDomain, Rank𝔾 and NZT𝔾 from
--    GauInt.Instances) are reused. Their quotient rounds each
--    component of x·y†/N(y) to a nearest integer, like newsynth, but
--    rounds halves down, whereas newsynth's rounddiv rounds halves up;
--    so quotients/remainders (and hence gcds, up to units) differ from
--    newsynth in tie cases (e.g. divmod 1 2 = (0, 1), newsynth: (1, -1)). The rank is
--    N(y) = ∣y∣², as in newsynth.
--
--  * ℤ[√2] = ZRootTwo and ℤ[ω] = ZOmega: new instances, exactly as in
--    newsynth (rounddiv-based quotient, rank = ∣norm∣, NonZero from
--    decidable equality).
--
-- Partiality and termination: the functions euclid-div and euclid-mod
-- are total; for y = 0 they return 0 and x respectively (Haskell:
-- division by zero error). The recursive algorithms (euclid-gcd,
-- extended-euclid, euclid-extract-power) use fuel derived from the
-- rank, which is sufficient because the rank strictly decreases in
-- each step (for a lawful Euclidean domain); when the fuel runs out
-- (impossible for the instances here) the current value is returned.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.EuclideanDomain where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; is-just)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.DivMod as IDM
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Function.Base using (_∘_)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring

-- Note on instance overlap: Quantum.Synthesis.Ring has generic
-- instances DivMod (A [√2]), DivMod (A [i]), DivMod (A [ω]) and the
-- corresponding NonZeroTypeclass instances, which require {{Fractional
-- A}}. Agda does not discard such a candidate for A = ℤ (although
-- Fractional ℤ does not exist), so the instances for ℤ[√2], ℤ[i] and
-- ℤ[ω] below are marked OVERLAPPING (they are more specific).

-- ----------------------------------------------------------------------
-- * Haskell-compatible integer division

infixl 7 _div_ _mod_ _quot_ _rem_

-- Haskell's divMod on integers: the quotient is rounded towards -∞,
-- and the remainder has the sign of the divisor. Division by 0
-- returns (0, x) (Haskell: error).
divMod : ℤ -> ℤ -> ℤ × ℤ
divMod x y with nonZero? y
... | no _ = 0 , x
... | yes nz = adjust (IDM._/_ x y {{nz}}) (+ IDM._%_ x y {{nz}})
  where
    -- (Note: Agda's "let" is substituted, not shared, so we use
    -- function arguments to share intermediate results.)
    adjust : ℤ -> ℤ -> ℤ × ℤ
    adjust q r = if (y <ᵇ 0) ∧ (r /= 0) then (q - 1 , r + y) else (q , r)

_div_ _mod_ : ℤ -> ℤ -> ℤ
x div y = proj₁ (divMod x y)
x mod y = proj₂ (divMod x y)

-- Haskell's quotRem on integers: the quotient is rounded towards 0,
-- and the remainder has the sign of the dividend. Division by 0
-- returns (0, x).
quotRem : ℤ -> ℤ -> ℤ × ℤ
quotRem x y with divMod x y
... | q , r = if (q <ᵇ 0) ∧ (r /= 0) then (q + 1 , r - y) else (q , r)

_quot_ _rem_ : ℤ -> ℤ -> ℤ
x quot y = proj₁ (quotRem x y)
x rem y = proj₂ (quotRem x y)

-- Haskell's gcd on integers (the result is non-negative). The
-- standard library's gcd builds well-founded recursion proofs, which
-- makes it very slow for large numbers in compiled code, so we use
-- fuel instead (the second argument strictly decreases).
gcd : ℤ -> ℤ -> ℤ
gcd a b = + go (suc Int.∣ b ∣) Int.∣ a ∣ Int.∣ b ∣
  where
    go : ℕ -> ℕ -> ℕ -> ℕ
    go _ m zero = m
    go zero m _ = m
    go (suc fuel) m n@(suc _) = go fuel n (m Nat.% n)

-- Haskell's even and odd on integers.
even odd : ℤ -> Bool
even = evenℤ
odd = not ∘ evenℤ

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- For y ≠ 0, find the integer q closest to x / y. This works
-- regardless of whether x and/or y are positive or negative. The
-- distance q − x / y is guaranteed to be in (-1/2, 1/2]. (For y = 0,
-- the result is 0.)
rounddiv : ℤ -> ℤ -> ℤ
rounddiv x y = (x + y quot 2) div y


-- ----------------------------------------------------------------------
-- * Particular Euclidean domains

-- ℤ[√2]. The division rounds the coefficients of x·y•/N(y). (For
-- y = 0, the quotient is 0 and the remainder is x.)
-- (Intermediate results are passed as function arguments, since
-- where-bound values are not shared in compiled code.)
divmod-ZRootTwo : ZRootTwo -> ZRootTwo -> ZRootTwo × ZRootTwo
divmod-ZRootTwo x y = with-k (x * adj2 y) (norm y)
  where
    with-q : ZRootTwo -> ZRootTwo × ZRootTwo
    with-q q = q , x - y * q
    with-k : ZRootTwo -> ℤ -> ZRootTwo × ZRootTwo
    with-k (RootTwo l m) k = with-q (RootTwo (rounddiv l k) (rounddiv m k))

-- ℤ[ω]. The division rounds the coefficients of
-- x·y†·(y·y†)• / N(y). (For y = 0, the quotient is 0 and the
-- remainder is x.)
divmod-ZOmega : ZOmega -> ZOmega -> ZOmega × ZOmega
divmod-ZOmega x y = with-k (x * adj y * adj2 (y * adj y)) (norm y)
  where
    with-q : ZOmega -> ZOmega × ZOmega
    with-q q = q , x - y * q
    with-k : ZOmega -> ℤ -> ZOmega × ZOmega
    with-k (Omega a' b' c' d') k =
      with-q (Omega (rounddiv a' k) (rounddiv b' k) (rounddiv c' k) (rounddiv d' k))

instance
  NonZeroZRootTwo : NonZeroTypeclass ZRootTwo
  NonZeroZRootTwo = nonZeroTypeclass-from-eq 0

  DivModZRootTwo : DivMod ZRootTwo
  DivModZRootTwo .NZT = NonZeroZRootTwo
  DivModZRootTwo ._/_ x y = proj₁ (divmod-ZRootTwo x y)
  DivModZRootTwo ._%_ x y = proj₂ (divmod-ZRootTwo x y)

  RankZRootTwo : Rank ZRootTwo
  RankZRootTwo .rank x = Int.∣ norm x ∣

  NonZeroZOmega : NonZeroTypeclass ZOmega
  NonZeroZOmega = nonZeroTypeclass-from-eq 0

  DivModZOmega : DivMod ZOmega
  DivModZOmega .NZT = NonZeroZOmega
  DivModZOmega ._/_ x y = proj₁ (divmod-ZOmega x y)
  DivModZOmega ._%_ x y = proj₂ (divmod-ZOmega x y)

  RankZOmega : Rank ZOmega
  RankZOmega .rank x = Int.∣ norm x ∣

{-# OVERLAPPING NonZeroZRootTwo DivModZRootTwo NonZeroZOmega DivModZOmega #-}

-- ℤ[i] = 𝔾: the Euclidean structure proven in GauInt. The instances
-- g-divmod and NZT𝔾 of GauInt are re-exported as OVERLAPPING
-- instances (with the same values); the original names are kept out
-- of scope, so that there is only one candidate of each type. (Note
-- that GauInt.EucDomain does not export its own DivMod instance for
-- ℤ, so importing it does not clash with DMℤ.)
module GaussianIntegers where
  import GauInt.EucDomain as GE
  import GauInt.Instances as GI
  instance
    DivModZComplex : DivMod ZComplex
    DivModZComplex = GE.g-divmod

    NonZeroZComplex : NonZeroTypeclass ZComplex
    NonZeroZComplex = GI.NZT𝔾
  {-# OVERLAPPING DivModZComplex NonZeroZComplex #-}
open GaussianIntegers public using (DivModZComplex ; NonZeroZComplex)

import GauInt.Instances hiding (NZT𝔾)
-- The rank N(x) of GauInt, and the NonZero proofs for literals of GauInt.
open GauInt.Instances public using (Rank𝔾 ; nzp ; nzn ; nzpi ; nzni)

-- ----------------------------------------------------------------------
-- * Functions

module _ {A : Set} {{_ : Ring A}} {{_ : DecEq A}} {{_ : DivMod A}} {{_ : Rank A}} where
  open LiteralsFor A

  -- Given a and b ≠ 0, return a quotient and remainder for division
  -- of a by b. Specifically, return (q,r) such that a = qb + r, and
  -- such that r = 0 or rank(r) < rank(b).
  divmod : (x y : A) .{{_ : NonZero y}} -> A × A
  divmod x y = x / y , x % y

  -- Calculate the remainder for the division of x by y. For y = 0,
  -- return x.
  euclid-mod : A -> A -> A
  euclid-mod x y with nonZero? y
  ... | yes nz = _%_ x y {{nz}}
  ... | no _ = x

  -- Calculate the quotient for the division of x by y, ignoring the
  -- remainder, if any. This is typically, but not always, used in
  -- situations where the remainder is known to be 0 ahead of time.
  -- For y = 0, return 0.
  euclid-div : A -> A -> A
  euclid-div x y with nonZero? y
  ... | yes nz = _/_ x y {{nz}}
  ... | no _ = 0

  -- Calculate the greatest common divisor in any Euclidean domain.
  euclid-gcd : A -> A -> A
  euclid-gcd x y = go (suc (rank y)) x y
    where
      go : ℕ -> A -> A -> A
      go zero x y = x
      go (suc f) x y with nonZero? y
      ... | no _ = x
      ... | yes nz = go f y (_%_ x y {{nz}})

  -- Perform the extended Euclidean algorithm. On inputs x and y, this
  -- returns (a,b,s,t,d) such that:
  --
  --  * d = gcd(x,y),
  --  * ax + by = d,
  --  * sx + ty = 0,
  --  * at - bs = 1.
  extended-euclid : A -> A -> A × A × A × A × A
  extended-euclid x y = go (suc (rank y)) x y
    where
      go : ℕ -> A -> A -> A × A × A × A × A
      go zero x y = 1 , 0 , 0 , 1 , x
      go (suc f) x y with nonZero? y
      ... | no _ = 1 , 0 , 0 , 1 , x
      ... | yes nz with go f y (_%_ x y {{nz}}) | _/_ x y {{nz}}
      ...   | a' , b' , s' , t' , d | q = b' , a' - b' * q , - t' , t' * q - s' , d

  -- Find the inverse of a unit in a Euclidean domain. If the given
  -- element is not a unit, return nothing.
  euclid-inverse : A -> Maybe A
  euclid-inverse x with nonZero? x
  ... | no _ = nothing
  ... | yes nz = if _%_ 1 x {{nz}} == 0 then just (_/_ 1 x {{nz}}) else nothing

  -- Determine whether an element of a Euclidean domain is a unit.
  is-unit : A -> Bool
  is-unit = is-just ∘ euclid-inverse

  -- Compute the inverse of a in R/(p), where R is a Euclidean domain.
  -- Note: this works whenever a and p are relatively prime. If a and
  -- p are not relatively prime, return nothing.
  inv-mod : A -> A -> Maybe A
  inv-mod p a with extended-euclid a p
  ... | b , _ , _ , _ , d with euclid-inverse d
  ...   | just d' = just (euclid-mod (b * d') p)
  ...   | nothing = nothing

  -- Check whether a is a divisor of b.
  euclid-divides : A -> A -> Bool
  euclid-divides a b with nonZero? a
  ... | no _ = b == 0
  ... | yes nz = _%_ b a {{nz}} == 0

  -- Check whether a and b are associates, i.e., differ at most by a
  -- multiplicative unit.
  euclid-associates : A -> A -> Bool
  euclid-associates a b = euclid-divides a b ∧ euclid-divides b a

  -- Given elements x and y of a Euclidean domain, find the largest k
  -- such that x can be written as yᵏz. Return the pair (k, z). If
  -- x = 0 or y is a unit, return (0, x).
  euclid-extract-power : A -> A -> ℕ × A
  euclid-extract-power x y = go (suc (rank x)) x
    where
      go : ℕ -> A -> ℕ × A
      go zero x = 0 , x
      go (suc f) x =
        if x == 0 then (0 , x)
        else if is-unit y then (0 , x)
        else if euclid-divides y x then
          map₁ suc (go f (euclid-div x y))
        else (0 , x)
