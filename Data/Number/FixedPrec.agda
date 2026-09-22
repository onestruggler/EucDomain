-- This module is an Agda port of the module Data.Number.FixedPrec of
-- the Haskell package fixedprec-0.2.2.2 (by P. Selinger): a
-- reasonably efficient implementation of arbitrary-but-fixed
-- precision real numbers.
--
-- A fixed-precision number of precision e is represented by an
-- integer n, standing for the real number n⋅10⁻ᵉ. In Haskell the
-- precision is a type (P0, P10, PPlus3 e, ...); here it is simply a
-- natural number term, so that
--
--   FixedPrec : ℕ → Set
--
-- and e.g. FixedPrec 100 has 100 decimal digits after the decimal
-- point. Everything is computed with integer arithmetic on the scaled
-- values (ℕ and ℤ are compiled to GHC's Integer), with exactly the
-- same algorithms and rounding as the Haskell code, so results agree
-- digit for digit.
--
-- Deviations from Haskell (all documented at the definitions):
--
-- * Partial functions are total: division by zero gives 0, log x = 0
--   for x ≤ 0, sqrt x = 0 for x < 0, asin/acos/acosh outside their
--   domain give 0 (Haskell: error).
-- * The NonZero predicate of FixedPrec is trivial (like for Float),
--   so that one can divide without proofs; see the previous item.
-- * Unbounded recursions (power series, Newton iterations, domain
--   reductions) take fuel. The fuel is always generous enough that it
--   never runs out on legal inputs.
-- * All of Haskell's Floating methods (including **, logBase, sinh, cosh,
--   tanh, asinh, acosh, atanh) are fields of the framework's Floating
--   class.

{-# OPTIONS --without-K --safe #-}

module Data.Number.FixedPrec where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Show as IntS
import Data.Sign.Base as Sign
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable.Core using (map′)

open import Instances
open import Literals
open import Quantum.Synthesis.Random using (Random ; randomR ; random ; RandomGen)

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- These are not exported by the Haskell module; here they live in the
-- sub-module Aux (use Data.Number.FixedPrec.Aux.intsqrt etc.).
module Aux where

  -- ----------------------------------------------------------------------
  -- ** Integer functions

  -- The natural number part of an integer (negative numbers ↦ 0).
  toℕ⁺ : ℤ -> ℕ
  toℕ⁺ (+ n) = n
  toℕ⁺ -[1+ _ ] = 0

  odd : ℕ -> Bool
  odd n = n Nat.% 2 Nat.≡ᵇ 1

  evenℤ : ℤ -> Bool
  evenℤ a = not (odd Int.∣ a ∣)

  -- Division on ℕ, with n / 0 = 0.
  divN : ℕ -> ℕ -> ℕ
  divN a zero = 0
  divN a (suc b) = a Nat./ suc b

  -- Haskell's div (rounding towards -∞). Division by 0 gives 0.
  divℤ : ℤ -> ℤ -> ℤ
  divℤ a (+ zero) = 0
  divℤ a (+ suc n) = Int._/ℕ_ a (suc n)
  divℤ a -[1+ n ] = Int._/ℕ_ (Int.- a) (suc n)

  -- Haskell's mod (the sign of the divisor).
  modℤ : ℤ -> ℤ -> ℤ
  modℤ a b = a Int.- b Int.* divℤ a b

  -- Haskell's quot (rounding towards 0). Division by 0 gives 0.
  quotℤ : ℤ -> ℤ -> ℤ
  quotℤ a b with Int.∣ b ∣
  ... | zero = 0
  ... | suc d = (Int.sign a Sign.* Int.sign b) Int.◃ (Int.∣ a ∣ Nat./ suc d)

  -- Haskell's rem (the sign of the dividend).
  remℤ : ℤ -> ℤ -> ℤ
  remℤ a b = a Int.- b Int.* quotℤ a b

  -- b ^ n by repeated squaring (the first argument of go is fuel).
  powℤ : ℤ -> ℕ -> ℤ
  powℤ b n = go n b n 1
    where
      go : ℕ -> ℤ -> ℕ -> ℤ -> ℤ
      go zero _ _ acc = acc
      go (suc f) b zero acc = acc
      go (suc f) b n@(suc _) acc =
        go f (b Int.* b) (n Nat./ 2) (if odd n then acc Int.* b else acc)

  powℕ : ℕ -> ℕ -> ℕ
  powℕ b n = Int.∣ powℤ (+ b) n ∣

  -- 10ⁿ. Since it is needed in almost every operation on FixedPrec
  -- numbers (every product, quotient and literal), it is computed as
  -- 10^(n mod 64) ⋅ 10^(64⋅⌊n/64⌋) from two tables, which are top-level
  -- constants and hence computed only once in compiled code (for n ≥
  -- 4096, by repeated squaring).
  pow10-table : ℤ -> List ℤ
  pow10-table b = go 64 1
    where
      go : ℕ -> ℤ -> List ℤ
      go zero _ = []
      go (suc k) x = x ∷ go k (x Int.* b)

  -- [10⁰, 10¹, ..., 10⁶³] and [10⁰, 10⁶⁴, ..., 10^(64⋅63)].
  pow10-small pow10-big : List ℤ
  pow10-small = pow10-table 10
  pow10-big = pow10-table (powℤ 10 64)

  private
    index : List ℤ -> ℕ -> ℤ
    index [] _ = 1
    index (x ∷ _) zero = x
    index (_ ∷ xs) (suc k) = index xs k

  pow10 : ℕ -> ℤ
  pow10 n =
    if n Nat.<ᵇ 4096 then index pow10-small (n Nat.% 64) Int.* index pow10-big (n Nat./ 64)
    else powℤ 10 n

  -- Integer division with rounding to the closest. Note: rounding
  -- could be improved. Right now, we always round up in case of a tie.
  divi : ℤ -> ℤ -> ℤ
  divi a b = divℤ (a Int.+ divℤ b 2) b

  -- Shift the integer to the right by the given number of decimal
  -- digits, with rounding.
  decshiftR : ℕ -> ℤ -> ℤ
  decshiftR n x = divi x (pow10 n)

  -- Shift the integer to the right by the given number of decimal
  -- digits, without rounding (i.e., truncate).
  dectruncR : ℕ -> ℤ -> ℤ
  dectruncR n x = quotℤ x (pow10 n)

  -- Shift the integer to the left by the given number of decimal
  -- digits.
  decshiftL : ℕ -> ℤ -> ℤ
  decshiftL n x = x Int.* pow10 n

  -- Return 1 + the position of the leftmost "1" bit of a natural
  -- number, i.e., its number of binary digits. We strip 64 bits at a
  -- time, which is fast enough for numbers of thousands of digits.
  hibit : ℕ -> ℕ
  hibit n = go n n
    where
      small : ℕ -> ℕ -> ℕ
      small zero _ = 0
      small (suc f) zero = 0
      small (suc f) m@(suc _) = suc (small f (m Nat./ 2))

      go : ℕ -> ℕ -> ℕ
      go zero m = 0
      go (suc f) m =
        if m Nat.<ᵇ 18446744073709551616 then small 65 m
        else go f (m Nat./ 18446744073709551616) Nat.+ 64

  -- For n ≥ 0, return the floor of the square root of n. This is done
  -- using integer arithmetic (Newton's method), so there are no
  -- rounding errors. For n ≤ 0, return 0.
  intsqrt : ℤ -> ℤ
  intsqrt (+ zero) = 0
  intsqrt -[1+ _ ] = 0
  intsqrt (+ n@(suc _)) = + start (hibit n)
    where
      -- (Intermediate values are passed as arguments, since let/where
      -- bindings are not shared in compiled code.)
      check : ℕ -> ℕ -> ℕ -> ℕ
      iter : ℕ -> ℕ -> ℕ
      iter zero m = m
      iter (suc f) m = check f m (m Nat.* m)
      check f m m-sq =
        if (m-sq Nat.≤ᵇ n) ∧ (n Nat.<ᵇ m-sq Nat.+ 2 Nat.* m Nat.+ 1) then m
        else iter f ((m Nat.+ divN n m) Nat./ 2)

      start : ℕ -> ℕ
      start h = iter (h Nat.+ 10) (powℕ 2 (h Nat./ 2))

  -- Find the ceiling of the larger solution of a quadratic equation.
  -- Specifically, given the polynomial p(x) = x² + bx + c, where b and
  -- c are integers, find the smallest integer x ≥ -b/2 satisfying
  -- p(x) ≥ 0, if b² - 4c ≥ 0 (otherwise return nothing).
  --
  -- This is done using integer arithmetic, so there are no rounding
  -- errors. It generalizes intsqrt.
  intquad : ℤ -> ℤ -> Maybe ℤ
  intquad b c =
    if disc <ᵇ 0 then nothing
    else if 0 ≤ᵇ x1 * x1 + b * x1 + c then just x1
    else just (iter (h Nat.+ 10) x0)
    where
      disc = b * b - 4 * c
      h = hibit (toℕ⁺ disc)
      x1 = - divℤ b 2
      x0 = x1 + powℤ 2 (h Nat./ 2)
      iter : ℕ -> ℤ -> ℤ
      iter zero x = x + 1
      iter (suc f) x =
        let px = x * x + b * x + c in
        if (px ≤ᵇ 0) ∧ (0 <ᵇ px + 2 * x + 1 + b) then x + 1
        else iter f (divℤ (x * x - c) (2 * x + b))

  -- ----------------------------------------------------------------------
  -- ** Other general-purpose functions

  -- Division in a generic field, returning 0 when dividing by 0.
  divide : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} -> A -> A -> A
  divide x y with nonZero? y
  ... | yes nz = _/_ x y {{nz}}
  ... | no _ = 0#

  -- Given b > 1 and x > 0, return (n, r) such that x = r bⁿ and
  -- 1 ≤ r < b. In other words, let n = ⌊log_b x⌋ and r = x b⁻ⁿ. For
  -- x ≤ 0 (Haskell: error) return (0, x). The recursion squares b at
  -- each level; 64 levels of fuel suffice for any practical input.
  floorlog : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : DecOrd A}} -> A -> A -> ℤ × A
  floorlog {A} b x = go 64 b
    where
      go : ℕ -> A -> ℤ × A
      go zero b = 0 , x
      go (suc f) b =
        if x ≤ᵇ 0# then (0 , x)
        else if (1# ≤ᵇ x) ∧ (x <ᵇ b) then (0 , x)
        else if (1# ≤ᵇ x * b) ∧ (x <ᵇ 1#) then (-1 , b * x)
        else rest (go f (b * b))
        where
          rest : ℤ × A -> ℤ × A
          rest (n , r) = if r <ᵇ b then (2 * n , r) else (2 * n + 1 , divide r b)

  -- Haskell's (^) (from GHC.Real), which uses repeated squaring. For
  -- inexact types such as FixedPrec, the rounding differs from the
  -- framework's _^_ (which multiplies n times), so we provide it for
  -- faithful ports of Haskell code.
  ghc-power : {A : Set} {{_ : SemiRing A}} -> A -> ℕ -> A
  ghc-power x zero = 1#
  ghc-power {A} x n@(suc _) = pow n x n
    where
      -- the first argument is fuel.
      pow-acc : ℕ -> A -> ℕ -> A -> A
      pow-acc zero x y z = x * z
      pow-acc (suc f) x y z =
        if not (odd y) then pow-acc f (x * x) (y Nat./ 2) z
        else if y Nat.≡ᵇ 1 then x * z
        else pow-acc f (x * x) (y Nat./ 2) (x * z)

      pow : ℕ -> A -> ℕ -> A
      pow zero x y = x
      pow (suc f) x y =
        if not (odd y) then pow f (x * x) (y Nat./ 2)
        else if y Nat.≡ᵇ 1 then x
        else pow-acc f (x * x) (y Nat./ 2) x

open Aux

-- ----------------------------------------------------------------------
-- * Precision

-- The precision, measured in decimal digits. In Haskell this is a
-- type class of type-level integers; here it is a natural number.
Precision : Set
Precision = ℕ

-- Get the precision, in decimal digits.
digits : Precision -> ℕ
digits e = e

P0 P1 P10 P100 P1000 P2000 : Precision
P0 = 0
P1 = 1
P10 = 10
P100 = 100
P1000 = 1000
P2000 = 2000

-- Add digits to a precision. PPlus3 is used for the internal
-- calculations of the analytic functions; it is written with suc
-- so that unification sees through it.
PPlus1 PPlus3 PPlus10 PPlus100 PPlus1000 : Precision -> Precision
PPlus1 e = suc e
PPlus3 e = suc (suc (suc e))
PPlus10 e = e Nat.+ 10
PPlus100 e = e Nat.+ 100
PPlus1000 e = e Nat.+ 1000

-- ----------------------------------------------------------------------
-- * Fixed-precision numbers

-- The value F n of type FixedPrec e represents the real number n⋅10⁻ᵉ.
record FixedPrec (e : Precision) : Set where
  constructor F
  field
    unF : ℤ
open FixedPrec public

-- Get the precision of a fixed-precision number, in decimal digits.
getprec : {e : Precision} -> FixedPrec e -> ℕ
getprec {e} _ = e

-- ----------------------------------------------------------------------
-- ** Static and dynamic casts

-- Cast from any FixedPrec type to another (rounding to the closest).
cast : {e f : Precision} -> FixedPrec e -> FixedPrec f
cast {e} {f} (F x) =
  if f Nat.≤ᵇ e then F (decshiftR (e Nat.∸ f) x) else F (decshiftL (f Nat.∸ e) x)

-- Cast to a fixed-point type with three additional digits of accuracy.
upcast : {e : Precision} -> FixedPrec e -> FixedPrec (PPlus3 e)
upcast = cast

-- Cast to a fixed-point type with three fewer digits of accuracy.
downcast : {e : Precision} -> FixedPrec (PPlus3 e) -> FixedPrec e
downcast = cast

-- with-added-digits d f x evaluates f(x), adding d digits of accuracy
-- to x during the computation (no digits if d ≤ 0).
with-added-digits : {A : Set} {f : Precision} -> ℤ -> ({e : Precision} -> FixedPrec e -> A) -> FixedPrec f -> A
with-added-digits {f = f} d g x = g {f Nat.+ toℕ⁺ d} (cast x)

-- ----------------------------------------------------------------------
-- ** Some primitive operations

infixl 7 _*ℤ_ _/ℤ_

-- Multiply an integer by a fixed-precision number (Haskell: ..*).
_*ℤ_ : {e : Precision} -> ℤ -> FixedPrec e -> FixedPrec e
n *ℤ F x = F (n Int.* x)

-- Divide a fixed-precision number by an integer (rounding to the
-- closest) (Haskell: /..).
_/ℤ_ : {e : Precision} -> FixedPrec e -> ℤ -> FixedPrec e
F x /ℤ n = F (divi x n)

-- Return the positive fractional part of a fixed-precision number.
-- The result is always in [0,1), regardless of the sign of the input.
fractional : {e : Precision} -> FixedPrec e -> FixedPrec e
fractional {e} (F x) = F (modℤ x (pow10 e))

-- The rational number a/d (d > 0) at precision e, rounded to the
-- closest. This is Haskell's fromRational (which computes
-- fromInteger a / fromInteger d; both round a⋅10ᵉ/d to the closest,
-- ties up).
fromRat : {e : Precision} -> ℤ -> ℕ -> FixedPrec e
fromRat {e} a d = F (divi (a Int.* pow10 e) (+ d))

-- ----------------------------------------------------------------------
-- ** Instances

module _ {e : Precision} where
  instance
    SemiRingFixedPrec : SemiRing (FixedPrec e)
    SemiRingFixedPrec ._+_ (F x) (F y) = F (x Int.+ y)
    SemiRingFixedPrec ._*_ (F x) (F y) = F (decshiftR e (x Int.* y))
    SemiRingFixedPrec .0# = F 0
    SemiRingFixedPrec .1# = F (pow10 e)
    SemiRingFixedPrec .fromℕ n = F (decshiftL e (+ n))

    RingFixedPrec : Ring (FixedPrec e)
    RingFixedPrec .sra = SemiRingFixedPrec
    RingFixedPrec .-_ (F x) = F (Int.- x)

    NumberFixedPrec : Number (FixedPrec e)
    NumberFixedPrec = number-from-semiring

    NegativeFixedPrec : Negative (FixedPrec e)
    NegativeFixedPrec = negative-from-ring

    DecEqFixedPrec : DecEq (FixedPrec e)
    DecEqFixedPrec ._≟_ (F x) (F y) = map′ (cong F) (cong unF) (x ≟ y)

    DecOrdFixedPrec : DecOrd (FixedPrec e)
    DecOrdFixedPrec ._≤_ x y = unF x Int.≤ unF y
    DecOrdFixedPrec ._≤?_ x y = unF x ≤? unF y
    DecOrdFixedPrec ._<_ x y = unF x Int.< unF y
    DecOrdFixedPrec ._<?_ x y = unF x <? unF y

    -- The NonZero predicate is trivial, like for Float: division by
    -- zero is allowed and gives 0 (Haskell: an exception).
    NonZeroFixedPrec : NonZeroTypeclass (FixedPrec e)
    NonZeroFixedPrec = nonZeroTypeclass-trivial

    -- FixedPrec is a (approximate) field: _%_ is always 0.
    DivModFixedPrec : DivMod (FixedPrec e)
    DivModFixedPrec .NZT = NonZeroFixedPrec
    DivModFixedPrec ._/_ (F x) (F y) = F (divi (pow10 e Int.* x) y)
    DivModFixedPrec ._%_ _ _ = F 0

    FractionalFixedPrec : Fractional (FixedPrec e)
    FractionalFixedPrec .DM = DivModFixedPrec
    FractionalFixedPrec ._⁻¹ (F y) = F (divi (pow10 e Int.* pow10 e) y)
    FractionalFixedPrec .fromℚ q = fromRat (Rat.↥ q) (Rat.↧ₙ q)

    -- toRational: the exact rational value x/10ᵉ.
    ToRationalFixedPrec : ToRational (FixedPrec e)
    ToRationalFixedPrec .toℚ (F x) = ratio x (powℕ 10 e)
      where
        ratio : ℤ -> ℕ -> ℚ
        ratio a zero = Rat.0ℚ
        ratio a (suc n) = a Rat./ suc n

-- Printing, as in Haskell: e.g. "-3.1416" at precision 4, "5.0" at
-- precision 0. The precedence is ignored (Haskell's Show instance
-- only defines show), so negative numbers are never parenthesized.
show-FixedPrec : {e : Precision} -> FixedPrec e -> String
show-FixedPrec {e} (F x) = sign ++ integral ++ "." ++ frac
  where
    x' = + Int.∣ x ∣
    sign = if x <ᵇ 0 then "-" else ""
    integral = IntS.show (dectruncR e x')
    frac' = IntS.show (modℤ x' (pow10 e))
    frac = String.fromList (List.replicate (e Nat.∸ String.length frac') '0') ++ frac'

instance
  ShowFixedPrec : {e : Precision} -> Show (FixedPrec e)
  ShowFixedPrec .showsPrec _ = show-FixedPrec

-- ----------------------------------------------------------------------
-- ** RealFrac: properFraction, truncate, round, ceiling, floor

module _ {e : Precision} where

  -- properFraction x = (n, r) with x = n + r, where n is x truncated
  -- towards 0, and r has the same sign as x.
  properFraction : FixedPrec e -> ℤ × FixedPrec e
  properFraction (F x) = quotℤ x (pow10 e) , F (remℤ x (pow10 e))

  truncate : FixedPrec e -> ℤ
  truncate x = proj₁ (properFraction x)

  -- Haskell's default round: to the nearest integer, ties to even.
  round : FixedPrec e -> ℤ
  round x with properFraction x
  ... | n , r =
    if d <ᵇ 0# then n
    else if d == 0# then (if evenℤ n then n else m)
    else m
    where
      m = if r <ᵇ 0# then n - 1 else n + 1
      d = abs r - fromRat 1 2

  ceiling : FixedPrec e -> ℤ
  ceiling x with properFraction x
  ... | n , r = if 0# <ᵇ r then n + 1 else n

  floor : FixedPrec e -> ℤ
  floor x with properFraction x
  ... | n , r = if r <ᵇ 0# then n - 1 else n

instance
  FloorFixedPrec : {e : Precision} -> Floor (FixedPrec e)
  FloorFixedPrec .floor-of = floor
  FloorFixedPrec .ceiling-of = ceiling

-- ----------------------------------------------------------------------
-- ** Other operations

-- Solve the quadratic equation x² + bx + c = 0 with maximal possible
-- precision, using a numerically stable method. Return the pair
-- (x1, x2) of solutions with x1 ≤ x2, or nothing if no solution
-- exists.
--
-- Haskell computes b' = floor (b * 10^p), c' = floor (c * 100^p)
-- with p = e + 3, and returns fromInteger x / 10^p. All these
-- operations are exact, so we compute them directly on the scaled
-- integers (same results).
solve-quadratic : {e : Precision} -> FixedPrec e -> FixedPrec e -> Maybe (FixedPrec e × FixedPrec e)
solve-quadratic {e} (F b) (F c) with intquad (b Int.* 1000) (c Int.* pow10 (e Nat.+ 6))
... | nothing = nothing
... | just x2' = just (F (divi (Int.- (b Int.* 1000) Int.- x2') 1000) , F (divi x2' 1000))

-- ----------------------------------------------------------------------
-- ** Power series

-- A power series is given by its sequence of rational coefficients
-- (numerator, positive denominator), produced from a state s by
-- coef and next. The series stops when the next coefficient is
-- smaller than the precision (rounds to 0). This is accurate for
-- alternating and decreasing series, provided |x| ≤ 1. Evaluated like
-- Haskell: h₀ + x(h₁ + x(h₂ + ...)).
powerseries : {e : Precision} {S : Set} -> (S -> ℤ × ℕ) -> (S -> S) -> S -> ℕ -> FixedPrec e -> FixedPrec e
powerseries coef next s zero x = 0
powerseries {e} coef next s (suc fuel) x =
  let h = coefficient (coef s) in
  if unF h == 0 then h else h + x * powerseries coef next (next s) fuel x
  where
    coefficient : ℤ × ℕ -> FixedPrec e
    coefficient (a , d) = fromRat a d

-- Enough terms for all the series below (they need at most about 2e
-- terms, where e is the precision).
series-fuel : Precision -> ℕ
series-fuel e = e Nat.* 4 Nat.+ 100

-- The coefficients of Haskell's "accs f = scanl f 1 [1..]": the state
-- is (n, aₙ), with a₀ = 1 and aₙ = f aₙ₋₁ n.
accs-series : {e : Precision} -> (ℤ × ℕ -> ℕ -> ℤ × ℕ) -> FixedPrec e -> FixedPrec e
accs-series {e} f = powerseries proj₂ (λ { (n , a) -> suc n , f a (suc n) }) (0 , (1 , 1)) (series-fuel e)

-- The coefficients 1/(qⁿ(2n+k)) for n = 0, 1, ...; the state is (n, qⁿ).
geometric-series : {e : Precision} -> ℤ -> ℕ -> ℕ -> FixedPrec e -> FixedPrec e
geometric-series {e} q a k = powerseries coef (λ { (n , p) -> suc n , p Int.* q }) (0 , 1) (series-fuel e)
  where
    coef : ℕ × ℤ -> ℤ × ℕ
    coef (n , p) = (Int.sign p Int.◃ 1) , Int.∣ p ∣ Nat.* (a Nat.* n Nat.+ k)

-- ----------------------------------------------------------------------
-- ** Limited domain implementations

-- The following are implementations of various analytic functions by
-- power series. These implementations have limited domain, and do
-- not compensate for round-off errors.

module _ {e : Precision} where

  -- The Taylor series for sin x, centered at 0. Works for |x| ≤ 1.
  sin-p : FixedPrec e -> FixedPrec e
  sin-p x = x * accs-series (λ { (a , d) n -> Int.- a , d Nat.* (2 Nat.* n Nat.* (2 Nat.* n Nat.+ 1)) }) (x * x)

  -- The Taylor series for cos x, centered at 0. Works for |x| ≤ 1.
  cos-p : FixedPrec e -> FixedPrec e
  cos-p x = accs-series (λ { (a , d) n -> Int.- a , d Nat.* (2 Nat.* n Nat.* (2 Nat.* n Nat.∸ 1)) }) (x * x)

  -- The Taylor series for exp x, centered at 0. Works for |x| ≤ 1.
  exp-p : FixedPrec e -> FixedPrec e
  exp-p x = accs-series (λ { (a , d) n -> a , d Nat.* n }) x

  -- The Taylor series for log x, centered at 1. Works for |x - 1| ≤ 1/4.
  -- Coefficients 1/((-4)ⁿ(n+1)).
  log-p : FixedPrec e -> FixedPrec e
  log-p x = (x - 1) * geometric-series -4 1 1 (4 *ℤ (x - 1))

  -- The Taylor series for atan x, centered at 0. Works for |x| ≤ 0.44.
  -- Coefficients 1/((-5)ⁿ(2n+1)).
  atan-p : FixedPrec e -> FixedPrec e
  atan-p x = x * geometric-series -5 2 1 (5 *ℤ x * x)

  -- Like atan-p, for |x| ≤ 0.2, and faster in that range.
  atan-p2 : FixedPrec e -> FixedPrec e
  atan-p2 x = x * geometric-series -25 2 1 (25 *ℤ x * x)

  -- Like atan-p, for |x| ≤ 1/239, and faster in that range.
  atan-p3 : FixedPrec e -> FixedPrec e
  atan-p3 x = x * geometric-series -57121 2 1 (57121 *ℤ x * x)

-- ----------------------------------------------------------------------
-- ** Raw versions of analytic functions

-- The following functions are "raw", in the sense that they do not
-- try to compensate for accumulated round-off errors. The *-fp
-- versions (which are the Floating methods) wrap them in upcast and
-- downcast, as in Haskell. Functions that call each other
-- recursively at increasing precision take fuel (the default fuel is
-- far more than needed).

default-fuel : ℕ
default-fuel = 20

-- Raw implementation of π.
pi-raw : {e : Precision} -> FixedPrec e
pi-raw = 16 *ℤ atan-p2 (1 / 5) - 4 *ℤ atan-p3 (1 / 239)

pi-fp : {e : Precision} -> FixedPrec e
pi-fp = downcast pi-raw

-- Raw implementation of the square root. For x < 0 (Haskell: error)
-- return 0.
sqrt-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
sqrt-raw {e} (F x) = if 0 ≤ᵇ x then F (intsqrt (x Int.* pow10 e)) else F 0

sqrt-fp : {e : Precision} -> FixedPrec e -> FixedPrec e
sqrt-fp x = downcast (sqrt-raw (upcast x))

-- Raw implementation of the sine function.
sin-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
sin-raw x =
  if (-1 ≤ᵇ x) ∧ (x <ᵇ 1) then sin-p x -- bypass slow domain reduction
  else if m == 0 then sin-p x'
  else if m == 1 then cos-p x'
  else if m == 2 then - sin-p x'
  else - cos-p x'
  where
    p2 = pi-fp /ℤ 2
    n = round (x / p2)
    m = modℤ n 4
    x' = x - n *ℤ p2

-- Raw implementation of the cosine function.
cos-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
cos-raw x =
  if (-1 ≤ᵇ x) ∧ (x <ᵇ 1) then cos-p x -- bypass slow domain reduction
  else if m == 0 then cos-p x'
  else if m == 1 then - sin-p x'
  else if m == 2 then - cos-p x'
  else sin-p x'
  where
    p2 = pi-fp /ℤ 2
    n = round (x / p2)
    m = modℤ n 4
    x' = x - n *ℤ p2

-- Raw implementation of the exponential function. Note: the loss of
-- precision is much more substantial than that of the other raw
-- functions. The halving recursion is bounded by the size of x.
exp-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
exp-raw x = go (Int.∣ unF x ∣) x
  where
    go : {e : Precision} -> ℕ -> FixedPrec e -> FixedPrec e
    go zero x = exp-p x
    go (suc f) x = if (-1 ≤ᵇ x) ∧ (x ≤ᵇ 1) then exp-p x else (go f (x / 2)) ^2

-- The exponential function (Haskell's Floating exp). Digits are
-- added to the internal calculation for x > 1, because exp-raw
-- multiplies numbers much larger than 1.
exp-fp : {e : Precision} -> FixedPrec e -> FixedPrec e
exp-fp x =
  if x ≤ᵇ 1 then exp-raw x
  else with-added-digits (1 + ceiling (x * fromRat 45 100)) (λ y -> cast (exp-raw y)) x

-- Raw implementation of the natural logarithm, and the logarithm
-- (Haskell's Floating log), with fuel. For x ≤ 0 (Haskell: error)
-- return 0.
mutual
  log-raw' : {e : Precision} -> ℕ -> FixedPrec e -> FixedPrec e
  log-raw' f x =
    if x ≤ᵇ 0 then 0
    else if (fromRat 3 4 ≤ᵇ x) ∧ (x ≤ᵇ fromRat 5 4) then log-p x
    else if fromRat 7 2 <ᵇ x then fromℤ (proj₁ nr) + log-fp' f (proj₂ nr)
    else if 1 <ᵇ x then fromRat 1 2 + log-fp' f (x / e2)
    else - log-fp' f (1 / x)
    where
      e2 = exp-p (fromRat 1 2)
      ee = exp-p 1
      nr = floorlog ee x

  log-fp' : {e : Precision} -> ℕ -> FixedPrec e -> FixedPrec e
  log-fp' zero x = 0
  log-fp' (suc f) x = downcast (log-raw' f (upcast x))

log-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
log-raw = log-raw' default-fuel

log-fp : {e : Precision} -> FixedPrec e -> FixedPrec e
log-fp = log-fp' default-fuel

-- Raw implementation of the inverse tangent, and the inverse tangent
-- (Haskell's Floating atan), with fuel.
mutual
  atan-raw' : {e : Precision} -> ℕ -> FixedPrec e -> FixedPrec e
  atan-raw' f x =
    if (- fromRat 44 100 ≤ᵇ x) ∧ (x ≤ᵇ fromRat 44 100) then atan-p x
    else if x <ᵇ 0 then - atan-fp' f (- x)
    else if fromRat 227 100 ≤ᵇ x then p2 - atan-p (1 / x)
    else p4 + atan-p ((x - 1) / (x + 1))
    where
      p2 = pi-fp /ℤ 2
      p4 = pi-fp /ℤ 4

  atan-fp' : {e : Precision} -> ℕ -> FixedPrec e -> FixedPrec e
  atan-fp' zero x = 0
  atan-fp' (suc f) x = downcast (atan-raw' f (upcast x))

atan-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
atan-raw = atan-raw' default-fuel

atan-fp : {e : Precision} -> FixedPrec e -> FixedPrec e
atan-fp = atan-fp' default-fuel

-- Raw implementation of the power function. This is subject to
-- similar loss of precision as exp-raw.
power-raw : {e : Precision} -> FixedPrec e -> FixedPrec e -> FixedPrec e
power-raw x y = exp-raw (log-raw x * y)

-- Raw implementation of logBase. This is subject to similar loss of
-- precision as exp-raw.
logBase-raw : {e : Precision} -> FixedPrec e -> FixedPrec e -> FixedPrec e
logBase-raw x y = log-fp y / log-fp x

-- Raw implementation of the inverse sine function. Outside [-1, 1]
-- (Haskell: error) return 0.
asin-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
asin-raw x =
  if (- fromRat 7 10 ≤ᵇ x) ∧ (x ≤ᵇ fromRat 7 10) then atan-fp (x / c)
  else if (0 <ᵇ x) ∧ (x ≤ᵇ 1) then p2 - atan-fp (c / x)
  else if (x <ᵇ 0) ∧ (-1 ≤ᵇ x) then - p2 - atan-fp (c / x)
  else 0
  where
    c = sqrt-fp (1 - x ^2)
    p2 = pi-fp /ℤ 2

-- Raw implementation of the inverse cosine function. Outside [-1, 1]
-- (Haskell: error) return 0.
acos-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
acos-raw x =
  if (- fromRat 7 10 ≤ᵇ x) ∧ (x ≤ᵇ fromRat 7 10) then p2 - atan-fp (x / s)
  else if (0 <ᵇ x) ∧ (x ≤ᵇ 1) then atan-fp (s / x)
  else if (x <ᵇ 0) ∧ (-1 ≤ᵇ x) then pi-fp + atan-fp (s / x)
  else 0
  where
    s = sqrt-fp (1 - x ^2)
    p2 = pi-fp /ℤ 2

-- Raw implementation of the hyperbolic sine.
sinh-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
sinh-raw x = (ex - 1 / ex) /ℤ 2 where ex = exp-fp x

-- Raw implementation of the hyperbolic cosine.
cosh-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
cosh-raw x = (ex + 1 / ex) /ℤ 2 where ex = exp-fp x

-- Raw implementation of the inverse hyperbolic tangent.
atanh-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
atanh-raw x = log-fp ((1 + x) / (1 - x)) /ℤ 2

-- Raw implementation of the inverse hyperbolic sine.
asinh-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
asinh-raw x = log-fp (x + sqrt-fp (x ^2 + 1))

-- Raw implementation of the inverse hyperbolic cosine. For x < 1
-- (Haskell: error) return 0.
acosh-raw : {e : Precision} -> FixedPrec e -> FixedPrec e
acosh-raw x = if 1 ≤ᵇ x then log-fp (x + sqrt-fp (x ^2 - 1)) else 0

-- ----------------------------------------------------------------------
-- ** The analytic functions (Haskell's Floating instance)

module _ {e : Precision} where
  sin-fp cos-fp tan-fp asin-fp acos-fp : FixedPrec e -> FixedPrec e
  sinh-fp cosh-fp tanh-fp asinh-fp acosh-fp atanh-fp : FixedPrec e -> FixedPrec e
  sin-fp x = downcast (sin-raw (upcast x))
  cos-fp x = downcast (cos-raw (upcast x))
  -- Haskell's default tan x = sin x / cos x.
  tan-fp x = sin-fp x / cos-fp x
  asin-fp x = downcast (asin-raw (upcast x))
  acos-fp x = downcast (acos-raw (upcast x))
  sinh-fp x = downcast (sinh-raw (upcast x))
  cosh-fp x = downcast (cosh-raw (upcast x))
  -- Haskell's default tanh x = sinh x / cosh x.
  tanh-fp x = sinh-fp x / cosh-fp x
  atanh-fp x = downcast (atanh-raw (upcast x))
  asinh-fp x = downcast (asinh-raw (upcast x))
  acosh-fp x = downcast (acosh-raw (upcast x))

-- ----------------------------------------------------------------------
-- ** log-double

-- Conversion of a rational number to the closest Float (Haskell's
-- fromRational at Double).
float-of-ℚ : ℚ -> Float
float-of-ℚ q = Float.fromRatio (Rat.↥ q) (+ Rat.↧ₙ q)

-- Float ceiling, as an integer (0 for NaN and infinities).
float-ceiling : Float -> ℤ
float-ceiling x with Float.⌈ x ⌉
... | just n = n
... | nothing = 0

-- A version of the natural logarithm that returns a Float. The
-- logarithm of just about any value can fit into a Float; so if not a
-- lot of precision is required in the mantissa, this function is
-- often faster than log.
-- log-double-with ex x is log-double x, where ex is the exponential
-- function (so that it can be used before the Floating instance of
-- FixedPrec is defined).
log-double-with : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : DecOrd A}} {{_ : ToRational A}} -> (A -> A) -> A -> Float
log-double-with {A} ex x = combine (floorlog (ex 1#) x)
  where
    combine : ℤ × A -> Float
    combine (n , r) = Float.fromℤ n Float.+ Float.log (float-of-ℚ (toℚ r))

log-double : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : DecOrd A}} {{_ : Floating A}} {{_ : ToRational A}} -> A -> Float
log-double = log-double-with exp

-- ----------------------------------------------------------------------
-- ** Power and logBase

module _ {e : Precision} where

  -- Haskell's x ** y at FixedPrec.
  power-fp : FixedPrec e -> FixedPrec e -> FixedPrec e
  power-fp x y =
    if x ≤ᵇ 1 then power-raw x y
    else with-added-digits d (λ z -> cast (power-raw (cast x) z)) y
    where
      -- we don't need a lot of precision in the logarithm here,
      -- because it is only to determine the number of digits
      d = 1 + ceiling (fromRat 45 100 * y * cast (log-raw (cast {e} {10} x)))

  -- Haskell's logBase x y at FixedPrec. (The first condition is never
  -- true, since lo > hi, but we keep it as in Haskell.)
  logBase-fp : FixedPrec e -> FixedPrec e -> FixedPrec e
  logBase-fp x y =
    if ((x <ᵇ fromRat 36 100) ∨ (fromRat 272 100 <ᵇ x)) ∧ (lo <ᵇ y) ∧ (y <ᵇ hi)
    then downcast (logBase-raw (upcast x) (upcast y))
    else with-added-digits d (λ z -> cast (logBase-raw (cast x) z)) y
    where
      dx = float-ceiling (Float.- 0.45 Float.* Float.log (abs (log-double-with exp-fp x)))
      dy = float-ceiling (0.45 Float.* Float.log (abs (log-double-with exp-fp y)))
      d = max dx (2 * dx + dy)
      lo = fromℕ 10000000000
      hi = fromRat 1 10000000000

-- ----------------------------------------------------------------------
-- * Haskell's Floating instance

instance
  FloatingFixedPrec : {e : Precision} -> Floating (FixedPrec e)
  FloatingFixedPrec .π = pi-fp
  FloatingFixedPrec .exp = exp-fp
  FloatingFixedPrec .log = log-fp
  FloatingFixedPrec .sqrt = sqrt-fp
  FloatingFixedPrec .sin = sin-fp
  FloatingFixedPrec .cos = cos-fp
  FloatingFixedPrec .tan = tan-fp
  FloatingFixedPrec .asin = asin-fp
  FloatingFixedPrec .acos = acos-fp
  FloatingFixedPrec .atan = atan-fp
  FloatingFixedPrec ._**_ = power-fp
  FloatingFixedPrec .logBase = logBase-fp
  FloatingFixedPrec .sinh = sinh-fp
  FloatingFixedPrec .cosh = cosh-fp
  FloatingFixedPrec .tanh = tanh-fp
  FloatingFixedPrec .asinh = asinh-fp
  FloatingFixedPrec .acosh = acosh-fp
  FloatingFixedPrec .atanh = atanh-fp

-- ----------------------------------------------------------------------
-- * Random

-- Haskell: randomR (lo, hi) draws an integer in [lo⋅10ᵉ, hi⋅10ᵉ] and
-- scales it by 0.1ᵉ (all exact), and random = randomR (0, 1).
instance
  RandomFixedPrec : {e : Precision} -> Random (FixedPrec e)
  RandomFixedPrec .Random.randomR (lo , hi) g with randomR (unF lo , unF hi) g
  ... | x , g' = F x , g'
  RandomFixedPrec {e} .Random.random g with randomR (0 , pow10 e) g
  ... | x , g' = F x , g'
