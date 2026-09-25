-- We use instance argument to overload the algebraic operations + and
-- * etc.. For example, Ring record here is like what Num class in
-- Haskell. Also like Haskell, we don't require the operations abide
-- by any laws (we can use the algebraic definitions in stdlib if
-- needed).
--
-- The class hierarchy follows the ring framework of the Haskell
-- package newsynth (module Quantum.Synthesis.Ring), see
-- https://hackage.haskell.org/package/newsynth. To avoid ambiguous
-- instance search ("diamonds"), the only superclass chains are
--
--   SemiRing ← Ring        and        NonZeroTypeclass ← DivMod ← Fractional.
--
-- All the other classes (HalfRing, RootTwoRing, ComplexRing, ...)
-- only carry their special constants and are used together with Ring
-- as separate instance arguments.

{-# OPTIONS --without-K --safe #-}

module Typeclasses where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)

open import Data.Bool using (Bool ; true ; false ; not ; T ; if_then_else_)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Integer as Int using (ℤ ; +_ ; -[1+_])
open import Data.Rational.Base as Rat using (ℚ)
open import Data.String.Base using (String)
-- tt must be in scope for instance search of the literal constraints.
open import Data.Unit.Base public using (⊤ ; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec ; does ; yes ; no)
open import Relation.Binary using (Rel ; Decidable ; DecidableEquality)

-- ----------------------------------------------------------------------
-- Type classes for Ring.

-- The fast-power evaluator is exposed so its algebraic laws can be proved
-- independently of the operational typeclass. Fuel and branch order agree
-- with the original evaluator, including for inexact carriers.
power-odd : ℕ -> Bool
power-odd zero = false
power-odd (suc zero) = true
power-odd (suc (suc n)) = power-odd n

power-acc : {A : Set} -> (A -> A -> A) -> ℕ -> A -> ℕ -> A -> A
power-acc mul zero x y z = mul x z
power-acc mul (suc f) x y z =
  if not (power-odd y) then power-acc mul f (mul x x) (Nat.⌊ y /2⌋) z
  else if y Nat.≡ᵇ suc zero then mul x z
  else power-acc mul f (mul x x) (Nat.⌊ y /2⌋) (mul x z)

power-fuel : {A : Set} -> (A -> A -> A) -> ℕ -> A -> ℕ -> A
power-fuel mul zero x y = x
power-fuel mul (suc f) x y =
  if not (power-odd y) then power-fuel mul f (mul x x) (Nat.⌊ y /2⌋)
  else if y Nat.≡ᵇ suc zero then x
  else power-acc mul f (mul x x) (Nat.⌊ y /2⌋) x

-- SemiRing typecalss has two operations + and * and two special
-- numbers 0 and 1. The field fromℕ is the unique semiring
-- homomorphism from ℕ, it is used to overload natural number
-- literals (see below).
record SemiRing (A : Set) : Set where
  infixl 6 _+_
  infixl 7 _*_
  infixr 8 _^2 _^_
  field
    _+_ : A -> A -> A
    _*_ : A -> A -> A
    0# : A
    1# : A
    fromℕ : ℕ -> A
  -- A useful shot-hand.
  _^2 : A -> A
  x ^2 = x * x

  -- Natural number power, computed by repeated squaring exactly like
  -- Haskell's (^) from GHC.Real, so that the rounding of inexact
  -- types (Float, FixedPrec) agrees with Haskell.
  _^_ : A -> ℕ -> A
  x ^ zero = 1#
  x ^ n@(suc _) = power-fuel _*_ n x n

  -- Doubling.
  twice : A -> A
  twice x = x + x

-- A special way to open a module in order to make the fields of the
-- record available as functions taking instance arguments.
open SemiRing {{...}} public

-- Ring typeclass is a subclass of SemiRing typeclass, and has
-- addtitve inverse. Hence we can define subtraction.
record Ring (A : Set) : Set where
  infixl 6 _-_
  infix 8 -_
  field
    {{sra}} : SemiRing A
    -_ : A -> A

  _-_ :  A -> A -> A
  _-_ x y = x + (- y)

  -- The unique ring homomorphism from ℤ.
  fromℤ : ℤ -> A
  fromℤ (+ n) = fromℕ n
  fromℤ -[1+ n ] = - fromℕ (suc n)

open Ring {{...}} public

-- ----------------------------------------------------------------------
-- Overloading of numeric constants.

-- Natural number literals such as 0, 1, 2 denote the corresponding
-- element in any semiring, and negative literals such as -1, -2 denote
-- the corresponding element in any ring. E.g. 0 : ℕ, 0 : ℤ, 0 : 𝔾,
-- -1 : ℤ [√2] etc. This is enabled by "open import Literals".
--
-- To this end, every ring type (constructor) T gets instances
--
--   instance NumberT = number-from-semiring ; NegativeT = negative-from-ring
--
-- We deliberately do not use a single generic instance {{SemiRing A}}
-- → Number A, since it would overlap with the instances for the
-- particular types (Agda does not discard a candidate whose own
-- instance arguments cannot be found). Generic code uses the module
-- LiteralsFor in Literals instead.
--
-- Note: in modules importing Agda.Builtin.FromNat (such as this one),
-- every natural number literal (including those of type ℕ) is
-- elaborated using fromNat, so the Number ℕ instance cannot use
-- literals itself.
number-from-semiring : {A : Set} {{_ : SemiRing A}} -> Number A
number-from-semiring .Number.Constraint _ = ⊤
number-from-semiring .Number.fromNat n = fromℕ n

negative-from-ring : {A : Set} {{_ : Ring A}} -> Negative A
negative-from-ring .Negative.Constraint _ = ⊤
negative-from-ring .Negative.fromNeg n = - fromℕ n

-- ----------------------------------------------------------------------
-- Type class for decidable equality.

record DecEq (A : Set) : Set where
  infix 4 _≟_ _==_ _/=_
  field
    _≟_ : DecidableEquality A

  -- Boolean equality.
  _==_ : A -> A -> Bool
  x == y = does (x ≟ y)

  _/=_ : A -> A -> Bool
  x /= y = not (x == y)

open DecEq {{...}} public

-- ----------------------------------------------------------------------
-- Type classes decidable order.

-- We will use orders on ℕ and ℤ simultaneously, so we also overload
-- the comparsion operations using typeclass.

-- Decidable order typeclass. Normally DecEq is a super class of
-- DecOrd, here we don't enforce this, since the main purpose is to
-- overload operators.

record DecOrd (A : Set) : Set₁ where
  infixl 4 _≤_ _<_
  infixl 4 _≤?_ _<?_
  infix 4 _≤ᵇ_ _<ᵇ_ _≥ᵇ_ _>ᵇ_
  field
    _≤_ : Rel A 0ℓ
    _≤?_ : Decidable _≤_
    _<_ : Rel A 0ℓ
    _<?_ : Decidable _<_

  -- Boolean versions of the comparisons.
  _≤ᵇ_ _<ᵇ_ _≥ᵇ_ _>ᵇ_ : A -> A -> Bool
  x ≤ᵇ y = does (x ≤? y)
  x <ᵇ y = does (x <? y)
  x ≥ᵇ y = y ≤ᵇ x
  x >ᵇ y = y <ᵇ x

  max min : A -> A -> A
  max x y = if x ≤ᵇ y then y else x
  min x y = if x ≤ᵇ y then x else y

open DecOrd {{...}} public

-- A total order given by a boolean comparison. This is how we
-- make approximate types such as Float into DecOrd instances.
decOrd-from-bool : {A : Set} -> (A -> A -> Bool) -> (A -> A -> Bool) -> DecOrd A
decOrd-from-bool le lt = record
  { _≤_ = λ x y -> T (le x y) ; _≤?_ = λ x y -> T? (le x y)
  ; _<_ = λ x y -> T (lt x y) ; _<?_ = λ x y -> T? (lt x y) }
  where
    T? : ∀ b -> Dec (T b)
    T? true = yes _
    T? false = no (λ ())

-- Absolute value and sign in an ordered ring.
abs : {A : Set} {{_ : Ring A}} {{_ : DecOrd A}} -> A -> A
abs x = if x <ᵇ 0# then - x else x

signum : {A : Set} {{_ : Ring A}} {{_ : DecOrd A}} -> A -> A
signum x = if x <ᵇ 0# then - 1# else if 0# <ᵇ x then 1# else 0#

-- ----------------------------------------------------------------------
-- Type classes NonZero and DivMod

-- We will use irrelevant implicit argument to exlude the zero divisor
-- case when defining the partial function "div" and "mod". For
-- generic algorithms we also need to decide whether an element is
-- non-zero.

record NonZeroTypeclass (A : Set) : Set₁  where
  field
    NonZero : (a : A) -> Set
    nonZero? : (a : A) -> Dec (NonZero a)

open NonZeroTypeclass {{...}} public

-- For types with decidable equality, the NonZero predicate can be
-- defined uniformly (this is not an instance, to avoid overlapping).
nonZeroTypeclass-from-eq : {A : Set} -> {{DecEq A}} -> A -> NonZeroTypeclass A
nonZeroTypeclass-from-eq z = record
  { NonZero = λ a -> T (not (a == z)) ; nonZero? = λ a -> T? (not (a == z)) }
  where
    T? : ∀ b -> Dec (T b)
    T? true = yes _
    T? false = no (λ ())

-- The NonZero predicate that is always satisfied. This is used for
-- approximate numbers such as Float, where division by zero is
-- defined (it gives infinity or 0).
nonZeroTypeclass-trivial : {A : Set} -> NonZeroTypeclass A
nonZeroTypeclass-trivial = record { NonZero = λ _ -> ⊤ ; nonZero? = λ _ -> yes _ }

-- DivMod typeclass is used to overload _/_ and _%_. In a Euclidean
-- domain, _/_ is the quotient and _%_ is the remainder. In a field,
-- _/_ is the division and _%_ is always 0.
record DivMod (A : Set) : Set₁ where
  infixl 7 _/_ _%_
  field
    {{NZT}} : NonZeroTypeclass A
    _/_     : (n d : A) .{{_ : NonZero d}} -> A
    _%_     : (n d : A) .{{_ : NonZero d}} -> A
open DivMod {{...}} public

-- Fractional typeclass (fields). The division is inherited from
-- DivMod.
record Fractional (A : Set) : Set₁ where
  infix 9 _⁻¹
  field
    {{DM}} : DivMod A
    _⁻¹ : (x : A) .{{_ : NonZero x}} -> A
    -- The unique ring homomorphism from ℚ.
    fromℚ : ℚ -> A

  recip : (x : A) .{{_ : NonZero x}} -> A
  recip x = x ⁻¹
open Fractional {{...}} public


-- ----------------------------------------------------------------------
-- Type classes for Rank (to be used in defining Euclidean structure)

-- Rank record has a rank function that spcifies the rank of the given
-- argument.
record Rank (A : Set) : Set where
  field
    rank : A -> ℕ
open Rank {{...}} public


-- ----------------------------------------------------------------------
-- Rings with particular elements (newsynth: HalfRing, RootTwoRing,
-- RootHalfRing, ComplexRing, OmegaRing).

-- Rings that contain ½. The field fromℤ/2^ is the unique ring
-- homomorphism from the dyadic fractions ℤ[½]: fromℤ/2^ a n = a / 2ⁿ.
-- It is a field (and not a derived function) since for fixed
-- precision types, the default a * ½ⁿ can underflow.
record HalfRing (A : Set) : Set where
  field
    half : A
    fromℤ/2^ : ℤ -> ℕ -> A

  ½ : A
  ½ = half
open HalfRing {{...}} public

-- Rings that contain √2. The field fromℤ[√2] is the unique ring
-- homomorphism from ℤ[√2]: fromℤ[√2] a b = a + b √2.
record RootTwoRing (A : Set) : Set where
  field
    roottwo : A
    fromℤ[√2] : ℤ -> ℤ -> A

  √2 : A
  √2 = roottwo
open RootTwoRing {{...}} public

-- Rings that contain 1/√2. The field fromD[√2] is the unique ring
-- homomorphism from ℤ[1/√2]: fromD[√2] (a , n) (b , m) = a / 2ⁿ + b
-- / 2ᵐ √2.
record RootHalfRing (A : Set) : Set where
  field
    roothalf : A
    fromD[√2] : ℤ -> ℕ -> ℤ -> ℕ -> A

  √½ : A
  √½ = roothalf
open RootHalfRing {{...}} public

-- Rings that contain a square root of -1.
record ComplexRing (A : Set) : Set where
  field
    i : A
open ComplexRing {{...}} public

-- The two square roots of -1. Note that +i and -i are identifiers.
+i -i : {A : Set} -> {{ComplexRing A}} -> {{Ring A}} -> A
+i = i
-i = - i

-- Rings that contain a square root of i, or equivalently, a fourth
-- root of -1.
record OmegaRing (A : Set) : Set where
  field
    omega : A

  ω : A
  ω = omega
open OmegaRing {{...}} public

-- ----------------------------------------------------------------------
-- Rings with particular automorphisms (newsynth: Adjoint, Adjoint2).

-- Complex conjugation, i.e. an automorphism mapping i to -i. For
-- matrices, it is the adjoint (conjugate transpose). For rings that
-- are not complex, it is the identity function.
record Adjoint (A : Set) : Set where
  infixl 9 _†
  field
    adj : A -> A

  _† : A -> A
  x † = adj x
open Adjoint {{...}} public

-- √2-conjugation, i.e. an automorphism mapping √2 to -√2. For rings
-- without √2 it is the identity function.
record Adjoint2 (A : Set) : Set where
  infixl 9 _•
  field
    adj2 : A -> A

  _• : A -> A
  x • = adj2 x
open Adjoint2 {{...}} public

-- ----------------------------------------------------------------------
-- Normed rings

-- A (number-theoretic) norm on a ring R is a function N : R → ℤ such
-- that N(rs) = N(r)N(s). It satisfies N(r) = 0 iff r = 0, and N(r) =
-- ±1 iff r is a unit.
record NormedRing (A : Set) : Set where
  field
    norm : A -> ℤ
open NormedRing {{...}} public

-- ----------------------------------------------------------------------
-- Floor and ceiling

record Floor (A : Set) : Set where
  field
    -- The greatest integer n such that n ≤ x.
    floor-of : A -> ℤ
    -- The least integer n such that x ≤ n.
    ceiling-of : A -> ℤ
open Floor {{...}} public

-- ----------------------------------------------------------------------
-- Real and complex analytic functions (Haskell's Floating class).

record Floating (A : Set) : Set where
  infixr 8 _**_
  field
    π : A
    exp log sqrt : A -> A
    sin cos tan : A -> A
    asin acos atan : A -> A
    -- Power and logarithm to a base: logBase b x = log x / log b.
    _**_ logBase : A -> A -> A
    sinh cosh tanh : A -> A
    asinh acosh atanh : A -> A

  pi : A
  pi = π
open Floating {{...}} public

-- Conversion to rational numbers (Haskell's toRational).
record ToRational (A : Set) : Set where
  field
    toℚ : A -> ℚ
open ToRational {{...}} public

-- ----------------------------------------------------------------------
-- Printing (Haskell's Show class).

record Show (A : Set) : Set where
  field
    -- showsPrec d x prints x in a context of precedence d.
    showsPrec : ℕ -> A -> String

  show : A -> String
  show = showsPrec zero
open Show {{...}} public
