-- This module is an Agda port of the module Quantum.Synthesis.Ring of
-- the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- The type classes themselves (SemiRing, Ring, HalfRing, RootTwoRing,
-- RootHalfRing, ComplexRing, OmegaRing, Adjoint, Adjoint2,
-- NormedRing, Floor, ...) are defined in Typeclasses, and the
-- instances for ℕ, ℤ, ℚ and Float are in Instances. This module
-- provides the particular rings of newsynth:
--
--   ℤ₂                   the integers modulo 2,
--   𝔻 = ℤ[½]             the dyadic fractions,
--   A [√2], A [i], A [ω] the extensions of a ring A by √2, i and ω,
--
-- and in particular ℤ[√2], 𝔻[√2], ℚ[√2], ℤ[i], 𝔻[i], ℚ[i], 𝔻[√2,i],
-- ℚ[√2,i], ℤ[ω], 𝔻[ω] and ℚ[ω]. Functions whose Haskell names contain
-- underscores are renamed with dashes, e.g. from_whole ↦ from-whole.
-- Haskell functions that call "error" on bad inputs either return a
-- Maybe, or are total with a documented default value.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; map ; foldr)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; _>>=_)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.DivMod as IDM
import Data.Nat.Properties as NatP
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base using (String ; _++_)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_∘_ ; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Decidable.Core using (T? ; map′ ; _×?_)

open import Instances
open import Literals

-- ----------------------------------------------------------------------
-- * Auxiliary functions on integers

-- Parity on ℕ and ℤ.
evenℕ : ℕ -> Bool
evenℕ n = n Nat.% 2 Nat.≡ᵇ 0

evenℤ : ℤ -> Bool
evenℤ a = evenℕ Int.∣ a ∣

-- Powers of two.
2^ : ℕ -> ℕ
2^ n = 2 Nat.^ n

2^ℤ : ℕ -> ℤ
2^ℤ n = + (2^ n)

-- 2ⁿ, computed with few multiplications: 2^ n performs n of them,
-- which is slow in compiled code for large n, whereas
--
--   pow2 n = (2⁶⁴)^⌊n/64⌋ ⋅ (2⁸)^⌊(n mod 64)/8⌋ ⋅ 2^(n mod 8)
--
-- performs at most n/64 + 16. It is equal to 2^ n (see
-- Quantum.Synthesis.Ring.Properties.Dyadic.pow2≡2^); 2^ is kept as
-- the specification used in the proofs.
pow2-small : ℕ -> ℕ
pow2-small r = 256 Nat.^ (r Nat./ 8) Nat.* 2^ (r Nat.% 8)

pow2 : ℕ -> ℕ
pow2 n = 18446744073709551616 Nat.^ (n Nat./ 64) Nat.* pow2-small (n Nat.% 64)

-- Floor division by a power of two (Haskell: shiftR).
shiftR : ℤ -> ℕ -> ℤ
shiftR a n = IDM._/_ a (2^ℤ n) {{NatP.m^n≢0 2 n}}

-- Multiplication by a power of two (Haskell: shiftL).
shiftL : ℤ -> ℕ -> ℤ
shiftL a n = a * + pow2 n

-- hibit n: 1 + the position of the leftmost "1" bit of n, i.e., the
-- number of binary digits of n. hibit 0 = 0. (For speed, 64 bits are
-- stripped at a time while n ≥ 2⁶⁴.)
hibit : ℕ -> ℕ
hibit n = go n n
  where
    -- the first argument of small and go is fuel.
    small : ℕ -> ℕ -> ℕ
    small _ zero = zero
    small zero _ = zero
    small (suc f) m@(suc _) = suc (small f (m Nat./ 2))

    go : ℕ -> ℕ -> ℕ
    go zero m = small m m
    go (suc f) m =
      if m Nat.<ᵇ 18446744073709551616 then small 64 m
      else go f (m Nat./ 18446744073709551616) Nat.+ 64

-- lobit n: the position of the rightmost "1" bit of an integer, or
-- -1 if none.
lobit : ℤ -> ℤ
lobit a with Int.∣ a ∣
... | zero = -1
... | n@(suc _) = + go n n
  where
    go : ℕ -> ℕ -> ℕ
    go zero _ = zero
    go (suc f) m = if evenℕ m then suc (go f (m Nat./ 2)) else zero

-- If n is of the form 2ᵏ, return k.
log2 : ℤ -> Maybe ℕ
log2 n with n ≤ᵇ 0
... | true = nothing
... | false with lobit n
...   | -[1+ _ ] = nothing
...   | + k = if n == 2^ℤ k then just k else nothing

-- For n ≥ 0, return the floor of the square root of n. This is done
-- using Newton's method in integer arithmetic.
intsqrtℕ : ℕ -> ℕ
intsqrtℕ zero = zero
intsqrtℕ n@(suc _) = start (hibit n)
  where
    -- (Intermediate values are passed as arguments, since let/where
    -- bindings are not shared in compiled code.)
    check : ℕ -> ℕ -> ℕ -> ℕ -> ℕ
    iter : ℕ -> ℕ -> ℕ
    iter zero m = m
    iter (suc f) zero = zero
    iter (suc f) m@(suc _) = check f m (m * m) (n Nat./ m)
    check f m m-sq q =
      if (m-sq Nat.≤ᵇ n) ∧ (n Nat.<ᵇ m-sq + 2 * m + 1) then m
      else iter f ((m + q) Nat./ 2)

    start : ℕ -> ℕ
    start h = iter (suc (suc h)) (pow2 (h Nat./ 2))

intsqrt : ℤ -> ℤ
intsqrt (+ n) = + intsqrtℕ n
intsqrt -[1+ _ ] = 0

-- ----------------------------------------------------------------------
-- * The ring ℤ₂ of integers modulo 2

data Z2 : Set where
  Even Odd : Z2

ℤ₂ : Set
ℤ₂ = Z2

instance
  SemiRingZ2 : SemiRing Z2
  SemiRingZ2 ._+_ Even x = x
  SemiRingZ2 ._+_ Odd Even = Odd
  SemiRingZ2 ._+_ Odd Odd = Even
  SemiRingZ2 ._*_ Odd x = x
  SemiRingZ2 ._*_ Even x = Even
  SemiRingZ2 .0# = Even
  SemiRingZ2 .1# = Odd
  SemiRingZ2 .fromℕ n = if evenℕ n then Even else Odd

  RingZ2 : Ring Z2
  RingZ2 .sra = SemiRingZ2
  RingZ2 .-_ x = x

  NumberZ2 : Number Z2
  NumberZ2 = number-from-semiring

  NegativeZ2 : Negative Z2
  NegativeZ2 = negative-from-ring

  DecEqZ2 : DecEq Z2
  DecEqZ2 ._≟_ Even Even = yes refl
  DecEqZ2 ._≟_ Even Odd = no λ ()
  DecEqZ2 ._≟_ Odd Even = no λ ()
  DecEqZ2 ._≟_ Odd Odd = yes refl

  AdjointZ2 : Adjoint Z2
  AdjointZ2 .adj x = x

  Adjoint2Z2 : Adjoint2 Z2
  Adjoint2Z2 .adj2 x = x

  ShowZ2 : Show Z2
  ShowZ2 .showsPrec _ Even = "0"
  ShowZ2 .showsPrec _ Odd = "1"

-- ----------------------------------------------------------------------
-- * The ring 𝔻 of dyadic fractions

-- A dyadic fraction is a rational number whose denominator is a
-- power of 2. We denote the dyadic fractions by 𝔻 = ℤ[½].
--
-- Unlike newsynth, we represent a dyadic fraction a/2ⁿ canonically:
-- either n = 0 or a is odd. Hence the propositional equality on
-- Dyadic is the equality of numbers.
Canonical : ℤ -> ℕ -> Bool
Canonical a n = (n Nat.≡ᵇ 0) ∨ not (evenℤ a)

record Dyadic : Set where
  constructor Dyadic'
  field
    numerator : ℤ
    exponent : ℕ
    .canonical : T (Canonical numerator exponent)

𝔻 : Set
𝔻 = Dyadic

-- Smart constructor: dyadic a n = a / 2ⁿ.
-- (The case split is on the decision T? (evenℤ a) rather than on the
-- boolean with "in eq", so that the definition can be reasoned about;
-- see Quantum.Synthesis.Ring.Properties.Dyadic.) The first clause is
-- a shortcut for performance: it returns the same result as the
-- general case, which would halve 0 n times (products with 0 occur
-- very often, e.g. in matrix products).
dyadic : ℤ -> ℕ -> Dyadic
dyadic (+ zero) _ = Dyadic' (+ zero) zero _
dyadic a zero = Dyadic' a zero _
dyadic a (suc n) with T? (evenℤ a)
... | yes _ = dyadic (shiftR a 1) n
... | no ¬e = Dyadic' a (suc n) (¬T⇒T-not ¬e)
  where
    ¬T⇒T-not : ∀ {b} -> ¬ T b -> T (not b)
    ¬T⇒T-not {true} ¬t = ¬t _
    ¬T⇒T-not {false} _ = _

-- Given a dyadic fraction r, return (a,n) such that r = a/2ⁿ, where
-- n ≥ 0 is chosen as small as possible.
decompose-dyadic : Dyadic -> ℤ × ℕ
decompose-dyadic (Dyadic' a n _) = a , n

-- Given a dyadic fraction r and an integer k ≥ 0, such that a =
-- r2ᵏ is an integer, return a. If a is not an integer, return the
-- floor of r2ᵏ.
integer-of-dyadic : Dyadic -> ℕ -> ℤ
integer-of-dyadic (Dyadic' a n _) k with n Nat.≤ᵇ k
... | true = shiftL a (k Nat.∸ n)
... | false = shiftR a (n Nat.∸ k)

private
  -- Bring two dyadics to a common exponent.
  align : Dyadic -> Dyadic -> ℤ × ℤ × ℕ
  align (Dyadic' a n _) (Dyadic' b m _) with n Nat.≤ᵇ m
  ... | true = shiftL a (m Nat.∸ n) , b , m
  ... | false = a , shiftL b (n Nat.∸ m) , n

instance
  SemiRingDyadic : SemiRing Dyadic
  SemiRingDyadic ._+_ x y with align x y
  ... | a , b , k = dyadic (a + b) k
  SemiRingDyadic ._*_ (Dyadic' a n _) (Dyadic' b m _) = dyadic (a * b) (n + m)
  SemiRingDyadic .0# = Dyadic' 0 0 _
  SemiRingDyadic .1# = Dyadic' 1 0 _
  SemiRingDyadic .fromℕ n = Dyadic' (+ n) 0 _

  RingDyadic : Ring Dyadic
  RingDyadic .sra = SemiRingDyadic
  RingDyadic .-_ (Dyadic' a n _) = dyadic (- a) n

  NumberDyadic : Number Dyadic
  NumberDyadic = number-from-semiring

  NegativeDyadic : Negative Dyadic
  NegativeDyadic = negative-from-ring

  -- The decisions of the component types are combined with map′ and
  -- _×?_ rather than by a "with" on them, because those compute the
  -- boolean "does" field without ever building the equality proof:
  -- x == y is then a cheap boolean test, which matters a lot when the
  -- type checker evaluates matrix equalities (Kopt.Optimality,
  -- Kopt.SynthProperties, Test.Kopt*).
  DecEqDyadic : DecEq Dyadic
  DecEqDyadic ._≟_ (Dyadic' a n _) (Dyadic' b m _) =
    map′ (λ { (refl , refl) -> refl }) (λ { refl -> refl , refl }) (a ≟ b ×? n ≟ m)

  DecOrdDyadic : DecOrd Dyadic
  DecOrdDyadic = decOrd-from-bool le lt
    where
      le lt : Dyadic -> Dyadic -> Bool
      le x y with align x y
      ... | a , b , _ = a ≤ᵇ b
      lt x y with align x y
      ... | a , b , _ = a <ᵇ b

  HalfRingDyadic : HalfRing Dyadic
  HalfRingDyadic .half = Dyadic' 1 1 _
  HalfRingDyadic .fromℤ/2^ = dyadic

  AdjointDyadic : Adjoint Dyadic
  AdjointDyadic .adj x = x

  Adjoint2Dyadic : Adjoint2 Dyadic
  Adjoint2Dyadic .adj2 x = x

  FloorDyadic : Floor Dyadic
  FloorDyadic .floor-of x = integer-of-dyadic x 0
  FloorDyadic .ceiling-of x = - integer-of-dyadic (- x) 0

  ToRationalDyadic : ToRational Dyadic
  ToRationalDyadic .toℚ (Dyadic' a n _) = Rat._/_ a (2^ n) {{NatP.m^n≢0 2 n}}

  ShowDyadic : Show Dyadic
  ShowDyadic .showsPrec d x = showsPrec d (toℚ x)

-- The unique ring homomorphism from 𝔻 to any HalfRing.
fromDyadic : {A : Set} {{_ : HalfRing A}} -> Dyadic -> A
fromDyadic (Dyadic' a n _) = fromℤ/2^ a n

-- The default implementation of fromℤ/2^ in terms of ½.
default-fromℤ/2^ : {A : Set} {{_ : Ring A}} -> A -> ℤ -> ℕ -> A
default-fromℤ/2^ h a n = fromℤ a * h ^ n

-- ----------------------------------------------------------------------
-- * The ring A [√2]

infixl 20 _[√2] _[i] _[ω]

-- The ring A[√2], where A is any ring. The value RootTwo a b
-- represents a + b √2.
record _[√2] (A : Set) : Set where
  constructor RootTwo
  field
    rt-a rt-b : A

module _ {A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  instance
    SemiRingRootTwo : SemiRing (A [√2])
    SemiRingRootTwo ._+_ (RootTwo a b) (RootTwo a' b') = RootTwo (a + a') (b + b')
    SemiRingRootTwo ._*_ (RootTwo a b) (RootTwo a' b') =
      RootTwo (a * a' + twice (b * b')) (a * b' + a' * b)
    SemiRingRootTwo .0# = RootTwo 0# 0#
    SemiRingRootTwo .1# = RootTwo 1# 0#
    SemiRingRootTwo .fromℕ n = RootTwo (fromℕ n) 0#

    RingRootTwo : Ring (A [√2])
    RingRootTwo .sra = SemiRingRootTwo
    RingRootTwo .-_ (RootTwo a b) = RootTwo (- a) (- b)

    NumberRootTwo : Number (A [√2])
    NumberRootTwo = number-from-semiring

    NegativeRootTwo : Negative (A [√2])
    NegativeRootTwo = negative-from-ring

    RootTwoRingRootTwo : RootTwoRing (A [√2])
    RootTwoRingRootTwo .roottwo = RootTwo 0# 1#
    RootTwoRingRootTwo .fromℤ[√2] a b = RootTwo (fromℤ a) (fromℤ b)

    DecEqRootTwo : {{DecEq A}} -> DecEq (A [√2])
    DecEqRootTwo ._≟_ (RootTwo a b) (RootTwo c d) =
      map′ (λ { (refl , refl) -> refl }) (λ { refl -> refl , refl }) (a ≟ c ×? b ≟ d)

    HalfRingRootTwo : {{HalfRing A}} -> HalfRing (A [√2])
    HalfRingRootTwo .half = RootTwo half 0#
    HalfRingRootTwo .fromℤ/2^ a n = RootTwo (fromℤ/2^ a n) 0#

    RootHalfRingRootTwo : {{HalfRing A}} -> RootHalfRing (A [√2])
    RootHalfRingRootTwo .roothalf = RootTwo 0# half
    RootHalfRingRootTwo .fromD[√2] a n b m = RootTwo (fromℤ/2^ a n) (fromℤ/2^ b m)

    ComplexRingRootTwo : {{ComplexRing A}} -> ComplexRing (A [√2])
    ComplexRingRootTwo .i = RootTwo i 0#

    OmegaRingRootTwo : {{ComplexRing A}} -> {{HalfRing A}} -> OmegaRing (A [√2])
    OmegaRingRootTwo .omega = roothalf * (1# + i)

    AdjointRootTwo : {{Adjoint A}} -> Adjoint (A [√2])
    AdjointRootTwo .adj (RootTwo a b) = RootTwo (adj a) (adj b)

    Adjoint2RootTwo : {{Adjoint2 A}} -> Adjoint2 (A [√2])
    Adjoint2RootTwo .adj2 (RootTwo a b) = RootTwo (adj2 a) (- adj2 b)

    NormedRingRootTwo : {{NormedRing A}} -> NormedRing (A [√2])
    NormedRingRootTwo .norm (RootTwo a b) = (norm a) ^2 - 2 * (norm b) ^2

  -- The sign of a + b√2, given the signs of a, b and a² - 2b². The
  -- result is -1, 0 or 1.
  module _ {{_ : DecOrd A}} where
    private
      isNeg isPos : A -> Bool
      isNeg x = x <ᵇ 0#
      isPos x = 0# <ᵇ x

    signum-RootTwo : A [√2] -> ℤ
    -- (n = a² - 2b² is passed as an argument, so that it is computed
    -- at most once in compiled code.)
    signum-RootTwo (RootTwo a b) = go (a * a - twice (b * b))
      where
        go : A -> ℤ
        go n =
          if not (isNeg a ∨ isPos a) ∧ not (isNeg b ∨ isPos b) then 0
          else if not (isNeg a) ∧ not (isNeg b) then 1
          else if not (isPos a) ∧ not (isPos b) then -1
          else if not (isNeg a) ∧ not (isPos b) ∧ not (isNeg n) then 1
          else if not (isPos a) ∧ not (isNeg b) ∧ not (isPos n) then 1
          else -1

    instance
      DecOrdRootTwo : DecOrd (A [√2])
      DecOrdRootTwo = decOrd-from-bool
        (λ x y -> not (signum-RootTwo (y - x) == -1))
        (λ x y -> signum-RootTwo (y - x) == 1)

  -- A [√2] is a field if A is (and √2 ∉ A).
  module _ {{_ : Fractional A}} {{_ : DecEq A}} where
    instance
      NonZeroRootTwo : NonZeroTypeclass (A [√2])
      NonZeroRootTwo = nonZeroTypeclass-from-eq 0#

    -- (The norm k is passed as an argument, so that it is computed
    -- only once in compiled code.)
    recip-RootTwo : A [√2] -> A [√2]
    recip-RootTwo (RootTwo a b) = with-k (a ^2 - twice (b ^2))
      where
        with-k : A -> A [√2]
        with-k k with nonZero? k
        ... | yes nz = RootTwo (_/_ a k {{nz}}) (_/_ (- b) k {{nz}})
        ... | no _ = 0#

    instance
      DivModRootTwo : DivMod (A [√2])
      DivModRootTwo .NZT = NonZeroRootTwo
      DivModRootTwo ._/_ x y = x * recip-RootTwo y
      DivModRootTwo ._%_ x y = 0#

      FractionalRootTwo : Fractional (A [√2])
      FractionalRootTwo .DM = DivModRootTwo
      FractionalRootTwo ._⁻¹ x = recip-RootTwo x
      FractionalRootTwo .fromℚ q = RootTwo (fromℚ q) 0#

  -- Printing, in the same format as newsynth, e.g. "1 + 2*roottwo".
  module _ {{_ : DecEq A}} {{_ : DecOrd A}} {{_ : Show A}} where
    showsPrec-RootTwo : ℕ -> A [√2] -> String
    showsPrec-RootTwo d (RootTwo a b) =
      if b == 0# then showsPrec d a
      else if a == 0# then irr d b
      else if 0# <ᵇ b then showParen d 6 (showsPrec 6 a ++ " + " ++ irr 6 b)
      else showParen d 6 (showsPrec 6 a ++ " - " ++ irr 7 (- b))
      where
        irr : ℕ -> A -> String
        irr d b = if b == 1# then "roottwo"
          else if b == - 1# then showParen d 6 "-roottwo"
          else showParen d 7 (showsPrec 7 b ++ "*roottwo")

    instance
      ShowRootTwo : Show (A [√2])
      ShowRootTwo .showsPrec = showsPrec-RootTwo

-- The ring ℤ[√2].
ZRootTwo ℤ[√2] : Set
ZRootTwo = ℤ [√2]
ℤ[√2] = ZRootTwo

-- The ring 𝔻[√2] = ℤ[1/√2].
DRootTwo 𝔻[√2] : Set
DRootTwo = 𝔻 [√2]
𝔻[√2] = DRootTwo

-- The field ℚ[√2].
QRootTwo ℚ[√2] : Set
QRootTwo = ℚ [√2]
ℚ[√2] = QRootTwo

-- The unique ring homomorphism from ℤ[√2] to any ring containing √2.
fromZRootTwo : {A : Set} {{_ : RootTwoRing A}} -> ZRootTwo -> A
fromZRootTwo (RootTwo a b) = fromℤ[√2] a b

-- The unique ring homomorphism from 𝔻[√2] to any ring containing 1/√2.
fromDRootTwo : {A : Set} {{_ : RootHalfRing A}} -> DRootTwo -> A
fromDRootTwo (RootTwo (Dyadic' a n _) (Dyadic' b m _)) = fromD[√2] a n b m

-- The unique ring homomorphism from ℚ[√2] to any field containing √2.
fromQRootTwo : {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : RootTwoRing A}} -> QRootTwo -> A
fromQRootTwo (RootTwo a b) = fromℚ a + roottwo * fromℚ b

-- The default implementations of fromℤ[√2] and fromD[√2].
default-fromℤ[√2] : {A : Set} {{_ : Ring A}} -> A -> ℤ -> ℤ -> A
default-fromℤ[√2] r a b = fromℤ a + r * fromℤ b

default-fromD[√2] : {A : Set} {{_ : Ring A}} {{_ : HalfRing A}} -> A -> ℤ -> ℕ -> ℤ -> ℕ -> A
default-fromD[√2] r a n b m = fromℤ/2^ a n + r * fromℤ/2^ b m

-- Return a square root of an element of ℤ[√2], if such a square root
-- exists.
zroottwo-root : ZRootTwo -> Maybe ZRootTwo
zroottwo-root z@(RootTwo a b) =
  if w1 * w1 == z then just w1
  else if w2 * w2 == z then just w2
  else if w3 * w3 == z then just w3
  else if w4 * w4 == z then just w4
  else nothing
  where
    d = a ^2 - 2 * b ^2
    r = intsqrt d
    x1 = intsqrt ((a + r) / 2)
    x2 = intsqrt ((a - r) / 2)
    y1 = intsqrt ((a - r) / 4)
    y2 = intsqrt ((a + r) / 4)
    w1 = RootTwo x1 y1
    w2 = RootTwo x2 y2
    w3 = RootTwo x1 (- y1)
    w4 = RootTwo x2 (- y2)

floor-QRootTwo : QRootTwo -> ℤ
floor-QRootTwo x@(RootTwo a b) = with-r (if 0 ≤ᵇ b then a' + b' else a' - b')
  where
    a' = Rat.floor a
    b' = intsqrt (Rat.floor (2 * b ^2))
    -- (r is an argument, so that it is computed only once; where
    -- bindings are not shared in compiled code.)
    with-r : ℤ -> ℤ
    with-r r =
      if fromℤ r + 1 ≤ᵇ x then r + 1
      else if fromℤ r ≤ᵇ x then r
      else r - 1

instance
  FloorQRootTwo : Floor QRootTwo
  FloorQRootTwo .floor-of = floor-QRootTwo
  FloorQRootTwo .ceiling-of x = - floor-QRootTwo (- x)

-- ----------------------------------------------------------------------
-- * The ring A [i]

-- The ring A[i], where A is any ring. The value Cplx a b represents
-- a + b i.
record _[i] (A : Set) : Set where
  constructor Cplx
  field
    re im : A

module _ {A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  instance
    SemiRingCplx : SemiRing (A [i])
    SemiRingCplx ._+_ (Cplx a b) (Cplx a' b') = Cplx (a + a') (b + b')
    SemiRingCplx ._*_ (Cplx a b) (Cplx a' b') = Cplx (a * a' - b * b') (a * b' + b * a')
    SemiRingCplx .0# = Cplx 0# 0#
    SemiRingCplx .1# = Cplx 1# 0#
    SemiRingCplx .fromℕ n = Cplx (fromℕ n) 0#

    RingCplx : Ring (A [i])
    RingCplx .sra = SemiRingCplx
    RingCplx .-_ (Cplx a b) = Cplx (- a) (- b)

    NumberCplx : Number (A [i])
    NumberCplx = number-from-semiring

    NegativeCplx : Negative (A [i])
    NegativeCplx = negative-from-ring

    ComplexRingCplx : ComplexRing (A [i])
    ComplexRingCplx .i = Cplx 0# 1#

    DecEqCplx : {{DecEq A}} -> DecEq (A [i])
    DecEqCplx ._≟_ (Cplx a b) (Cplx c d) =
      map′ (λ { (refl , refl) -> refl }) (λ { refl -> refl , refl }) (a ≟ c ×? b ≟ d)

    OmegaRingCplx : {{RootHalfRing A}} -> OmegaRing (A [i])
    OmegaRingCplx .omega = Cplx roothalf roothalf

    HalfRingCplx : {{HalfRing A}} -> HalfRing (A [i])
    HalfRingCplx .half = Cplx half 0#
    HalfRingCplx .fromℤ/2^ a n = Cplx (fromℤ/2^ a n) 0#

    RootHalfRingCplx : {{RootHalfRing A}} -> RootHalfRing (A [i])
    RootHalfRingCplx .roothalf = Cplx roothalf 0#
    RootHalfRingCplx .fromD[√2] a n b m = Cplx (fromD[√2] a n b m) 0#

    RootTwoRingCplx : {{RootTwoRing A}} -> RootTwoRing (A [i])
    RootTwoRingCplx .roottwo = Cplx roottwo 0#
    RootTwoRingCplx .fromℤ[√2] a b = Cplx (fromℤ[√2] a b) 0#

    AdjointCplx : {{Adjoint A}} -> Adjoint (A [i])
    AdjointCplx .adj (Cplx a b) = Cplx (adj a) (- adj b)

    Adjoint2Cplx : {{Adjoint2 A}} -> Adjoint2 (A [i])
    Adjoint2Cplx .adj2 (Cplx a b) = Cplx (adj2 a) (adj2 b)

    NormedRingCplx : {{NormedRing A}} -> NormedRing (A [i])
    NormedRingCplx .norm (Cplx a b) = (norm a) ^2 + (norm b) ^2

  -- A [i] is a field if A is (and i ∉ A).
  module _ {{_ : Fractional A}} {{_ : DecEq A}} where
    instance
      NonZeroCplx : NonZeroTypeclass (A [i])
      NonZeroCplx = nonZeroTypeclass-from-eq 0#

    -- (d is passed as an argument, so that it is computed only once
    -- in compiled code.)
    recip-Cplx : A [i] -> A [i]
    recip-Cplx (Cplx a b) = with-d (a ^2 + b ^2)
      where
        with-d : A -> A [i]
        with-d d with nonZero? d
        ... | yes nz = Cplx (_/_ a d {{nz}}) (_/_ (- b) d {{nz}})
        ... | no _ = 0#

    instance
      DivModCplx : DivMod (A [i])
      DivModCplx .NZT = NonZeroCplx
      DivModCplx ._/_ x y = x * recip-Cplx y
      DivModCplx ._%_ x y = 0#

      FractionalCplx : Fractional (A [i])
      FractionalCplx .DM = DivModCplx
      FractionalCplx ._⁻¹ x = recip-Cplx x
      FractionalCplx .fromℚ q = Cplx (fromℚ q) 0#

  -- Printing, in the same format as newsynth, e.g. "1 - 2*i". We
  -- do not make this an instance for all A, since newsynth prints
  -- 𝔻[√2,i] differently, see below.
  module _ {{_ : DecEq A}} {{_ : DecOrd A}} {{_ : Show A}} where
    showsPrec-Cplx : ℕ -> A [i] -> String
    showsPrec-Cplx d (Cplx a b) =
      if b == 0# then showsPrec d a
      else if a == 0# then imag d b
      else if 0# <ᵇ b then showParen d 6 (showsPrec 6 a ++ " + " ++ imag 6 b)
      else showParen d 6 (showsPrec 6 a ++ " - " ++ imag 7 (- b))
      where
        imag : ℕ -> A -> String
        imag d b = if b == 1# then "i"
          else if b == - 1# then showParen d 6 "-i"
          else showParen d 7 (showsPrec 7 b ++ "*i")

-- The ring ℤ[i] of Gaussian integers (see also GauInt.Base).
ZComplex ℤ[i] : Set
ZComplex = ℤ [i]
ℤ[i] = ZComplex

-- The ring 𝔻[i] = ℤ[½, i] of Gaussian dyadic fractions.
DComplex 𝔻[i] : Set
DComplex = 𝔻 [i]
𝔻[i] = DComplex

-- The field ℚ[i] of Gaussian rationals.
QComplex ℚ[i] : Set
QComplex = ℚ [i]
ℚ[i] = QComplex

-- The ring 𝔻[√2, i] = ℤ[1/√2, i].
DRComplex 𝔻[√2,i] : Set
DRComplex = DRootTwo [i]
𝔻[√2,i] = DRComplex

-- The field ℚ[√2, i].
QRComplex ℚ[√2,i] : Set
QRComplex = QRootTwo [i]
ℚ[√2,i] = QRComplex

-- Complex floating point numbers.
CDouble CFloat : Set
CDouble = Float [i]
CFloat = CDouble

-- The unique ring homomorphism from ℤ[i] to any ring containing i.
fromZComplex : {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} -> ZComplex -> A
fromZComplex (Cplx a b) = fromℤ a + i * fromℤ b

-- The unique ring homomorphism from 𝔻[i] to any ring containing ½ and i.
fromDComplex : {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} {{_ : HalfRing A}} -> DComplex -> A
fromDComplex (Cplx a b) = fromDyadic a + i * fromDyadic b

-- The unique ring homomorphism from ℚ[i] to any field containing i.
fromQComplex : {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} {{_ : Fractional A}} -> QComplex -> A
fromQComplex (Cplx a b) = fromℚ a + i * fromℚ b

-- The unique ring homomorphism from 𝔻[√2, i] to any ring containing
-- 1/√2 and i.
fromDRComplex : {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} {{_ : RootHalfRing A}} -> DRComplex -> A
fromDRComplex (Cplx a b) = fromDRootTwo a + i * fromDRootTwo b

-- The unique ring homomorphism from ℚ[√2, i] to any field containing
-- √2 and i.
fromQRComplex : {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} {{_ : Fractional A}} {{_ : RootTwoRing A}} -> QRComplex -> A
fromQRComplex (Cplx a b) = fromQRootTwo a + i * fromQRootTwo b

-- ----------------------------------------------------------------------
-- * The ring A [ω]

-- The ring A[ω], where A is any ring, and ω = e^{iπ/4} is an 8th
-- root of unity. The value Omega a b c d represents aω³+bω²+cω+d.
record _[ω] (A : Set) : Set where
  constructor Omega
  field
    om-a om-b om-c om-d : A

-- An inverse to the embedding A ↦ A[ω]: return the "real rational"
-- part, i.e., map aω³+bω²+cω+d to d.
omega-real : {A : Set} -> A [ω] -> A
omega-real (Omega a b c d) = d

module _ {A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  instance
    SemiRingOmega : SemiRing (A [ω])
    SemiRingOmega ._+_ (Omega a b c d) (Omega a' b' c' d') =
      Omega (a + a') (b + b') (c + c') (d + d')
    SemiRingOmega ._*_ (Omega a b c d) (Omega a' b' c' d') = Omega a'' b'' c'' d''
      where
        a'' = a * d' + b * c' + c * b' + d * a'
        b'' = b * d' + c * c' + d * b' - a * a'
        c'' = c * d' + d * c' - a * b' - b * a'
        d'' = d * d' - a * c' - b * b' - c * a'
    SemiRingOmega .0# = Omega 0# 0# 0# 0#
    SemiRingOmega .1# = Omega 0# 0# 0# 1#
    SemiRingOmega .fromℕ n = Omega 0# 0# 0# (fromℕ n)

    RingOmega : Ring (A [ω])
    RingOmega .sra = SemiRingOmega
    RingOmega .-_ (Omega a b c d) = Omega (- a) (- b) (- c) (- d)

    NumberOmega : Number (A [ω])
    NumberOmega = number-from-semiring

    NegativeOmega : Negative (A [ω])
    NegativeOmega = negative-from-ring

    DecEqOmega : {{DecEq A}} -> DecEq (A [ω])
    DecEqOmega ._≟_ (Omega a b c d) (Omega a' b' c' d') =
      map′ (λ { (refl , refl , refl , refl) -> refl }) (λ { refl -> refl , refl , refl , refl })
           (a ≟ a' ×? b ≟ b' ×? c ≟ c' ×? d ≟ d')

    HalfRingOmega : {{HalfRing A}} -> HalfRing (A [ω])
    HalfRingOmega .half = Omega 0# 0# 0# half
    HalfRingOmega .fromℤ/2^ a n = Omega 0# 0# 0# (fromℤ/2^ a n)

    RootHalfRingOmega : {{HalfRing A}} -> RootHalfRing (A [ω])
    RootHalfRingOmega .roothalf = Omega (- half) 0# half 0#
    RootHalfRingOmega .fromD[√2] a n b m = Omega (- y) 0# y (fromℤ/2^ a n)
      where y = fromℤ/2^ b m

    RootTwoRingOmega : RootTwoRing (A [ω])
    RootTwoRingOmega .roottwo = Omega (- 1#) 0# 1# 0#
    RootTwoRingOmega .fromℤ[√2] a b = Omega (- fromℤ b) 0# (fromℤ b) (fromℤ a)

    ComplexRingOmega : ComplexRing (A [ω])
    ComplexRingOmega .i = Omega 0# 1# 0# 0#

    OmegaRingOmega : OmegaRing (A [ω])
    OmegaRingOmega .omega = Omega 0# 0# 1# 0#

    AdjointOmega : {{Adjoint A}} -> Adjoint (A [ω])
    AdjointOmega .adj (Omega a b c d) = Omega (- adj c) (- adj b) (- adj a) (adj d)

    Adjoint2Omega : {{Adjoint2 A}} -> Adjoint2 (A [ω])
    Adjoint2Omega .adj2 (Omega a b c d) = Omega (- adj2 a) (adj2 b) (- adj2 c) (adj2 d)

    NormedRingOmega : {{NormedRing A}} -> NormedRing (A [ω])
    NormedRingOmega .norm (Omega x y z w) =
      (a ^2 + b ^2 + c ^2 + d ^2) ^2 - 2 * (a * b + b * c + c * d - d * a) ^2
      where
        a = norm x
        b = norm y
        c = norm z
        d = norm w

  -- A [ω] is a field if A is.
  module _ {{_ : Fractional A}} {{_ : DecEq A}} where
    instance
      NonZeroOmega : NonZeroTypeclass (A [ω])
      NonZeroOmega = nonZeroTypeclass-from-eq 0#

    -- The norm of aω³+bω²+cω+d as an element of A.
    omega-denom : A -> A -> A -> A -> A
    omega-denom a b c d =
      (a ^2 + b ^2 + c ^2 + d ^2) ^2 - 2 * (a * b + b * c + c * d - d * a) ^2

    -- (The norm is passed as an argument, so that it is computed only
    -- once in compiled code.)
    recip-Omega : A [ω] -> A [ω]
    recip-Omega (Omega a b c d) = with-n (omega-denom a b c d)
      where
        with-n : A -> A [ω]
        with-n n with nonZero? n
        ... | yes nz = x1 * x2 * x3 * Omega 0# 0# 0# (_/_ 1# n {{nz}})
          where
            x1 = Omega (- c) (- b) (- a) d
            x2 = Omega (- a) b (- c) d
            x3 = Omega c (- b) a d
        ... | no _ = 0#

    instance
      DivModOmega : DivMod (A [ω])
      DivModOmega .NZT = NonZeroOmega
      DivModOmega ._/_ x y = x * recip-Omega y
      DivModOmega ._%_ x y = 0#

      FractionalOmega : Fractional (A [ω])
      FractionalOmega .DM = DivModOmega
      FractionalOmega ._⁻¹ x = recip-Omega x
      FractionalOmega .fromℚ q = Omega 0# 0# 0# (fromℚ q)

  -- Printing in the format "Omega a b c d".
  module _ {{_ : Show A}} where
    showsPrec-Omega : ℕ -> A [ω] -> String
    showsPrec-Omega p (Omega a b c d) = showParen p 10 ("Omega " ++ showsPrec 11 a ++ " "
      ++ showsPrec 11 b ++ " " ++ showsPrec 11 c ++ " " ++ showsPrec 11 d)

-- The ring ℤ[ω] of cyclotomic integers of degree 8.
ZOmega ℤ[ω] : Set
ZOmega = ℤ [ω]
ℤ[ω] = ZOmega

-- The ring 𝔻[ω]. It is isomorphic to the ring 𝔻[√2, i], but they
-- have different Show instances.
DOmega 𝔻[ω] : Set
DOmega = 𝔻 [ω]
𝔻[ω] = DOmega

-- The field ℚ[ω] of cyclotomic rationals of degree 8.
QOmega ℚ[ω] : Set
QOmega = ℚ [ω]
ℚ[ω] = QOmega

-- The unique ring homomorphism from ℤ[ω] to any ring containing ω.
fromZOmega : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} -> ZOmega -> A
fromZOmega (Omega a b c d) = fromℤ a * ω ^ 3 + fromℤ b * ω ^ 2 + fromℤ c * ω + fromℤ d

-- The unique ring homomorphism from 𝔻[ω] to any ring containing ω and ½.
fromDOmega : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} {{_ : HalfRing A}} -> DOmega -> A
fromDOmega (Omega a b c d) = fromDyadic a * ω ^ 3 + fromDyadic b * ω ^ 2 + fromDyadic c * ω + fromDyadic d

-- The unique ring homomorphism from ℚ[ω] to any field containing ω.
fromQOmega : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} {{_ : Fractional A}} -> QOmega -> A
fromQOmega (Omega a b c d) = fromℚ a * ω ^ 3 + fromℚ b * ω ^ 2 + fromℚ c * ω + fromℚ d

-- Inverse of the embedding ℤ[√2] → ℤ[ω]. Note that ℤ[√2] = ℤ[ω] ∩ ℝ.
-- This function takes an element of ℤ[ω] that is real, and converts
-- it to an element of ℤ[√2]. It returns nothing if the input is not
-- real.
zroottwo-of-zomega : ZOmega -> Maybe ZRootTwo
zroottwo-of-zomega (Omega a b c d) =
  if (a == - c) ∧ (b == 0) then just (RootTwo d c) else nothing

-- ----------------------------------------------------------------------
-- * Conversion to dyadic

-- A type class relating "rational" types to their dyadic
-- counterparts.
record ToDyadic (A B : Set) : Set where
  field
    -- Convert a "rational" value to a "dyadic" value, if the
    -- denominator is a power of 2. Otherwise, return nothing.
    maybe-dyadic : A -> Maybe B
open ToDyadic {{...}} public

instance
  ToDyadicDyadic : ToDyadic Dyadic Dyadic
  ToDyadicDyadic .maybe-dyadic = just

  ToDyadicℚ : ToDyadic ℚ Dyadic
  ToDyadicℚ .maybe-dyadic q with log2 (+ Rat.↧ₙ q)
  ... | just k = just (dyadic (Rat.↥ q) k)
  ... | nothing = nothing

  ToDyadicRootTwo : {A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (A [√2]) (B [√2])
  ToDyadicRootTwo .maybe-dyadic (RootTwo x y) =
    maybe-dyadic x >>= λ x' -> maybe-dyadic y >>= λ y' -> just (RootTwo x' y')

  ToDyadicCplx : {A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (A [i]) (B [i])
  ToDyadicCplx .maybe-dyadic (Cplx x y) =
    maybe-dyadic x >>= λ x' -> maybe-dyadic y >>= λ y' -> just (Cplx x' y')

  ToDyadicOmega : {A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (A [ω]) (B [ω])
  ToDyadicOmega .maybe-dyadic (Omega x y z w) =
    maybe-dyadic x >>= λ x' -> maybe-dyadic y >>= λ y' ->
    maybe-dyadic z >>= λ z' -> maybe-dyadic w >>= λ w' -> just (Omega x' y' z' w')

-- ----------------------------------------------------------------------
-- * Real part

-- A type class for rings that have a "real" component. A typical
-- instance is A = DRComplex with B = DRootTwo.
record RealPart (A B : Set) : Set where
  field
    real : A -> B
open RealPart {{...}} public

instance
  RealPartCplx : {A : Set} -> RealPart (A [i]) A
  RealPartCplx .real (Cplx a b) = a

  RealPartOmega : {A : Set} {{_ : Ring A}} {{_ : HalfRing A}} -> RealPart (A [ω]) (A [√2])
  RealPartOmega .real (Omega a b c d) = RootTwo d (half * (c - a))

-- ----------------------------------------------------------------------
-- * Rings of integers

-- A type class for rings that have a distinguished subring "of
-- integers". A typical instance is A = DRootTwo, which has B =
-- ZRootTwo as its ring of integers.
record WholePart (A B : Set) : Set where
  field
    -- The embedding of the ring of integers into the larger ring.
    from-whole : B -> A
    -- The inverse of from-whole. For non-integral inputs, the
    -- result is unspecified (we take the floor of the coefficients).
    to-whole : A -> B
open WholePart {{...}} public

instance
  WholePartDyadic : WholePart Dyadic ℤ
  WholePartDyadic .from-whole = fromℤ
  WholePartDyadic .to-whole d = integer-of-dyadic d 0

  WholePartDRootTwo : WholePart DRootTwo ZRootTwo
  WholePartDRootTwo .from-whole (RootTwo a b) = RootTwo (fromℤ a) (fromℤ b)
  WholePartDRootTwo .to-whole (RootTwo x y) = RootTwo (to-whole x) (to-whole y)

  WholePartDOmega : WholePart DOmega ZOmega
  WholePartDOmega .from-whole (Omega a b c d) = Omega (fromℤ a) (fromℤ b) (fromℤ c) (fromℤ d)
  WholePartDOmega .to-whole (Omega x y z w) = Omega (to-whole x) (to-whole y) (to-whole z) (to-whole w)

  WholePartPair : {A A' B B' : Set} {{_ : WholePart A A'}} {{_ : WholePart B B'}} -> WholePart (A × B) (A' × B')
  WholePartPair .from-whole (x , y) = from-whole x , from-whole y
  WholePartPair .to-whole (x , y) = to-whole x , to-whole y

  WholePartUnit : WholePart ⊤ ⊤
  WholePartUnit .from-whole _ = _
  WholePartUnit .to-whole _ = _

  WholePartList : {A B : Set} {{_ : WholePart A B}} -> WholePart (List A) (List B)
  WholePartList .from-whole = map from-whole
  WholePartList .to-whole = map to-whole

  WholePartCplx : {A B : Set} {{_ : WholePart A B}} -> WholePart (A [i]) (B [i])
  WholePartCplx .from-whole (Cplx a b) = Cplx (from-whole a) (from-whole b)
  WholePartCplx .to-whole (Cplx a b) = Cplx (to-whole a) (to-whole b)

-- ----------------------------------------------------------------------
-- * Common denominators

-- A type class for things from which a common power of 1/√2 (a least
-- denominator exponent) can be factored out. Typical instances are
-- DRootTwo, DRComplex, as well as tuples, lists, vectors, and
-- matrices thereof.
record DenomExp (A : Set) : Set where
  field
    -- Calculate the least denominator exponent k of a. Returns the
    -- smallest k ≥ 0 such that a = b/√2ᵏ for some integral b.
    denomexp : A -> ℕ
    -- Factor out a kth power of 1/√2 from a. In other words,
    -- calculate a√2ᵏ.
    denomexp-factor : A -> ℕ -> A
open DenomExp {{...}} public

-- Calculate and factor out the least denominator exponent k of a.
-- Return (b,k), where a = b/(√2)ᵏ and k ≥ 0.
denomexp-decompose : {A B : Set} {{_ : WholePart A B}} {{_ : DenomExp A}} -> A -> B × ℕ
denomexp-decompose a = to-whole (denomexp-factor a k) , k
  where k = denomexp a

-- Generic show-like method that factors out a common denominator
-- exponent.
showsPrec-DenomExp : {A B : Set} {{_ : WholePart A B}} {{_ : Show B}} {{_ : DenomExp A}} -> ℕ -> A -> String
showsPrec-DenomExp {A} {B} d a with denomexp-decompose {A} {B} a
... | b , zero = showsPrec d b
... | b , suc zero = showParen d 7 ("roothalf * " ++ showsPrec 7 b)
... | b , k = showParen d 7 ("roothalf^" ++ show k ++ " * " ++ showsPrec 7 b)

instance
  DenomExpDRootTwo : DenomExp DRootTwo
  DenomExpDRootTwo .denomexp (RootTwo (Dyadic' _ k _) (Dyadic' _ l _)) = max (2 * k) (2 * l Nat.∸ 1)
  DenomExpDRootTwo .denomexp-factor a k = a * roottwo ^ k

  DenomExpDOmega : DenomExp DOmega
  DenomExpDOmega .denomexp (Omega (Dyadic' a ak _) (Dyadic' b bk _) (Dyadic' c ck _) (Dyadic' d dk _)) =
    if (0 <ᵇ k) ∧ evenℤ (a' - c') ∧ evenℤ (b' - d') then 2 * k Nat.∸ 1 else 2 * k
    where
      k = max (max ak bk) (max ck dk)
      a' = if k == ak then a else 0
      b' = if k == bk then b else 0
      c' = if k == ck then c else 0
      d' = if k == dk then d else 0
  DenomExpDOmega .denomexp-factor a k = a * roottwo ^ k

  DenomExpPair : {A B : Set} {{_ : DenomExp A}} {{_ : DenomExp B}} -> DenomExp (A × B)
  DenomExpPair .denomexp (a , b) = max (denomexp a) (denomexp b)
  DenomExpPair .denomexp-factor (a , b) k = denomexp-factor a k , denomexp-factor b k

  DenomExpUnit : DenomExp ⊤
  DenomExpUnit .denomexp _ = 0
  DenomExpUnit .denomexp-factor _ _ = _

  DenomExpList : {A : Set} {{_ : DenomExp A}} -> DenomExp (List A)
  DenomExpList .denomexp as = foldr (λ a k -> max (denomexp a) k) 0 as
  DenomExpList .denomexp-factor as k = map (λ a -> denomexp-factor a k) as

  DenomExpCplx : {A : Set} {{_ : DenomExp A}} -> DenomExp (A [i])
  DenomExpCplx .denomexp (Cplx a b) = max (denomexp a) (denomexp b)
  DenomExpCplx .denomexp-factor (Cplx a b) k = Cplx (denomexp-factor a k) (denomexp-factor b k)

-- ----------------------------------------------------------------------
-- Show instances for the particular rings. Elements of 𝔻[ω] and
-- 𝔻[√2,i] are shown by pulling out a common denominator exponent,
-- e.g. "roothalf^3 * Omega 1 0 1 0".

instance
  ShowZComplex : Show ZComplex
  ShowZComplex .showsPrec = showsPrec-Cplx

  ShowDComplex : Show DComplex
  ShowDComplex .showsPrec = showsPrec-Cplx

  ShowQComplex : Show QComplex
  ShowQComplex .showsPrec = showsPrec-Cplx

  ShowQRComplex : Show QRComplex
  ShowQRComplex .showsPrec = showsPrec-Cplx

  ShowCDouble : Show CDouble
  ShowCDouble .showsPrec = showsPrec-Cplx

  ShowZRComplex : Show (ZRootTwo [i])
  ShowZRComplex .showsPrec = showsPrec-Cplx

  ShowDRComplex : Show DRComplex
  ShowDRComplex .showsPrec = showsPrec-DenomExp

  ShowZOmega : Show ZOmega
  ShowZOmega .showsPrec = showsPrec-Omega

  ShowQOmega : Show QOmega
  ShowQOmega .showsPrec = showsPrec-Omega

  ShowDOmega : Show DOmega
  ShowDOmega .showsPrec = showsPrec-DenomExp

-- ----------------------------------------------------------------------
-- * Conversion to ℚ[ω]

-- QOmega is the largest one of our "exact" arithmetic types. We
-- define a toQOmega family of functions for converting just about
-- anything to QOmega.
record ToQOmega (A : Set) : Set where
  field
    toQOmega : A -> QOmega
open ToQOmega {{...}} public

instance
  ToQOmegaℤ : ToQOmega ℤ
  ToQOmegaℤ .toQOmega = fromℤ

  ToQOmegaℚ : ToQOmega ℚ
  ToQOmegaℚ .toQOmega q = Omega 0 0 0 q

  ToQOmegaDyadic : ToQOmega Dyadic
  ToQOmegaDyadic .toQOmega d = Omega 0 0 0 (toℚ d)

  ToQOmegaRootTwo : {A : Set} {{_ : ToQOmega A}} -> ToQOmega (A [√2])
  ToQOmegaRootTwo .toQOmega (RootTwo a b) = toQOmega a + roottwo * toQOmega b

  ToQOmegaCplx : {A : Set} {{_ : ToQOmega A}} -> ToQOmega (A [i])
  ToQOmegaCplx .toQOmega (Cplx a b) = toQOmega a + i * toQOmega b

  ToQOmegaOmega : {A : Set} {{_ : ToQOmega A}} -> ToQOmega (A [ω])
  ToQOmegaOmega .toQOmega (Omega a b c d) =
    ω ^ 3 * toQOmega a + ω ^ 2 * toQOmega b + ω * toQOmega c + toQOmega d

-- ----------------------------------------------------------------------
-- * Parity

-- A type class for things that have parity.
record Parity (A : Set) : Set where
  field
    parity : A -> Z2
open Parity {{...}} public

instance
  Parityℕ : Parity ℕ
  Parityℕ .parity n = if evenℕ n then Even else Odd

  Parityℤ : Parity ℤ
  Parityℤ .parity n = if evenℤ n then Even else Odd

  ParityZRootTwo : Parity ZRootTwo
  ParityZRootTwo .parity (RootTwo a b) = parity a
