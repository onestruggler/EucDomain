-- This file defines instances for natural numbers, integers,
-- rationals and floating point numbers to overload various
-- operations.

{-# OPTIONS --without-K --safe #-}

module Instances where

-- imports from stdlib.
open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String ; _++_)
import Data.Nat as Nat
import Data.Nat.Properties as NatP
import Data.Nat.Show as NatS
import Data.Integer as Int
import Data.Integer.Properties as IntP
import Data.Integer.Show as IntS
import Data.Integer.DivMod as IDM
import Data.Nat.DivMod as NDM
import Data.Rational.Base as Rat
import Data.Rational.Properties as RatP
import Data.Float.Base as Float
import Data.Float.Properties as FloatP

-- The instance proving that suc n is non-zero (so that literals like 2
-- can be used as divisors in ℕ, ℤ and ℚ).
open import Data.Nat.Base public using (nonZero)

-- imports from local.
open import Typeclasses public
open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)

-- Natural number literals in ℕ. This instance must not depend on
-- other instances, see the comment on number-from-semiring in
-- Typeclasses.
instance
  Numberℕ : Number Nat.ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat n = n

-- An auxiliary function for printing, like Haskell's showParen.
showParen : Nat.ℕ -> Nat.ℕ -> String -> String
showParen d p s = if p Nat.<ᵇ d then "(" ++ s ++ ")" else s

-- ----------------------------------------------------------------------
-- Natural numbers

-- Natural numbers form a semiring. Note that we cannot use literals
-- here, since literals are elaborated using this instance.
instance
  SMℕ : SemiRing Nat.ℕ
  SMℕ ._+_ = Nat._+_
  SMℕ ._*_ = Nat._*_
  SMℕ .0# = Nat.zero
  SMℕ .1# = Nat.suc Nat.zero
  SMℕ .fromℕ n = n

  DEℕ : DecEq Nat.ℕ
  DEℕ ._≟_ = Nat._≟_

-- The usual order on ℕ is decidable.
instance
  DOℕ : DecOrd Nat.ℕ
  DOℕ ._≤_   = Nat._≤_
  DOℕ ._≤?_  = Nat._≤?_
  DOℕ ._<_   = Nat._<_
  DOℕ ._<?_  = Nat._<?_

-- ℕ has NonZero stucture on it defined in Data.Nat.Base.
instance
  NZTℕ : NonZeroTypeclass Nat.ℕ
  NZTℕ .NonZero = Nat.NonZero
  NZTℕ .nonZero? = NatP.nonZero?

-- div and mod function on ℕ. They are defined in Data.Nat.DivMod.
instance
  DMℕ : DivMod Nat.ℕ
  DMℕ .NZT = NZTℕ
  DMℕ ._/_ = NDM._/_
  DMℕ ._%_ = NDM._%_

-- Identity function can be used as the rank function.
instance
  Rankℕ : Rank Nat.ℕ
  Rankℕ .rank x = x

instance
  Showℕ : Show Nat.ℕ
  Showℕ .showsPrec _ = NatS.show

-- ----------------------------------------------------------------------
-- Integers

-- Integers form a semiring.
instance
  SMℤ : SemiRing Int.ℤ
  SMℤ ._+_ = Int._+_
  SMℤ ._*_ = Int._*_
  SMℤ .0# = Int.0ℤ
  SMℤ .1# = Int.1ℤ
  SMℤ .fromℕ = Int.+_

-- The set of intergers is a ring.
instance
  Ringℤ : Ring Int.ℤ
  Ringℤ .sra = SMℤ
  Ringℤ .-_ = Int.-_

  Numberℤ : Number Int.ℤ
  Numberℤ = number-from-semiring

  Negativeℤ : Negative Int.ℤ
  Negativeℤ = negative-from-ring

  DEℤ : DecEq Int.ℤ
  DEℤ ._≟_ = Int._≟_

-- The usual order on ℤ is decidable.
instance
  DOℤ : DecOrd Int.ℤ
  DOℤ ._≤_   = Int._≤_
  DOℤ ._≤?_  = Int._≤?_
  DOℤ ._<_   = Int._<_
  DOℤ ._<?_  = Int._<?_

-- ℤ has NonZero stucture on it defined in Data.Integer.Base.
instance
  NZTℤ : NonZeroTypeclass Int.ℤ
  NZTℤ .NonZero = Int.NonZero
  NZTℤ .nonZero? i = NatP.nonZero? Int.∣ i ∣

-- div and mod function on ℤ. They are defined in Data.Integer.DivMod.
instance
  DMℤ : DivMod Int.ℤ
  DMℤ .NZT = NZTℤ
  DMℤ ._/_ = IDM._/_
  DMℤ ._%_ n d = Int.+ (n IDM.% d)

-- Absolute value function can be used as the rank function.
instance
  Rankℤ : Rank Int.ℤ
  Rankℤ .rank = Int.∣_∣

instance
  NormedRingℤ : NormedRing Int.ℤ
  NormedRingℤ .norm x = x

  Floorℤ : Floor Int.ℤ
  Floorℤ .floor-of x = x
  Floorℤ .ceiling-of x = x

  Adjointℤ : Adjoint Int.ℤ
  Adjointℤ .adj x = x

  Adjoint2ℤ : Adjoint2 Int.ℤ
  Adjoint2ℤ .adj2 x = x

  ToRationalℤ : ToRational Int.ℤ
  ToRationalℤ .toℚ x = x Rat./ 1

-- Negative numbers are printed with parentheses in a context of
-- precedence > 6, like in Haskell.
instance
  Showℤ : Show Int.ℤ
  Showℤ .showsPrec d (Int.+ n) = NatS.show n
  Showℤ .showsPrec d x@(Int.-[1+ _ ]) = showParen d 6 (IntS.show x)

-- ----------------------------------------------------------------------
-- Rationals

instance
  SMℚ : SemiRing Rat.ℚ
  SMℚ ._+_ = Rat._+_
  SMℚ ._*_ = Rat._*_
  SMℚ .0# = Rat.0ℚ
  SMℚ .1# = Rat.1ℚ
  SMℚ .fromℕ n = Int.+ n Rat./ 1

  Ringℚ : Ring Rat.ℚ
  Ringℚ .sra = SMℚ
  Ringℚ .-_ = Rat.-_

  Numberℚ : Number Rat.ℚ
  Numberℚ = number-from-semiring

  Negativeℚ : Negative Rat.ℚ
  Negativeℚ = negative-from-ring

  DEℚ : DecEq Rat.ℚ
  DEℚ ._≟_ = RatP._≟_

  DOℚ : DecOrd Rat.ℚ
  DOℚ ._≤_   = Rat._≤_
  DOℚ ._≤?_  = RatP._≤?_
  DOℚ ._<_   = Rat._<_
  DOℚ ._<?_  = RatP._<?_

  NZTℚ : NonZeroTypeclass Rat.ℚ
  NZTℚ .NonZero = Rat.NonZero
  NZTℚ .nonZero? p@record{} = NatP.nonZero? Int.∣ Rat.↥ p ∣

  -- ℚ is a field, so the remainder is always 0.
  DMℚ : DivMod Rat.ℚ
  DMℚ .NZT = NZTℚ
  DMℚ ._/_ p q = p Rat.÷ q
  DMℚ ._%_ p q = Rat.0ℚ

  Fractionalℚ : Fractional Rat.ℚ
  Fractionalℚ .DM = DMℚ
  Fractionalℚ ._⁻¹ p = Rat.1/ p
  Fractionalℚ .fromℚ p = p

  Floorℚ : Floor Rat.ℚ
  Floorℚ .floor-of = Rat.floor
  Floorℚ .ceiling-of = Rat.ceiling

  HalfRingℚ : HalfRing Rat.ℚ
  HalfRingℚ .half = Rat.½
  HalfRingℚ .fromℤ/2^ a n = a Rat./ (2 Nat.^ n)
    where instance _ = NatP.m^n≢0 2 n

  Adjointℚ : Adjoint Rat.ℚ
  Adjointℚ .adj x = x

  Adjoint2ℚ : Adjoint2 Rat.ℚ
  Adjoint2ℚ .adj2 x = x

  ToRationalℚ : ToRational Rat.ℚ
  ToRationalℚ .toℚ x = x

-- Rationals are printed as in newsynth, e.g. -3/4, omitting
-- denominators of 1.
instance
  Showℚ : Show Rat.ℚ
  Showℚ .showsPrec d p with Rat.↧ₙ p Nat.≡ᵇ 1 | Rat.↥ p
  ... | Data.Bool.Base.true | a = showsPrec d a
  ... | Data.Bool.Base.false | a@(Int.+ _) = showParen d 7 (IntS.show a ++ "/" ++ NatS.show (Rat.↧ₙ p))
  ... | Data.Bool.Base.false | a@(Int.-[1+ _ ]) =
    showParen d 6 ("-" ++ IntS.show (Int.- a) ++ "/" ++ NatS.show (Rat.↧ₙ p))

-- ----------------------------------------------------------------------
-- Double precision floating point numbers

-- Float approximates the real numbers. Division by zero is defined
-- (by IEEE 754), so NonZero is trivial.

-- 0.5, 2.0 etc. as floats.
private
  fl : Nat.ℕ -> Float.Float
  fl = Float.fromℕ

  fl0 : Float.Float -> Int.ℤ
  fl0 x with Float.⌊ x ⌋
  ... | just n = n
  ... | nothing = Int.0ℤ

  fl1 : Float.Float -> Int.ℤ
  fl1 x with Float.⌈ x ⌉
  ... | just n = n
  ... | nothing = Int.0ℤ

instance
  SMFloat : SemiRing Float.Float
  SMFloat ._+_ = Float._+_
  SMFloat ._*_ = Float._*_
  SMFloat .0# = fl 0
  SMFloat .1# = fl 1
  SMFloat .fromℕ = Float.fromℕ

  RingFloat : Ring Float.Float
  RingFloat .sra = SMFloat
  RingFloat .-_ = Float.-_

  NumberFloat : Number Float.Float
  NumberFloat = number-from-semiring

  NegativeFloat : Negative Float.Float
  NegativeFloat = negative-from-ring

  DEFloat : DecEq Float.Float
  DEFloat ._≟_ = FloatP._≟_

  DOFloat : DecOrd Float.Float
  DOFloat = decOrd-from-bool Float._≤ᵇ_ Float._<ᵇ_

  NZTFloat : NonZeroTypeclass Float.Float
  NZTFloat = nonZeroTypeclass-trivial

  DMFloat : DivMod Float.Float
  DMFloat .NZT = NZTFloat
  DMFloat ._/_ x y = x Float.÷ y
  DMFloat ._%_ x y = fl 0

  FractionalFloat : Fractional Float.Float
  FractionalFloat .DM = DMFloat
  FractionalFloat ._⁻¹ x = fl 1 Float.÷ x
  FractionalFloat .fromℚ p = Float.fromℤ (Rat.↥ p) Float.÷ Float.fromℕ (Rat.↧ₙ p)

  FloatingFloat : Floating Float.Float
  FloatingFloat .π = 3.141592653589793
  FloatingFloat .exp = Float.e^_
  FloatingFloat .log = Float.log
  FloatingFloat .sqrt = Float.sqrt
  FloatingFloat .sin = Float.sin
  FloatingFloat .cos = Float.cos
  FloatingFloat .tan = Float.tan
  FloatingFloat .asin = Float.asin
  FloatingFloat .acos = Float.acos
  FloatingFloat .atan = Float.atan
  FloatingFloat ._**_ = Float._**_
  FloatingFloat .logBase b x = Float.log x Float.÷ Float.log b
  FloatingFloat .sinh = Float.sinh
  FloatingFloat .cosh = Float.cosh
  FloatingFloat .tanh = Float.tanh
  FloatingFloat .asinh = Float.asinh
  FloatingFloat .acosh = Float.acosh
  FloatingFloat .atanh = Float.atanh

  FloorFloat : Floor Float.Float
  FloorFloat .floor-of = fl0
  FloorFloat .ceiling-of = fl1

  HalfRingFloat : HalfRing Float.Float
  HalfRingFloat .half = 0.5
  HalfRingFloat .fromℤ/2^ a n = Float.fromℤ a Float.÷ (fl 2 Float.** fl n)

  RootTwoRingFloat : RootTwoRing Float.Float
  RootTwoRingFloat .roottwo = Float.sqrt (fl 2)
  RootTwoRingFloat .fromℤ[√2] a b = Float.fromℤ a Float.+ Float.sqrt (fl 2) Float.* Float.fromℤ b

  RootHalfRingFloat : RootHalfRing Float.Float
  RootHalfRingFloat .roothalf = Float.sqrt 0.5
  RootHalfRingFloat .fromD[√2] a n b m =
    HalfRingFloat .fromℤ/2^ a n Float.+ Float.sqrt (fl 2) Float.* HalfRingFloat .fromℤ/2^ b m

  AdjointFloat : Adjoint Float.Float
  AdjointFloat .adj x = x

  Adjoint2Float : Adjoint2 Float.Float
  Adjoint2Float .adj2 x = x

  ShowFloat : Show Float.Float
  ShowFloat .showsPrec d x = if x Float.<ᵇ fl 0 then showParen d 6 (Float.show x) else Float.show x

-- Exact conversion of a Float to a rational number (Haskell's
-- toRational). NaN and the infinities (Haskell: garbage values) are
-- mapped to 0.
toℚ-Float : Float.Float -> Rat.ℚ
toℚ-Float x with Float.toRatio x
... | n , Int.+[1+ d ] = Rat._/_ n (Nat.suc d)
... | _ , _ = Rat.0ℚ

instance
  ToRationalFloat : ToRational Float.Float
  ToRationalFloat .toℚ = toℚ-Float
