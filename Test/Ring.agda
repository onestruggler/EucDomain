-- Sanity checks for Quantum.Synthesis.Ring: overloaded constants and
-- arithmetic in the various rings, checked by evaluation.

{-# OPTIONS --without-K --safe #-}

module Test.Ring where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
open import Data.Rational.Base using (ℚ)
open import Data.Maybe.Base using (just ; nothing)
open import Function.Base using (_∋_)
open import Data.Bool.Base using (true ; false)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring

-- The same literal in different rings.
_ : (ℤ ∋ 0) ≡ 0#
_ = refl
_ : (ZOmega ∋ -1) ≡ Omega 0 0 0 -1
_ = refl

-- ω is a primitive 8th root of unity in ℤ[ω], 𝔻[√2,i] and ℚ[ω].
_ : (ZOmega ∋ ω ^ 8) ≡ 1
_ = refl
_ : (ZOmega ∋ ω ^ 4) ≡ -1
_ = refl
_ : (DRComplex ∋ ω ^ 2) ≡ i
_ = refl
_ : (ZOmega ∋ ω ^ 2) ≡ +i
_ = refl
_ : (ZOmega ∋ -i * -i) ≡ -1
_ = refl
_ : (ZComplex ∋ -i * +i) ≡ 1
_ = refl
_ : (DRComplex ∋ i * -i) ≡ 1
_ = refl

-- √2 and 1/√2.
_ : (ZRootTwo ∋ √2 * √2) ≡ 2
_ = refl
_ : (DRootTwo ∋ √½ * √½) ≡ ½
_ = refl
_ : (DOmega ∋ √½ * √2) ≡ 1
_ = refl
_ : (DRootTwo ∋ ½ + ½) ≡ 1
_ = refl

-- Conjugations.
_ : (ZOmega ∋ adj ω * ω) ≡ 1
_ = refl
_ : (ZRootTwo ∋ (1 + √2) • ) ≡ 1 - √2
_ = refl
_ : norm (ZRootTwo ∋ 1 + √2) ≡ -1
_ = refl
_ : norm (ZOmega ∋ 1 + ω) ≡ 2
_ = refl

-- Division in fields.
_ : (QRootTwo ∋ 1 / (1 + √2)) ≡ -1 + √2
_ = refl
_ : (QOmega ∋ ω ⁻¹) ≡ adj ω
_ = refl
_ : (QComplex ∋ (1 + i) / (1 - i)) ≡ i
_ = refl

-- Homomorphisms.
_ : (DOmega ∋ fromZOmega (Omega 1 2 3 4)) ≡ Omega 1 2 3 4
_ = refl
_ : (DOmega ∋ fromDRComplex (Cplx √½ √½)) ≡ ω
_ = refl
_ : toQOmega (DRComplex ∋ ω) ≡ ω
_ = refl
_ : zroottwo-of-zomega (fromZRootTwo (3 + 2 * √2)) ≡ just (3 + 2 * √2)
_ = refl

-- Order on ℤ[√2]: 1.4 < √2 < 1.5.
_ : ((ZRootTwo ∋ 3 * √2) <ᵇ 5) ≡ true
_ = refl
_ : ((ZRootTwo ∋ 15 * √2) <ᵇ 21) ≡ false
_ = refl

-- Integer square roots and square roots in ℤ[√2].
_ : intsqrt 1000000 ≡ 1000
_ = refl
_ : intsqrt 99 ≡ 9
_ = refl
_ : zroottwo-root ((3 + 2 * √2) ^2) ≡ just (3 + 2 * √2)
_ = refl
_ : zroottwo-root (1 + √2) ≡ nothing
_ = refl

-- Floor on ℚ[√2].
_ : floor-of (QRootTwo ∋ 100 * √2) ≡ 141
_ = refl
_ : ceiling-of (QRootTwo ∋ -100 * √2) ≡ -141
_ = refl

-- Denominator exponents.
_ : denomexp (DRootTwo ∋ √½) ≡ 1
_ = refl
_ : denomexp (DOmega ∋ √½ ^ 5) ≡ 5
_ = refl

-- Printing, in the same format as newsynth.
_ : show (DRootTwo ∋ 1 - ½ * √2) ≡ "1 - 1/2*roottwo"
_ = refl
_ : show (ZComplex ∋ 2 - 3 * i) ≡ "2 - 3*i"
_ = refl
_ : show (DOmega ∋ √½ ^ 3 * (1 + ω)) ≡ "roothalf^3 * Omega 0 0 1 1"
_ = refl
_ : show (DRComplex ∋ ω) ≡ "roothalf * (1 + i)"
_ = refl
_ : show (ℚ ∋ -3 / 4) ≡ "-3/4"
_ = refl
