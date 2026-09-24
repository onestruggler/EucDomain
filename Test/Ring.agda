-- Sanity checks for Quantum.Synthesis.Ring: overloaded constants and
-- arithmetic in the various rings, checked by evaluation.

{-# OPTIONS --without-K --safe #-}

module Test.Ring where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
import Data.Nat.Base as Nat
open import Data.List.Base using (List ; [] ; _∷_ ; map ; concatMap ; foldr)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ)
open import Data.Maybe.Base using (just ; nothing)
open import Function.Base using (_∋_)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_)

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

-- Different bases coexist on the same carrier, including a client-defined tag.
data FourBase : Set where

instance
  DenomExpDyadicFour : DenomExp FourBase Dyadic
  DenomExpDyadicFour .DenomExp.denomexp (Dyadic' _ k _) = Nat.⌈ k /2⌉
  DenomExpDyadicFour .DenomExp.denomexp-factor a k = a * 4 ^ k

_ : denomexp (DRootTwo ∋ ½) ≡ 2
_ = refl
_ : denomexpBy TwoBase (DRootTwo ∋ ½) ≡ 1
_ = refl
_ : denomexp (DOmega ∋ ½) ≡ 2
_ = refl
_ : denomexpBy TwoBase (DOmega ∋ ½) ≡ 1
_ = refl
_ : denomexpBy TwoBase (dyadic -6 4) ≡ 3
_ = refl
_ : denomexpBy TwoBase (dyadic 0 7) ≡ 0
_ = refl
_ : denomexpBy TwoBase (Dyadic ∋ -3) ≡ 0
_ = refl
_ : denomexp-factorBy TwoBase (Dyadic ∋ ½) 3 ≡ 4
_ = refl
_ : denomexp-decomposeBy {Dyadic} {ℤ} TwoBase (dyadic 1 3) ≡ (1 , 3)
_ = refl
_ : denomexp-decomposeBy {Dyadic} {ℤ} FourBase (dyadic 1 3) ≡ (2 , 2)
_ = refl
_ : denomexpBy TwoBase ((DRootTwo ∋ √½) , (DOmega ∋ ½ ^ 3)) ≡ 3
_ = refl
_ : denomexp-decomposeBy {Dyadic [i]} {ZComplex} TwoBase
      (Cplx ½ (dyadic -1 3)) ≡ (Cplx 4 -1 , 3)
_ = refl
_ : denomexpBy TwoBase (List Dyadic ∋ []) ≡ 0
_ = refl
_ : denomexp-decomposeBy {List Dyadic} {List ℤ} FourBase
      (½ ∷ dyadic 1 3 ∷ []) ≡ ((8 ∷ 2 ∷ []) , 2)
_ = refl
_ : showsPrec-DenomExpBy {Dyadic} {ℤ} TwoBase "half" 0 (dyadic 1 3)
      ≡ "half^3 * 1"
_ = refl
_ : showsPrec-DenomExpBy {Dyadic} {ℤ} TwoBase "half" 0 ½ ≡ "half * 1"
_ = refl
_ : showsPrec-DenomExpBy {Dyadic} {ℤ} TwoBase "half" 0 3 ≡ "3"
_ = refl

-- Ramification identities and units underlying the complex-base formulas.
_ : (ZComplex ∋ (1 + i) ^ 2) ≡ 2 * i
_ = refl
_ : (ZOmega ∋ 1 + i) ≡ ω * √2
_ = refl
_ : (ZOmega ∋ (1 + ω) ^ 2) ≡ √2 * (ω * (1 + √2))
_ = refl
_ : (ZOmega ∋ (ω * (1 + √2)) * (adj ω * (√2 - 1))) ≡ 1
_ = refl

inverse-one-plus-omega : DOmega
inverse-one-plus-omega = ½ * (1 - ω + ω ^ 2 - ω ^ 3)

_ : (1 + ω) * inverse-one-plus-omega ≡ 1
_ = refl
_ : denomexp-decomposeBy {DComplex} {ZComplex} OnePlusIBase (½ * (1 - i)) ≡ (1 , 1)
_ = refl
_ : denomexp-decomposeBy {DComplex} {ZComplex} OnePlusIBase ½ ≡ (i , 2)
_ = refl
_ : denomexp-decomposeBy {DRComplex} {ZRootTwo [i]} OnePlusIBase (½ * (1 - i)) ≡ (1 , 1)
_ = refl
_ : denomexp-decomposeBy {DOmega} {ZOmega} OnePlusIBase (½ * (1 - i)) ≡ (1 , 1)
_ = refl
_ : denomexp-decomposeBy {DOmega} {ZOmega} OnePlusOmegaBase inverse-one-plus-omega ≡ (1 , 1)
_ = refl
_ : map (λ k -> denomexpBy OnePlusOmegaBase (inverse-one-plus-omega ^ k))
      (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 7 ∷ []) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 7 ∷ [])
_ = refl
_ : denomexpBy OnePlusIBase (DComplex ∋ (½ * (1 - i)) ^ 7) ≡ 7
_ = refl
-- These carriers have different distinguished whole rings.
_ : denomexpBy OnePlusIBase (DRComplex ∋ ω) ≡ 1
_ = refl
_ : denomexpBy OnePlusIBase (DOmega ∋ ω) ≡ 0
_ = refl
_ : denomexpBy OnePlusOmegaBase (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexpBy OnePlusOmegaBase (DOmega ∋ 0) ≡ 0
_ = refl
_ : denomexpBy OnePlusIBase (DComplex ∋ 0) ≡ 0
_ = refl

private
  -- Independent oracle: multiply by the actual base, test integrality
  -- by a WholePart round trip, and reject every smaller exponent.
  check-denominator : {A B : Set} (Base : Set)
    {{_ : Ring A}} {{_ : DecEq A}} {{_ : WholePart A B}} {{_ : DenomExp Base A}} -> A -> A -> Bool
  check-denominator {A} {B} Base base x =
    integral (x * base ^ k) ∧ no-smaller k x ∧
    (denomexp-factorBy Base x (Nat.suc k) == x * base ^ (Nat.suc k))
    where
      k = denomexpBy Base x
      integral : A -> Bool
      integral y = from-whole {A} {B} (to-whole y) == y
      no-smaller : Nat.ℕ -> A -> Bool
      no-smaller Nat.zero y = true
      no-smaller (Nat.suc n) y = not (integral y) ∧ no-smaller n (y * base)

  coefficients : List Dyadic
  coefficients = (- ½) ∷ 0 ∷ ½ ∷ []

  complex-samples : List DComplex
  complex-samples = concatMap (λ a -> map (Cplx a) coefficients) coefficients

  four-coefficients : {A : Set} -> (Dyadic -> Dyadic -> Dyadic -> Dyadic -> A) -> List A
  four-coefficients f = concatMap (λ a -> concatMap (λ b ->
    concatMap (λ c -> map (f a b c) coefficients) coefficients) coefficients) coefficients

-- 9 Gaussian, 81 biquadratic, and 81 cyclotomic samples, including
-- cancellations, negative coefficients, zero and unequal coordinate exponents.
_ : foldr _∧_ true (map (check-denominator {DComplex} {ZComplex} OnePlusIBase (1 + i)) complex-samples) ≡ true
_ = refl
_ : foldr _∧_ true (map (check-denominator {DRComplex} {ZRootTwo [i]} OnePlusIBase (1 + i))
      (four-coefficients (λ a b c d -> Cplx (RootTwo a b) (RootTwo c d)))) ≡ true
_ = refl
_ : foldr _∧_ true (map (check-denominator {DOmega} {ZOmega} OnePlusIBase (1 + i))
      (four-coefficients (λ a b c d -> Omega (½ * a) (½ * b) (½ * c) (½ * d)))) ≡ true
_ = refl
_ : foldr _∧_ true (map (check-denominator {DOmega} {ZOmega} OnePlusOmegaBase (1 + ω))
      (four-coefficients (λ a b c d -> Omega (½ * a) (½ * b) (½ * c) (½ * d)))) ≡ true
_ = refl

-- Existing default formatting remains unchanged.
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
