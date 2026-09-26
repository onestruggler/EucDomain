{-# OPTIONS --safe --without-K #-}

-- The faithful Gaussian embedding and the inverse gamma action in 𝔻[i].
module Quantum.Synthesis.Ring.Properties.DyadicComplex where

open import Quantum.Synthesis.Ring using
  (Dyadic; Dyadic'; dyadic; DComplex; ZComplex; Cplx; _[i]; integer-of-dyadic)
import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Ring.Properties as RP
import Quantum.Synthesis.Ring.Properties.Dyadic as DP
import Quantum.Synthesis.Ring.Properties.Hom as Hom
open import Instances as TC using (_+_; _-_; _*_; -_; _^_; 0#; 1#)
open import Algebra.Bundles using (CommutativeRing)
import Typeclasses.Properties as Power
import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma as G
import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra as ZG
open import Data.Integer.Base using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ZP
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)
open import Data.Bool.Base using (T)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

integer : ℤ → Dyadic
integer a = Dyadic' a zero _

abstract
  canonical : ∀ (x : Dyadic) → dyadic (Dyadic.numerator x) (Dyadic.exponent x) ≡ x
  canonical = DP.dyadic-canonical

integer-+ : ∀ a b → integer (a + b) ≡ integer a + integer b
integer-+ a b = trans (sym (canonical (integer (a + b))))
  (cong (λ t → dyadic (t + b) zero) (sym (ZP.*-identityʳ a)))

integer-* : ∀ a b → integer (a * b) ≡ integer a * integer b
integer-* a b = sym (canonical (integer (a * b)))

integer-neg : ∀ a → integer (- a) ≡ - integer a
integer-neg a = sym (canonical (integer (- a)))

integer-sub : ∀ a b → integer (a - b) ≡ integer a - integer b
integer-sub a b = trans (integer-+ a (- b)) (cong (λ t → integer a + t) (integer-neg b))

integer-fromℤ : ∀ a → (TC.fromℤ a) ≡ integer a
integer-fromℤ (+ zero) = refl
integer-fromℤ (+ suc n) = refl
integer-fromℤ -[1+ n ] = refl

whole-integer : ∀ a → integer-of-dyadic (integer a) zero ≡ a
whole-integer a = ZP.*-identityʳ a

embed : ZComplex → DComplex
embed (Cplx a b) = Cplx (integer a) (integer b)

embed-+ : ∀ a b → embed (a + b) ≡ embed a + embed b
embed-+ (Cplx a b) (Cplx c d) = cong₂ Cplx (integer-+ a c) (integer-+ b d)

embed-* : ∀ a b → embed (a * b) ≡ embed a * embed b
embed-* (Cplx a b) (Cplx c d) = cong₂ Cplx
  (trans (integer-sub (a * c) (b * d)) (cong₂ _-_ (integer-* a c) (integer-* b d)))
  (trans (integer-+ (a * d) (b * c)) (cong₂ _+_ (integer-* a d) (integer-* b c)))

embed-neg : ∀ a → embed (- a) ≡ - embed a
embed-neg (Cplx a b) = cong₂ Cplx (integer-neg a) (integer-neg b)

embed-adj : ∀ a → embed (TC.adj a) ≡ TC.adj (embed a)
embed-adj (Cplx a b) = cong (Cplx (integer a)) (integer-neg b)

embed-whole : ∀ a → R.from-whole {DComplex} {ZComplex} a ≡ embed a
embed-whole (Cplx a b) = cong₂ Cplx (integer-fromℤ a) (integer-fromℤ b)

whole-embed : ∀ a → R.to-whole {DComplex} {ZComplex} (embed a) ≡ a
whole-embed (Cplx a b) = cong₂ Cplx (whole-integer a) (whole-integer b)

embed-injective : ∀ {a b} → embed a ≡ embed b → a ≡ b
embed-injective {a} {b} h = trans (sym (whole-embed a))
  (trans (cong (R.to-whole {DComplex} {ZComplex}) h) (whole-embed b))

integer-isRingHom : Hom.IsRingHom integer
integer-isRingHom = record
  { multiplicative = record { f-* = integer-* ; f-1 = refl }
  ; f-+ = integer-+ ; f-0 = refl ; f-neg = integer-neg }

embed-isRingHom : Hom.IsRingHom embed
embed-isRingHom = RP.mapCoefficients-Cplx-isRingHom integer-isRingHom

adj-isRingHom : Hom.IsRingHom {DComplex} {DComplex} TC.adj
adj-isRingHom = RP.adj-isRingHom-DComplex

open import Algebra.Morphism.Structures using (IsRingMonomorphism)

embed-isRingMonomorphism : IsRingMonomorphism (Hom.instanceRawRing ZComplex) (Hom.instanceRawRing DComplex) embed
embed-isRingMonomorphism = record
  { isRingHomomorphism = Hom.toRingHomomorphism embed-isRingHom
  ; injective = embed-injective }

integer-isRingMonomorphism : IsRingMonomorphism (Hom.instanceRawRing ℤ) (Hom.instanceRawRing Dyadic) integer
integer-isRingMonomorphism = record
  { isRingHomomorphism = Hom.toRingHomomorphism integer-isRingHom
  ; injective = λ {a} {b} h -> trans (sym (whole-integer a))
      (trans (cong (λ x -> integer-of-dyadic x zero) h) (whole-integer b)) }

ring : CommutativeRing _ _
ring = RP.commutativeRing-DComplex

open CommutativeRing ring public using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-assoc; *-comm; *-identityˡ; *-identityʳ)
module Powers = Power.Powers {A = DComplex} {{R.SemiRingCplx}}
  (CommutativeRing.*-isCommutativeMonoid ring)

gamma inverseGamma : DComplex
gamma = 1# + TC.i
inverseGamma = TC.½ * (1# - TC.i)

inverse-gamma : inverseGamma * gamma ≡ 1#
inverse-gamma = refl

product-swap : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
product-swap = Powers.product-swap

inverse-powers : ∀ n → (inverseGamma ^ n) * (gamma ^ n) ≡ 1#
inverse-powers = Powers.inverse-powers inverseGamma gamma inverse-gamma

gamma-cancel : ∀ n {x y : DComplex} → (gamma ^ n) * x ≡ (gamma ^ n) * y → x ≡ y
gamma-cancel n {x} {y} h = Powers.cancel-powers inverseGamma gamma inverse-gamma n {a = x} {b = y} h

restore-cleared : ∀ n (z : DComplex) (w : ZComplex) →
  (gamma ^ n) * z ≡ embed w → (inverseGamma ^ n) * embed w ≡ z
restore-cleared n z w h =
  trans {j = a * (b * z)} (cong (a *_) {x = embed w} {y = b * z} (sym h))
    (trans {j = (a * b) * z} (sym (*-assoc a b z))
      (trans {j = 1# * z} (cong (_* z) {x = a * b} {y = 1#} (inverse-powers n)) (*-identityˡ z)))
  where
  a = inverseGamma ^ n
  b = gamma ^ n

clear-restored : ∀ n (z : DComplex) → (gamma ^ n) * ((inverseGamma ^ n) * z) ≡ z
clear-restored n z = trans {j = (a * b) * z} (sym (*-assoc a b z))
  (trans {j = 1# * z} (cong (_* z) {x = a * b} {y = 1#}
    (trans (*-comm a b) (inverse-powers n))) (*-identityˡ z))
  where
  a = gamma ^ n
  b = inverseGamma ^ n

module Scalar = CommutativeRing RP.commutativeRing-𝔻
module ScalarPowers = Power.Powers {A = Dyadic} {{R.SemiRingDyadic}} Scalar.*-isCommutativeMonoid
module EmbedPowers = Power.MapPowers {A = ZComplex} {B = DComplex}
  {{R.SemiRingCplx}} {{R.SemiRingCplx}}
  (CommutativeRing.*-isCommutativeMonoid ZG.gaussianRing)
  (CommutativeRing.*-isCommutativeMonoid ring) embed refl embed-*

embed-gamma : embed G.γ ≡ gamma
embed-gamma = refl

embed-power : ∀ n → embed (G.powγ n) ≡ gamma ^ n
embed-power zero = refl
embed-power (suc n) = trans (embed-* (G.powγ n) G.γ)
  (trans (cong₂ _*_ (embed-power n) embed-gamma)
    (trans (*-comm (gamma ^ n) gamma) (sym (Powers.^-suc gamma n))))

real : Dyadic → DComplex
real a = Cplx a 0#

from-integer-complex : ∀ a → TC.fromℤ {DComplex} a ≡ real (integer a)
from-integer-complex (+ zero) = refl
from-integer-complex (+ suc n) = refl
from-integer-complex -[1+ n ] = refl

imaginary : ∀ b → (TC.i {DComplex}) * real b ≡ Cplx 0# b
imaginary b = cong₂ Cplx
  (cong (λ x → x - 0#) (Scalar.zeroˡ b))
  (trans (Scalar.+-identityˡ (1# * b)) (Scalar.*-identityˡ b))

real-imaginary : ∀ a b → real a + (TC.i {DComplex}) * real b ≡ Cplx a b
real-imaginary a b = trans {j = real a + Cplx 0# b}
  (cong (λ x → real a + x) {x = TC.i * real b} {y = Cplx 0# b} (imaginary b))
  (cong₂ Cplx (Scalar.+-identityʳ a) (Scalar.+-identityˡ b))

fromZComplex-embed : ∀ z → R.fromZComplex {DComplex} z ≡ embed z
fromZComplex-embed (Cplx a b) = trans {j = real (integer a) + TC.i * real (integer b)}
  (cong₂ _+_ (from-integer-complex a)
    (cong (TC.i *_) {x = TC.fromℤ b} {y = real (integer b)} (from-integer-complex b)))
  (real-imaginary (integer a) (integer b))

real-* : ∀ a b → real (a * b) ≡ real a * real b
real-* a b = sym (cong₂ Cplx (Scalar.+-identityʳ (a * b))
  (trans (cong₂ _+_ (Scalar.zeroʳ a) (Scalar.zeroˡ b)) (Scalar.+-identityˡ 0#)))

module RealPowers = Power.MapPowers {A = Dyadic} {B = DComplex}
  {{R.SemiRingDyadic}} {{R.SemiRingCplx}}
  Scalar.*-isCommutativeMonoid (CommutativeRing.*-isCommutativeMonoid ring)
  real refl real-*

private
  one-canonical : ∀ n → T (R.Canonical (+ 1) n)
  one-canonical zero = tt
  one-canonical (suc n) = tt

one-over-two-power : ℕ → Dyadic
one-over-two-power n = Dyadic' (+ 1) n (one-canonical n)

half-power : ∀ n → (TC.½ {Dyadic}) ^ n ≡ one-over-two-power n
half-power zero = refl
half-power (suc n) = trans (ScalarPowers.^-suc TC.½ n)
  (cong (TC.½ *_) (half-power n))

dyadic-value : ∀ a n → dyadic a n ≡ integer a * ((TC.½ {Dyadic}) ^ n)
dyadic-value a n = trans (cong (λ t → dyadic t n) (sym (ZP.*-identityʳ a)))
  (cong (integer a *_) (sym (half-power n)))

bit-value : ∀ x → x ≡ integer (Dyadic.numerator x) * ((TC.½ {Dyadic}) ^ Dyadic.exponent x)
bit-value x = trans (sym (canonical x)) (dyadic-value (Dyadic.numerator x) (Dyadic.exponent x))

common-real : ∀ x n → Dyadic.exponent x ≤ n →
  x ≡ integer (integer-of-dyadic x n) * ((TC.½ {Dyadic}) ^ n)
common-real x n h = trans (sym (DP.integer-of-dyadic-correct x n h))
  (dyadic-value (integer-of-dyadic x n) n)

scale-real : ∀ a b t → embed (Cplx a b) * real t ≡ Cplx (integer a * t) (integer b * t)
scale-real a b t = cong₂ Cplx
  (trans (cong (λ v → integer a * t - v) (Scalar.zeroʳ (integer b))) (Scalar.+-identityʳ (integer a * t)))
  (trans (cong (λ v → v + integer b * t) (Scalar.zeroʳ (integer a))) (Scalar.+-identityˡ (integer b * t)))

scale-half : ∀ a b n → embed (Cplx a b) * ((TC.½ {DComplex}) ^ n) ≡
  Cplx (integer a * ((TC.½ {Dyadic}) ^ n)) (integer b * ((TC.½ {Dyadic}) ^ n))
scale-half a b n = trans (cong (embed (Cplx a b) *_) (sym (RealPowers.map-power TC.½ n)))
  (scale-real a b ((TC.½ {Dyadic}) ^ n))

bitNumerator : DComplex → ℕ → ZComplex
bitNumerator (Cplx a b) n = Cplx (integer-of-dyadic a n) (integer-of-dyadic b n)

common-value : ∀ (z : DComplex) n → Dyadic.exponent (_[i].re z) ≤ n → Dyadic.exponent (_[i].im z) ≤ n →
  z ≡ embed (bitNumerator z n) * ((TC.½ {DComplex}) ^ n)
common-value (Cplx a b) n ha hb = trans (cong₂ Cplx (common-real a n ha) (common-real b n hb))
  (sym (scale-half (integer-of-dyadic a n) (integer-of-dyadic b n) n))

gamma-square-half : (gamma * gamma) * (TC.½ {DComplex}) ≡ TC.i
gamma-square-half = refl

gamma-half-power : ∀ n → (gamma ^ (n + n)) * ((TC.½ {DComplex}) ^ n) ≡ (TC.i {DComplex}) ^ n
gamma-half-power n = trans (cong (_* ((TC.½ {DComplex}) ^ n)) (Powers.^-double gamma n))
  (trans (sym (Powers.^-mul (gamma * gamma) TC.½ n)) (cong (λ x → x ^ n) gamma-square-half))

coarseNumerator : DComplex → ℕ → ZComplex
coarseNumerator z n = ((TC.i {ZComplex}) ^ n) * bitNumerator z n

coarse-clears : ∀ (z : DComplex) n → Dyadic.exponent (_[i].re z) ≤ n → Dyadic.exponent (_[i].im z) ≤ n →
  (gamma ^ (n + n)) * z ≡ embed (coarseNumerator z n)
-- Explicit endpoints prevent reverse inference through dyadic multiplication
-- and exponentiation. The algebraic proof and computed numerator are unchanged.
coarse-clears z n ha hb =
  trans {j = g * (a * h)} (cong (g *_) {x = z} {y = a * h} (common-value z n ha hb))
    (trans {j = a * (g * h)} (Powers.exchange g a h)
      (trans {j = a * u} (cong (a *_) {x = g * h} {y = u} (gamma-half-power n))
        (trans {j = u * a} (*-comm a u)
          (trans {j = v * a} (cong (_* a) {x = u} {y = v} (sym (EmbedPowers.map-power TC.i n)))
            (sym (embed-* ((TC.i {ZComplex}) ^ n) (bitNumerator z n)))))))
  where
  g = gamma ^ (n + n)
  a = embed (bitNumerator z n)
  h = (TC.½ {DComplex}) ^ n
  u = (TC.i {DComplex}) ^ n
  v = embed ((TC.i {ZComplex}) ^ n)
