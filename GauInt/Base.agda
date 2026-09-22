-- This file gives the definition of Gaussian Integers, and common
-- operations on them.
--
-- Gaussian integers are the ring ℤ[i] = ℤ [i] of the newsynth ring
-- framework (see Quantum.Synthesis.Ring), so the ring operations +,
-- *, -, the constants 0, 1, i, and the conjugation adj are all
-- inherited from the generic instances for A [i].

{-# OPTIONS --without-K --safe  #-}

module GauInt.Base where

open import Data.Bool using (Bool ; true ; false ; T ; not ; _∧_)
open import Data.Nat using (ℕ ; _≡ᵇ_)
open import Data.Integer using (ℤ ; +_ ; -[1+_] ; ∣_∣ ; 0ℤ ; 1ℤ)

-- The name i (the complex unit) is hidden, since it conflicts with
-- the notation a + b i below. The other hidden names are defined
-- for 𝔾 below, and become instances in GauInt.Instances.
open import Instances hiding (i ; _==_ ; rank ; NonZero ; nonZero)
open import Quantum.Synthesis.Ring using (_[i] ; Cplx)

infix  4 _==_ -- boolean equality on 𝔾.
infix  4 _==ℤ_ -- boolean equality on ℤ.
infixl 9 _ᶜ  -- conjugation on 𝔾.

-- A Gaussian integer is a pair of integers.
𝔾 : Set
𝔾 = ℤ [i]

-- The notation a + b i for Cplx a b.
infix 5 _+_i
pattern _+_i a b = Cplx a b

-- Additive identity.
0𝔾 : 𝔾
0𝔾 = 0ℤ + 0ℤ i

-- Multiplicative identity.
1𝔾 : 𝔾
1𝔾 = 1ℤ + 0ℤ i

-- imaginary unit i.
iG : 𝔾
iG = 0ℤ + 1ℤ i

-- Real and imaginary part.
Re : 𝔾 -> ℤ
Re (a + b i) = a

Im : 𝔾 -> ℤ
Im (a + b i) = b

-- Conjugation of complex numbers retricted to Gaussian integers. This
-- is the newsynth adjoint.
_ᶜ : 𝔾 -> 𝔾
_ᶜ = adj

-- Rank.
rank : 𝔾 -> ℕ
rank (a + b i) = ∣ a * a + b * b ∣

-- Boolean equality on ℤ.
_==ℤ_ : ℤ -> ℤ -> Bool
+_ n ==ℤ +_ m = n ≡ᵇ m
+_ n ==ℤ -[1+_] n₁ = false
-[1+_] n ==ℤ +_ n₁ = false
-[1+_] n ==ℤ -[1+_] m = n ≡ᵇ m

-- Boolean equality on 𝔾. Unlike the overloaded equality, it reduces
-- as soon as one component is known to differ, which is used by the
-- NonZero instances in GauInt.Instances.
_==_ : 𝔾 -> 𝔾 -> Bool
a + b i == c + d i = (a ==ℤ c) ∧ (b ==ℤ d)

-- NonZero predicate. Intended to use as implicit argument to deal
-- with the zero divisor case.
record NonZero (x : 𝔾) : Set where
  field
    nonZero : T (not ( x == 0𝔾))


-- ----------------------------------------------------------------------
-- Injections

-- I don't have good notation for this.
infix 5 _+0i'
_+0i' : ℤ -> 𝔾
_+0i' n = n + 0ℤ i

-- Injection of naturals are used more often.
infix 5 _+0i
_+0i : ℕ -> 𝔾
_+0i n = + n +0i'
