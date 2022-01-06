-- This file gives the definition of Gaussian Integers, and common
-- operations on them.

{-# OPTIONS --without-K --safe  #-}

module GauInt.Base where

open import Data.Bool using (Bool ; true ; false ; T ; not ; _∧_)
open import Data.Nat using (ℕ ; _≡ᵇ_)
open import Data.Integer renaming (-_ to -ℤ_ ; _-_ to _-ℤ_ ; _+_ to _+ℤ_ ; _*_ to _*ℤ_ ) hiding (NonZero)

infix  4 _==_ -- boolean equality on 𝔾.
infix  4 _==ℤ_ -- boolean equality on ℤ.
infixl 6 _+_ _-_
infixl 7 _*_
infix 8  -_
infixl 9 _ᶜ  -- conjugation on 𝔾.

-- A Gaussian integer is a pair of integers. 
infix 5 _+_i
data 𝔾 : Set where
  _+_i : ℤ -> ℤ -> 𝔾

-- Addition.
_+_ : 𝔾 -> 𝔾 -> 𝔾
(a + b i) + (c + d i) = x + y i where
  x = a +ℤ c
  y = b +ℤ d

-- Additive identity.  
0𝔾 : 𝔾
0𝔾 = 0ℤ + 0ℤ i

-- Additive inverse. 
-_ : 𝔾 -> 𝔾
- (a + b i) = (-ℤ a) + (-ℤ b) i

-- Subtraction.
_-_ : 𝔾 -> 𝔾 -> 𝔾
_-_ x y = x + (- y)


-- Multiplication.
_*_ : 𝔾 -> 𝔾 -> 𝔾
(a + b i) * (c + d i) = x + y i where
  x = a *ℤ c -ℤ b *ℤ d
  y = (a *ℤ d) +ℤ b *ℤ c

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

-- Conjugation of complex numbers retricted to Gaussian integers.
_ᶜ : 𝔾 -> 𝔾
_ᶜ (a + b i) = a + (-ℤ b) i

-- Rank. 
rank : 𝔾 -> ℕ
rank (a + b i) = ∣ a *ℤ a +ℤ b *ℤ b ∣

-- Boolean equality on ℤ.
_==ℤ_ : ℤ -> ℤ -> Bool
+_ n ==ℤ +_ m = n ≡ᵇ m
+_ n ==ℤ -[1+_] n₁ = false
-[1+_] n ==ℤ +_ n₁ = false
-[1+_] n ==ℤ -[1+_] m = n ≡ᵇ m

-- Boolean equality on 𝔾.
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


