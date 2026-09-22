-- Tests for Quantum.Synthesis.EuclideanDomain, checked by evaluation.
-- The expected values were computed with the Haskell newsynth
-- reference implementation (except where noted).

{-# OPTIONS --without-K --safe #-}

module Test.EuclideanDomain where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Bool.Base using (true ; false)
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.EuclideanDomain

-- ----------------------------------------------------------------------
-- Haskell integer division

_ : map (λ (x , y) -> rounddiv x y)
      ((7 , 2) ∷ (-7 , 2) ∷ (7 , -2) ∷ (-7 , -2) ∷ (5 , 3) ∷ (-5 , 3) ∷ (6 , 4) ∷ (-6 , 4) ∷ [])
    ≡ (4 ∷ -3 ∷ -3 ∷ 4 ∷ 2 ∷ -2 ∷ 2 ∷ -1 ∷ [])
_ = refl

_ : map (λ (x , y) -> divMod x y) ((7 , 2) ∷ (-7 , 2) ∷ (7 , -2) ∷ (-7 , -2) ∷ [])
    ≡ ((3 , 1) ∷ (-4 , 1) ∷ (-4 , -1) ∷ (3 , -1) ∷ [])
_ = refl

_ : map (λ (x , y) -> quotRem x y) ((7 , 2) ∷ (-7 , 2) ∷ (7 , -2) ∷ (-7 , -2) ∷ [])
    ≡ ((3 , 1) ∷ (-3 , -1) ∷ (-3 , 1) ∷ (3 , -1) ∷ [])
_ = refl

-- ----------------------------------------------------------------------
-- ℤ

_ : euclid-gcd (ℤ ∋ 12) 18 ≡ 6
_ = refl

-- Haskell gives -6 (floored division); we get the associate 6.
_ : euclid-gcd (ℤ ∋ -12) -18 ≡ 6
_ = refl

_ : euclid-extract-power (ℤ ∋ 1000) 10 ≡ (3 , 1)
_ = refl

_ : inv-mod (ℤ ∋ 17) 5 ≡ just 7
_ = refl

_ : inv-mod (ℤ ∋ 18) 4 ≡ nothing
_ = refl

_ : map (is-unit {ℤ}) (-1 ∷ 2 ∷ 0 ∷ []) ≡ (true ∷ false ∷ false ∷ [])
_ = refl

-- ----------------------------------------------------------------------
-- ℤ[√2]

_ : divmod (ZRootTwo ∋ RootTwo 17 -5) (RootTwo 3 1) ≡ (RootTwo 9 -5 , RootTwo 0 1)
_ = refl

_ : euclid-gcd (ZRootTwo ∋ RootTwo 7 3) (RootTwo 5 1) ≡ RootTwo -1 -1
_ = refl

_ : extended-euclid (ZRootTwo ∋ RootTwo 7 3) (RootTwo 5 1)
    ≡ (RootTwo 1 -2 , RootTwo 0 2 , RootTwo -3 4 , RootTwo 1 -4 , RootTwo -1 -1)
_ = refl

-- The identities of extended-euclid.
module RootTwoEE where
  T3 = ZRootTwo × ZRootTwo × ZRootTwo
  x y : ZRootTwo
  x = RootTwo 7 3
  y = RootTwo 5 1

  _ : (T3 ∋ let (a , b , s , t , d) = extended-euclid x y in
      (a * x + b * y - d , s * x + t * y , a * t - b * s)) ≡ (0 , 0 , 1)
  _ = refl

_ : euclid-inverse (ZRootTwo ∋ RootTwo 3 2) ≡ just (RootTwo 3 -2)
_ = refl

_ : euclid-inverse (ZRootTwo ∋ RootTwo 3 1) ≡ nothing
_ = refl

_ : euclid-inverse (ZRootTwo ∋ (1 + √2) ^ 5) ≡ just ((-1 + √2) ^ 5)
_ = refl

_ : euclid-extract-power (ZRootTwo ∋ RootTwo 8 4) √2 ≡ (5 , RootTwo 1 1)
_ = refl

_ : inv-mod (ZRootTwo ∋ 7) (RootTwo 3 1) ≡ nothing
_ = refl

-- 3 + √2 is a prime of norm 7, so 2 + √2 is invertible modulo it.
_ : inv-mod (ZRootTwo ∋ RootTwo 3 1) (RootTwo 2 1) ≡ just -1
_ = refl

_ : euclid-associates (ZRootTwo ∋ RootTwo 1 1) (RootTwo 1 -1) ≡ true
_ = refl

_ : euclid-associates (ZRootTwo ∋ RootTwo 3 1) (RootTwo 3 -1) ≡ false
_ = refl

-- ----------------------------------------------------------------------
-- ℤ[ω]

_ : divmod (ZOmega ∋ Omega 3 -7 2 11) (Omega 1 0 2 1) ≡ (Omega -1 1 -4 4 , Omega -2 -1 -1 1)
_ = refl

_ : euclid-gcd (ZOmega ∋ Omega 3 -7 2 11) (Omega 1 0 2 1) ≡ Omega -2 -1 -1 1
_ = refl

_ : extended-euclid (ZOmega ∋ Omega 3 -7 2 11) (Omega 1 0 2 5)
    ≡ (Omega 1 1 -2 1 , Omega -4 -2 5 -5 , Omega 3 -4 6 -3 , Omega -2 12 -21 12 , Omega 1 1 1 0)
_ = refl

_ : euclid-inverse (ZOmega ∋ 1 + ω) ≡ nothing
_ = refl

_ : euclid-inverse (ZOmega ∋ 1 + √2 + ω) ≡ nothing
_ = refl

_ : euclid-inverse (ZOmega ∋ ω ^ 3 * (1 + √2)) ≡ just (ω ^ 5 * (-1 + √2))
_ = refl


-- ----------------------------------------------------------------------
-- ℤ[i] (the instances of GauInt)

-- Same as newsynth.
_ : divmod (ZComplex ∋ Cplx 17 -5) (Cplx 3 1) ≡ (Cplx 5 -3 , Cplx -1 -1)
_ = refl

_ : euclid-associates (euclid-gcd (ZComplex ∋ Cplx 17 -5) (Cplx 3 1)) (Cplx -1 -1) ≡ true
_ = refl

_ : euclid-gcd (ZComplex ∋ Cplx 12 18) 8 ≡ -2
_ = refl

_ : euclid-inverse (ZComplex ∋ Cplx 0 -1) ≡ just i
_ = refl

_ : euclid-inverse (ZComplex ∋ Cplx 1 1) ≡ nothing
_ = refl

module ComplexEE where
  T3 = ZComplex × ZComplex × ZComplex
  x y : ZComplex
  x = Cplx 17 -5
  y = Cplx 3 1

  _ : (T3 ∋ let (a , b , s , t , d) = extended-euclid x y in
      (a * x + b * y - d , s * x + t * y , a * t - b * s)) ≡ (0 , 0 , 1)
  _ = refl

-- A tie: GauInt rounds halves down, newsynth rounds them up
-- (newsynth: divmod 1 2 = (1, -1)).
_ : divmod (ZComplex ∋ 1) 2 ≡ (0 , 1)
_ = refl
