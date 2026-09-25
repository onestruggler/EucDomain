{-# OPTIONS --safe --without-K #-}

module Test.GammaDenominator where

import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Ring.Properties.DyadicComplex as D
import Quantum.Synthesis.Ring.Properties.GammaDenominator as G
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Nat using (s≤s; z≤n; _≤_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Zero/integral inputs must not acquire a negative exponent on cancellation.
_ : R.denomexp-decomposeBy {R.DComplex} {R.ZComplex} R.OnePlusIBase
  (R.Cplx (R.dyadic (+ 0) 7) (R.dyadic (+ 0) 4)) ≡ (R.Cplx (+ 0) (+ 0) , 0)
_ = refl

_ : R.denomexp-decomposeBy {R.DComplex} {R.ZComplex} R.OnePlusIBase
  (D.embed (R.Cplx (+ 2) (+ 2))) ≡ (R.Cplx (+ 2) (+ 2) , 0)
_ = refl

-- Equal odd parity cancels exactly the factor used by the soundness proof.
negative : R.DComplex
negative = R.Cplx (R.dyadic -[1+ 0 ] 2) (R.dyadic -[1+ 2 ] 2)

_ : R.denomexp-decomposeBy {R.DComplex} {R.ZComplex} R.OnePlusIBase negative ≡
  (R.Cplx (+ 2) (+ 1) , 3)
_ = refl

-- Unequal coordinate exponents exercise alignment before the parity test.
_ : R.denomexp-decomposeBy {R.DComplex} {R.ZComplex} R.OnePlusIBase
  (R.Cplx (R.dyadic (+ 1) 2) (R.dyadic (+ 1) 1)) ≡ (R.Cplx -[1+ 0 ] -[1+ 1 ] , 4)
_ = refl

_ : R.denomexp-decomposeBy {R.DComplex} {R.ZComplex} R.OnePlusIBase
  (R.Cplx (R.dyadic (+ 0) 0) (R.dyadic (+ 1) 3)) ≡ (R.Cplx (+ 1) (+ 0) , 6)
_ = refl

-- The proof covers redundant exponents as well as the chosen one.
_ : D.embed (R.to-whole {R.DComplex} {R.ZComplex}
      (R.denomexp-factorBy R.OnePlusIBase negative 5)) ≡ R.denomexp-factorBy R.OnePlusIBase negative 5
_ = G.denominator-factor-whole-at negative 5 (s≤s (s≤s (s≤s z≤n)))

-- Lower bounds rule out *any* integer numerator at a smaller exponent.
negative-needs-three : ¬ G.Clears negative 2
negative-needs-three h = impossible (G.denominator-minimal negative 2 h)
  where
  impossible : 3 ≤ 2 → ⊥
  impossible (s≤s (s≤s ()))

half-real-needs-two : ¬ G.Clears (R.Cplx (R.dyadic (+ 1) 1) (R.dyadic (+ 0) 0)) 1
half-real-needs-two h = impossible
  (G.denominator-minimal (R.Cplx (R.dyadic (+ 1) 1) (R.dyadic (+ 0) 0)) 1 h)
  where
  impossible : 2 ≤ 1 → ⊥
  impossible (s≤s ())

mixed-needs-four : ¬ G.Clears (R.Cplx (R.dyadic (+ 1) 2) (R.dyadic (+ 1) 1)) 3
mixed-needs-four h = impossible
  (G.denominator-minimal (R.Cplx (R.dyadic (+ 1) 2) (R.dyadic (+ 1) 1)) 3 h)
  where
  impossible : 4 ≤ 3 → ⊥
  impossible (s≤s (s≤s (s≤s ())))
