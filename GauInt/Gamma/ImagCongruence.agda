{-# OPTIONS --safe --without-K #-}

module GauInt.Gamma.ImagCongruence where
open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
import GauInt.Gamma.Congruence as G
import Integer.Congruence as IC
open import Integer.Parity using (parityBit-congruent)
open import Integer.Parity using (parityBit)
open import Data.Integer using (+_)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

imag-congruent : ∀ a b → G.Cong 2 a b → parityBit (im a) ≡ parityBit (im b)
imag-congruent a b (Cplx u v , h) = parityBit-congruent (im a) (im b)
  (u , trans (cong im h) (solve 3 (λ b u v → b :+ (u :* con (+ 2) :+ v :* con (+ 0)) :=
    b :+ con (+ 2) :* u) refl (im b) u v))
