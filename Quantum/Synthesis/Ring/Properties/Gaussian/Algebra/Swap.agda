{-# OPTIONS --safe --without-K #-}

-- Commutative rearrangements of Gaussian-integer products, kept outside
-- Quantum.Synthesis.Ring.Properties.Gaussian.Algebra so that wholesale openings of it never see the name swap.
module Quantum.Synthesis.Ring.Properties.Gaussian.Algebra.Swap where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_*_)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra using (module GaussianSolver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open GaussianSolver

swap : ∀ x y z → x * (y * z) ≡ y * (x * z)
swap = solve 3 (λ x y z → x :* (y :* z) := y :* (x :* z)) refl

product-scale : ∀ a b x y → (a * b) * (x * y) ≡ (a * x) * (b * y)
product-scale = solve 4 (λ a b x y → (a :* b) :* (x :* y) := (a :* x) :* (b :* y)) refl
