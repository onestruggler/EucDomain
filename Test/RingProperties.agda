-- Usage of the commutative ring structures of
-- Quantum.Synthesis.Ring.Properties.
--
-- Note: this module does not open Literals, so that the ℕ literals of
-- the solver calls ("solve 2 ...") are plain ℕ literals.

{-# OPTIONS --without-K --safe #-}

module Test.RingProperties where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
import GauInt.Properties as GauInt
open import GauInt.Base using (𝔾)

-- ----------------------------------------------------------------------
-- ℤ[i] is 𝔾: the ring structure of GauInt.Properties and the one
-- obtained from the generic proof for A [i] have the same type (the
-- same carrier and the same instance operations).

_ : IsCommutativeRing (_≡_ {A = 𝔾}) _+_ _*_ -_ 0# 1#
_ = GauInt.+-*-isCommutativeRing

_ : IsCommutativeRing (_≡_ {A = 𝔾}) _+_ _*_ -_ 0# 1#
_ = isCommutativeRing-ZComplex

-- ----------------------------------------------------------------------
-- A ring solver for ℤ[ω]. (ZSolver needs no decidable equality; one
-- could also use Algebra.Solver.Ring.Simple with DecEqOmega.)

module ZOmegaSolver = ZSolver commutativeRing-ZOmega
open ZOmegaSolver using (solve ; _:=_ ; _:+_ ; _:*_ ; _:-_ ; :-_)

diff-squares : ∀ (x y : ZOmega) -> (x + y) * (x - y) ≡ x * x - y * y
diff-squares = solve 2 (λ x y -> (x :+ y) :* (x :- y) := x :* x :- y :* y) refl

-- Constants such as ω can be treated as variables, and computed
-- afterwards (here ω * ω reduces to i).
binomial-ω : ∀ (x : ZOmega) -> (x + ω) * (x + ω) ≡ x * x + twice (ω * x) + i
binomial-ω x = solve 2 (λ x w -> (x :+ w) :* (x :+ w) := x :* x :+ (w :* x :+ w :* x) :+ w :* w) refl x ω

-- (1 + ω)(1 - ω) = 1 - i, via the ring laws.
_ : ∀ (x : ZOmega) -> (1# + x) * (1# - x) ≡ 1# - x * x
_ = λ x -> trans (diff-squares 1# x) (cong (_- x * x) (IsCommutativeRing.*-identityˡ isCommutativeRing-ZOmega 1#))

-- Using the laws of the bundles directly.
_ : ∀ (x y : QOmega) -> x * y ≡ y * x
_ = IsCommutativeRing.*-comm isCommutativeRing-QOmega

_ : ∀ (x y z : QRComplex) -> x * (y + z) ≡ x * y + x * z
_ = IsCommutativeRing.distribˡ isCommutativeRing-QRComplex

_ : ∀ (x : Z2) -> x + x ≡ 0#
_ = IsCommutativeRing.-‿inverseʳ isCommutativeRing-Z2

-- ----------------------------------------------------------------------
-- The rings built from 𝔻.

_ : CommutativeRing _ _
_ = commutativeRing-DOmega

_ : ∀ (x y : DRComplex) -> x * y ≡ y * x
_ = IsCommutativeRing.*-comm isCommutativeRing-DRComplex

module DOmegaSolver = ZSolver commutativeRing-DOmega

-- The proof-friendly variant dyadic′ satisfies the specification.
_ : ∀ a n -> toℚ (dyadic′ a n) ≡ _
_ = dyadic-spec′

-- adj and adj2 are ring homomorphisms.
_ : ∀ (x y : ZOmega) -> adj (x * y) ≡ adj x * adj y
_ = IsInvolutiveRingEndo.f-* adj-ZOmega

_ : ∀ (x : ZOmega) -> adj2 (adj2 x) ≡ x
_ = IsInvolutiveRingEndo.involutive adj2-ZOmega

_ : ∀ (x y : ZRootTwo) -> norm (x * y) ≡ norm x * norm y
_ = norm-*-ZRootTwo
