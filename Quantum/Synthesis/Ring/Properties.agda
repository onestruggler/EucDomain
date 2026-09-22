-- The rings of the newsynth ring framework (Quantum.Synthesis.Ring)
-- are commutative rings, as stdlib structures IsCommutativeRing (with
-- propositional equality) for the operations of the instances.
--
-- * Generic: if A is a commutative ring, then so are A [√2], A [i]
--   and A [ω] (Properties.RootTwo, Properties.Cplx,
--   Properties.Omega).
--
-- * ℤ₂ (Properties.Z2).
--
-- * 𝔻 = ℤ[½] (Properties.Dyadic), via the injective ring
--   homomorphism toℚ : 𝔻 → ℚ, using the specification DyadicSpec of
--   the smart constructor "dyadic" (proved as dyadic-spec′). The
--   results are stated in the parameterized modules WithDyadicSpec and
--   WithDyadicSpec-Adjoint below, which are instantiated with the
--   proof at the end of this module.
--
-- * The particular rings ℤ[√2], ℚ[√2], ℤ[i], ℚ[i], ℚ[√2,i], ℤ[ω],
--   ℚ[ω], 𝔻, 𝔻[√2], 𝔻[i], 𝔻[√2,i], 𝔻[ω].
--
-- * adj and adj2 are involutive ring automorphisms of all these rings
--   (generic lemmas adj-RootTwo, adj2-Cplx, ... and instances below),
--   and the norms of ℤ[√2] and ℤ[i] are multiplicative.
--
-- For ℤ and ℚ, the instance operations are definitionally the stdlib
-- ones, so the stdlib proofs are used.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer.Base using (ℤ ; +_)
import Data.Integer.Solver
import Data.Integer.Properties as ℤP
open import Data.Rational.Base using (ℚ)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Quantum.Synthesis.Ring

open import Quantum.Synthesis.Ring.Properties.Common public
open import Quantum.Synthesis.Ring.Properties.RootTwo public
open import Quantum.Synthesis.Ring.Properties.Cplx public
open import Quantum.Synthesis.Ring.Properties.Omega public
open import Quantum.Synthesis.Ring.Properties.Z2 public
open import Quantum.Synthesis.Ring.Properties.Dyadic public
open import Quantum.Synthesis.Ring.Properties.Hom public using (IsRingEndo ; IsInvolutiveRingEndo ; id-isInvolutiveRingEndo)

-- ----------------------------------------------------------------------
-- * ℤ and ℚ

isCommutativeRing-ℤ : IsCommutativeRing (_≡_ {A = ℤ}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ℤ = ℤP.+-*-isCommutativeRing

commutativeRing-ℤ : CommutativeRing 0ℓ 0ℓ
commutativeRing-ℤ = record { isCommutativeRing = isCommutativeRing-ℤ }

isCommutativeRing-ℚ : IsCommutativeRing (_≡_ {A = ℚ}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ℚ = ℚP.+-*-isCommutativeRing

commutativeRing-ℚ : CommutativeRing 0ℓ 0ℓ
commutativeRing-ℚ = record { isCommutativeRing = isCommutativeRing-ℚ }

-- ----------------------------------------------------------------------
-- * Extensions of ℤ and ℚ

isCommutativeRing-ZRootTwo : IsCommutativeRing (_≡_ {A = ZRootTwo}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZRootTwo = isCommutativeRing-RootTwo isCommutativeRing-ℤ

commutativeRing-ZRootTwo : CommutativeRing 0ℓ 0ℓ
commutativeRing-ZRootTwo = record { isCommutativeRing = isCommutativeRing-ZRootTwo }

isCommutativeRing-QRootTwo : IsCommutativeRing (_≡_ {A = QRootTwo}) _+_ _*_ -_ 0# 1#
isCommutativeRing-QRootTwo = isCommutativeRing-RootTwo isCommutativeRing-ℚ

commutativeRing-QRootTwo : CommutativeRing 0ℓ 0ℓ
commutativeRing-QRootTwo = record { isCommutativeRing = isCommutativeRing-QRootTwo }

-- ℤ[i] = 𝔾 (the Gaussian integers of GauInt.Base). This is the same
-- structure as GauInt.Properties.+-*-isCommutativeRing (both have the
-- same type, see Test.RingProperties).
isCommutativeRing-ZComplex : IsCommutativeRing (_≡_ {A = ZComplex}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZComplex = isCommutativeRing-Cplx isCommutativeRing-ℤ

commutativeRing-ZComplex : CommutativeRing 0ℓ 0ℓ
commutativeRing-ZComplex = record { isCommutativeRing = isCommutativeRing-ZComplex }

isCommutativeRing-QComplex : IsCommutativeRing (_≡_ {A = QComplex}) _+_ _*_ -_ 0# 1#
isCommutativeRing-QComplex = isCommutativeRing-Cplx isCommutativeRing-ℚ

commutativeRing-QComplex : CommutativeRing 0ℓ 0ℓ
commutativeRing-QComplex = record { isCommutativeRing = isCommutativeRing-QComplex }

isCommutativeRing-QRComplex : IsCommutativeRing (_≡_ {A = QRComplex}) _+_ _*_ -_ 0# 1#
isCommutativeRing-QRComplex = isCommutativeRing-Cplx isCommutativeRing-QRootTwo

commutativeRing-QRComplex : CommutativeRing 0ℓ 0ℓ
commutativeRing-QRComplex = record { isCommutativeRing = isCommutativeRing-QRComplex }

isCommutativeRing-ZOmega : IsCommutativeRing (_≡_ {A = ZOmega}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZOmega = isCommutativeRing-Omega isCommutativeRing-ℤ

commutativeRing-ZOmega : CommutativeRing 0ℓ 0ℓ
commutativeRing-ZOmega = record { isCommutativeRing = isCommutativeRing-ZOmega }

isCommutativeRing-QOmega : IsCommutativeRing (_≡_ {A = QOmega}) _+_ _*_ -_ 0# 1#
isCommutativeRing-QOmega = isCommutativeRing-Omega isCommutativeRing-ℚ

commutativeRing-QOmega : CommutativeRing 0ℓ 0ℓ
commutativeRing-QOmega = record { isCommutativeRing = isCommutativeRing-QOmega }

-- ----------------------------------------------------------------------
-- * Extensions of 𝔻 (given the specification of the smart constructor
-- dyadic).

module WithDyadicSpec (dyadic-spec : DyadicSpec) where

  isCommutativeRing-𝔻 : IsCommutativeRing (_≡_ {A = Dyadic}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-𝔻 = isCommutativeRing-Dyadic dyadic-spec

  commutativeRing-𝔻 : CommutativeRing 0ℓ 0ℓ
  commutativeRing-𝔻 = commutativeRing-Dyadic dyadic-spec

  isCommutativeRing-DRootTwo : IsCommutativeRing (_≡_ {A = DRootTwo}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-DRootTwo = isCommutativeRing-RootTwo isCommutativeRing-𝔻

  commutativeRing-DRootTwo : CommutativeRing 0ℓ 0ℓ
  commutativeRing-DRootTwo = record { isCommutativeRing = isCommutativeRing-DRootTwo }

  isCommutativeRing-DComplex : IsCommutativeRing (_≡_ {A = DComplex}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-DComplex = isCommutativeRing-Cplx isCommutativeRing-𝔻

  commutativeRing-DComplex : CommutativeRing 0ℓ 0ℓ
  commutativeRing-DComplex = record { isCommutativeRing = isCommutativeRing-DComplex }

  isCommutativeRing-DRComplex : IsCommutativeRing (_≡_ {A = DRComplex}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-DRComplex = isCommutativeRing-Cplx isCommutativeRing-DRootTwo

  commutativeRing-DRComplex : CommutativeRing 0ℓ 0ℓ
  commutativeRing-DRComplex = record { isCommutativeRing = isCommutativeRing-DRComplex }

  isCommutativeRing-DOmega : IsCommutativeRing (_≡_ {A = DOmega}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-DOmega = isCommutativeRing-Omega isCommutativeRing-𝔻

  commutativeRing-DOmega : CommutativeRing 0ℓ 0ℓ
  commutativeRing-DOmega = record { isCommutativeRing = isCommutativeRing-DOmega }

-- ----------------------------------------------------------------------
-- * The adjoint operations are involutive automorphisms
--
-- adj is the complex conjugation, adj2 the √2-conjugation. On ℤ, ℚ
-- and 𝔻 both are the identity.

adj-ℤ : IsInvolutiveRingEndo {ℤ} adj
adj-ℤ = id-isInvolutiveRingEndo

adj-ℚ : IsInvolutiveRingEndo {ℚ} adj
adj-ℚ = id-isInvolutiveRingEndo

adj-ZRootTwo : IsInvolutiveRingEndo {ZRootTwo} adj
adj-ZRootTwo = adj-RootTwo isCommutativeRing-ℤ adj-ℤ

adj2-ZRootTwo : IsInvolutiveRingEndo {ZRootTwo} adj2
adj2-ZRootTwo = adj2-RootTwo isCommutativeRing-ℤ adj-ℤ

adj-QRootTwo : IsInvolutiveRingEndo {QRootTwo} adj
adj-QRootTwo = adj-RootTwo isCommutativeRing-ℚ adj-ℚ

adj2-QRootTwo : IsInvolutiveRingEndo {QRootTwo} adj2
adj2-QRootTwo = adj2-RootTwo isCommutativeRing-ℚ adj-ℚ

adj-ZComplex : IsInvolutiveRingEndo {ZComplex} adj
adj-ZComplex = adj-Cplx isCommutativeRing-ℤ adj-ℤ

adj2-ZComplex : IsInvolutiveRingEndo {ZComplex} adj2
adj2-ZComplex = adj2-Cplx isCommutativeRing-ℤ adj-ℤ

adj-QComplex : IsInvolutiveRingEndo {QComplex} adj
adj-QComplex = adj-Cplx isCommutativeRing-ℚ adj-ℚ

adj2-QComplex : IsInvolutiveRingEndo {QComplex} adj2
adj2-QComplex = adj2-Cplx isCommutativeRing-ℚ adj-ℚ

adj-QRComplex : IsInvolutiveRingEndo {QRComplex} adj
adj-QRComplex = adj-Cplx (isCommutativeRing-RootTwo isCommutativeRing-ℚ) adj-QRootTwo

adj2-QRComplex : IsInvolutiveRingEndo {QRComplex} adj2
adj2-QRComplex = adj2-Cplx (isCommutativeRing-RootTwo isCommutativeRing-ℚ) adj2-QRootTwo

adj-ZOmega : IsInvolutiveRingEndo {ZOmega} adj
adj-ZOmega = adj-Omega isCommutativeRing-ℤ adj-ℤ

adj2-ZOmega : IsInvolutiveRingEndo {ZOmega} adj2
adj2-ZOmega = adj2-Omega isCommutativeRing-ℤ adj-ℤ

adj-QOmega : IsInvolutiveRingEndo {QOmega} adj
adj-QOmega = adj-Omega isCommutativeRing-ℚ adj-ℚ

adj2-QOmega : IsInvolutiveRingEndo {QOmega} adj2
adj2-QOmega = adj2-Omega isCommutativeRing-ℚ adj-ℚ

module WithDyadicSpec-Adjoint (dyadic-spec : DyadicSpec) where
  open WithDyadicSpec dyadic-spec

  adj-𝔻 : IsInvolutiveRingEndo {Dyadic} adj
  adj-𝔻 = id-isInvolutiveRingEndo

  adj-DRootTwo : IsInvolutiveRingEndo {DRootTwo} adj
  adj-DRootTwo = adj-RootTwo isCommutativeRing-𝔻 adj-𝔻

  adj2-DRootTwo : IsInvolutiveRingEndo {DRootTwo} adj2
  adj2-DRootTwo = adj2-RootTwo isCommutativeRing-𝔻 adj-𝔻

  adj-DComplex : IsInvolutiveRingEndo {DComplex} adj
  adj-DComplex = adj-Cplx isCommutativeRing-𝔻 adj-𝔻

  adj2-DComplex : IsInvolutiveRingEndo {DComplex} adj2
  adj2-DComplex = adj2-Cplx isCommutativeRing-𝔻 adj-𝔻

  adj-DRComplex : IsInvolutiveRingEndo {DRComplex} adj
  adj-DRComplex = adj-Cplx (isCommutativeRing-RootTwo isCommutativeRing-𝔻) adj-DRootTwo

  adj2-DRComplex : IsInvolutiveRingEndo {DRComplex} adj2
  adj2-DRComplex = adj2-Cplx (isCommutativeRing-RootTwo isCommutativeRing-𝔻) adj2-DRootTwo

  adj-DOmega : IsInvolutiveRingEndo {DOmega} adj
  adj-DOmega = adj-Omega isCommutativeRing-𝔻 adj-𝔻

  adj2-DOmega : IsInvolutiveRingEndo {DOmega} adj2
  adj2-DOmega = adj2-Omega isCommutativeRing-𝔻 adj-𝔻

-- ----------------------------------------------------------------------
-- * The norms of ℤ[√2] and ℤ[i] are multiplicative

private
  module ℤSolver = Data.Integer.Solver.+-*-Solver

norm-*-ZRootTwo : ∀ (x y : ZRootTwo) -> norm (x * y) ≡ norm x * norm y
norm-*-ZRootTwo (RootTwo a b) (RootTwo c d) = solve 4 (λ a b c d ->
    (a :* c :+ (b :* d :+ b :* d)) :* (a :* c :+ (b :* d :+ b :* d))
      :- con (+ 2) :* ((a :* d :+ c :* b) :* (a :* d :+ c :* b))
    := (a :* a :- con (+ 2) :* (b :* b)) :* (c :* c :- con (+ 2) :* (d :* d)))
  refl a b c d
  where open ℤSolver

norm-*-ZComplex : ∀ (x y : ZComplex) -> norm (x * y) ≡ norm x * norm y
norm-*-ZComplex (Cplx a b) (Cplx c d) = solve 4 (λ a b c d ->
    (a :* c :- b :* d) :* (a :* c :- b :* d) :+ (a :* d :+ b :* c) :* (a :* d :+ b :* c)
    := (a :* a :+ b :* b) :* (c :* c :+ d :* d))
  refl a b c d
  where open ℤSolver

-- ----------------------------------------------------------------------
-- * The results about 𝔻 and its extensions, instantiated with the proof
-- of the specification of dyadic.

open WithDyadicSpec dyadic-spec′ public
open WithDyadicSpec-Adjoint dyadic-spec′ public
