-- Polynomial expressions of the integer coefficient ring solver
-- (Quantum.Synthesis.Ring.Properties.Common.ZSolver) over a
-- commutative ring A form a Ring in the sense of the typeclasses.
--
-- This is the trick used for proving the ring laws of the extensions
-- A [√2], A [i], A [ω]: instead of writing down the solver
-- expressions by hand, we compute them with the ring operations of
-- (Polynomial n) [√2] etc., i.e. by the very same definitions. The
-- semantics ⟦_⟧ of the solver maps these expressions definitionally
-- to the corresponding expressions in A.

{-# OPTIONS --without-K --safe #-}

open import Instances
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Quantum.Synthesis.Ring.Properties.Poly
  {A : Set} {{RA : Ring A}} (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (+_)
open import Quantum.Synthesis.Ring.Properties.Common using (module ZSolver)

-- The commutative ring A as a stdlib bundle.
commutativeRing : CommutativeRing 0ℓ 0ℓ
commutativeRing = record { isCommutativeRing = isCR }

open ZSolver commutativeRing public
  using (Polynomial ; var ; con ; _:+_ ; _:*_ ; :-_ ; _:-_ ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; solve ; _:=_ ; ⟦_⟧ℤ)

instance
  SemiRingPoly : {n : ℕ} -> SemiRing (Polynomial n)
  SemiRingPoly ._+_ = _:+_
  SemiRingPoly ._*_ = _:*_
  SemiRingPoly .0# = con (+ 0)
  SemiRingPoly .1# = con (+ 1)
  SemiRingPoly .fromℕ k = con (+ k)

  RingPoly : {n : ℕ} -> Ring (Polynomial n)
  RingPoly .sra = SemiRingPoly
  RingPoly .-_ = :-_
