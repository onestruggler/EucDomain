-- A fast power of γ = 1+i that can be reasoned about.
--
-- Kopt.Patterns needs γˡ for the (n,l)-residues, with l as large as
-- the lde of the operator (152 in the authors' data set). The
-- framework's _^_ (Typeclasses.SemiRing) computes it by repeated
-- squaring, but its helper functions live in an inaccessible where
-- block, so nothing can be proved about it; the structural power
-- γ↑l = γ·(γ·(…·1)) of Kopt.Base can be reasoned about but performs l
-- multiplications in 𝔻[i], each of which normalises four dyadic
-- fractions.
--
-- This module computes γˡ in ℤ[i] instead, with ⌊l/2⌋ multiplications
-- by γ² = 2i, each of which is two integer additions and a negation:
--
--   γ⁰ = 1,  γ¹ = γ,  γ^(l+2) = 2i·γˡ,   2i·(a+bi) = -2b + 2ai.
--
-- It is equal to γ↑l (gz-↑ and γ-pow-↑ of Kopt.PatternFacts, which is
-- where the proof lives: this module deliberately does not depend on
-- Kopt.Properties.*, so that Kopt.Patterns does not either).

{-# OPTIONS --without-K --safe #-}

module Kopt.GammaPow where

open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)

open import Instances
open import Quantum.Synthesis.Ring
open import Kopt.Base

-- Multiplication by γ² = 2i in ℤ[i], by additions only.
twoi* : ZComplex -> ZComplex
twoi* (Cplx a b) = Cplx (Int.- (b Int.+ b)) (a Int.+ a)

-- γˡ in ℤ[i].
gz : ℕ -> ZComplex
gz zero = 1#
gz (suc zero) = γ
gz (suc (suc l)) = twoi* (gz l)

-- γˡ in 𝔻[i].
γ-pow : ℕ -> DComplex
γ-pow l = from-whole (gz l)
