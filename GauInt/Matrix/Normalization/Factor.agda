{-# OPTIONS --safe --without-K #-}

-- The executable normalizer exposes an exact gamma-power factorization:
-- a presentation is its normal form times γ to the number of cancellations.
module GauInt.Matrix.Normalization.Factor where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_+_; _*_)
open import GauInt.Algebra using (*-assoc)
open import GauInt.Gamma using (powγ; powγ-add; powγ-cancel)
open import GauInt.Matrix using (_≈_; scale)
open import GauInt.Matrix.Presentation using (ScaledMatrix; numerator; exponent; equivalent-refl)
open import GauInt.Matrix.Normalization using (normalize; value; equivalent)
open import GauInt.Matrix.Normalization.Minimal using (normalize-lower)
open import Data.Nat using (ℕ; _∸_; _≤_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

normal-exponent-bound : ∀ {d} (A : ScaledMatrix d) → exponent (value (normalize A)) ≤ exponent A
normal-exponent-bound A = normalize-lower A A (equivalent-refl A)

cancellations : ∀ {d} → ScaledMatrix d → ℕ
cancellations A = exponent A ∸ exponent (value (normalize A))

normal-exponent-split : ∀ {d} (A : ScaledMatrix d) → exponent (value (normalize A)) + cancellations A ≡ exponent A
normal-exponent-split A = NP.m+[n∸m]≡n (normal-exponent-bound A)

normal-factor : ∀ {d} (A : ScaledMatrix d) → numerator A ≈ scale (powγ (cancellations A)) (numerator (value (normalize A)))
normal-factor A i j = powγ-cancel (exponent N)
  (trans (sym (equivalent (normalize A) i j))
    (trans (cong (λ n → powγ n * numerator N i j) (sym (normal-exponent-split A)))
      (trans (cong (_* numerator N i j) (powγ-add (exponent N) (cancellations A)))
        (*-assoc (powγ (exponent N)) (powγ (cancellations A)) (numerator N i j)))))
  where N = value (normalize A)

cancel-arithmetic : ∀ k n m → n ≤ k + m → k + n ∸ m ≤ 2 * k
cancel-arithmetic k n m h = subst (k + n ∸ m ≤_)
  (trans (cong (_∸ m) (sym (NP.+-assoc k k m)))
    (trans (NP.m+n∸n≡m (k + k) m) (cong (k TC.+_) (sym (NP.+-identityʳ k)))))
  (NP.∸-monoˡ-≤ m (NP.+-monoʳ-≤ k h))
