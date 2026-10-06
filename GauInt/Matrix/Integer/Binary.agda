{-# OPTIONS --safe --without-K #-}

-- The binary residue of an integer matrix: parity bits, row weights and overlaps.
module GauInt.Matrix.Integer.Binary where

open import GauInt.Matrix.Integer using (IntMat)
open import GauInt.Matrix.Integer.Residues using (rowWeight; rowOverlap)
open import Integer.Parity using (parity; parityBit; parity-cases)
open import Finite.BinaryMatrix using (Binary; bitNat; bit-and)
open import Natural.Sum using (sumNat; sum-cong)
open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin)
open import Data.Bool using (_∧_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong₂)

parityBit-value : ∀ x → bitNat (parityBit x) ≡ parity x
parityBit-value x with parity-cases x
... | inj₁ h rewrite h = refl
... | inj₂ h rewrite h = refl

binary : ∀ {n} → IntMat n → Binary n
binary M i j = parityBit (M i j)

-- Row weights and overlaps of Boolean matrices, in the conjunction form
-- used by the executable binary checks.
weight : ∀ {n} → Binary n → Fin n → ℕ
weight R i = sumNat (λ j → bitNat (R i j))

overlapCount : ∀ {n} → Binary n → Fin n → Fin n → ℕ
overlapCount R i j = sumNat (λ k → bitNat (R i k ∧ R j k))

weight-correct : ∀ {n} (M : IntMat n) i → weight (binary M) i ≡ rowWeight M i
weight-correct M i = sum-cong (λ j → parityBit-value (M i j))

overlapCount-correct : ∀ {n} (M : IntMat n) i j → overlapCount (binary M) i j ≡ rowOverlap M i j
overlapCount-correct M i j = sum-cong (λ k → trans (bit-and (parityBit (M i k)) (parityBit (M j k)))
  (cong₂ _*_ (parityBit-value (M i k)) (parityBit-value (M j k))))
