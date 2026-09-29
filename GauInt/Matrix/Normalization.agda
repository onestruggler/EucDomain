{-# OPTIONS --safe --without-K #-}

-- Exact cancellation with a proof of denominator-aware preservation.
module GauInt.Matrix.Normalization where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; _/_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (γ; powγ)
open import GauInt.Gamma.Division using (divideGamma)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.Matrix.Presentation using (ScaledMatrix; scaled; numerator; exponent; Equivalent; equivalent-refl; equivalent-trans)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (+_)
import Data.Integer as Z
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

divideMatrix : ∀ {n} → Mat n → Mat n
divideMatrix M i j = divideGamma (M i j)

division-equivalent : ∀ {n} (M : Mat n) k → scale γ (divideMatrix M) ≈ M →
  Equivalent (scaled (divideMatrix M) k) (scaled M (suc k))
division-equivalent M k h i j = trans (*-assoc (powγ k) γ (divideMatrix M i j))
  (cong (powγ k *_) (h i j))

record NormalizedResult {n} (A : ScaledMatrix n) : Set where
  constructor normalized
  field
    value : ScaledMatrix n
    equivalent : Equivalent value A
open NormalizedResult public

normalizeAt : ∀ {n} k (M : Mat n) → NormalizedResult (scaled M k)
normalizeAt zero M = normalized (scaled M zero) (equivalent-refl (scaled M zero))
normalizeAt (suc k) M with matrixEq (scale γ (divideMatrix M)) M
... | no _ = normalized (scaled M (suc k)) (equivalent-refl (scaled M (suc k)))
... | yes h with normalizeAt k (divideMatrix M)
...   | normalized B he = normalized B (equivalent-trans {A = B} {B = scaled (divideMatrix M) k}
  {C = scaled M (suc k)} he (division-equivalent M k h))

normalize : ∀ {n} (A : ScaledMatrix n) → NormalizedResult A
normalize A = normalizeAt (exponent A) (numerator A)
