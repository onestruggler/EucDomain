{-# OPTIONS --safe --without-K #-}

-- Completeness of gamma cancellation, and minimality of the actual
-- executable normalizer. No primitive-numerator premise is supplied by users.
module GauInt.Matrix.Normalization.Minimal where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (γ; powγ; powγ-cancel)
open import GauInt.Matrix
open import GauInt.Matrix.Presentation
open import GauInt.Matrix.Normalization
open import GauInt.Matrix.Denominator
open import GauInt.Gamma.Division
open import Finite.Check
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤-antisym)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

counterexample : ∀ n (P : Fin n → Set) → (∀ i → Dec (P i)) →
  ¬ (∀ i → P i) → Σ[ i ∈ Fin n ] ¬ P i
counterexample zero P decide notAll = ⊥-elim (notAll (λ ()))
counterexample (suc n) P decide notAll with decide zero
... | no notFirst = zero , notFirst
... | yes first with counterexample n (λ i → P (suc i)) (λ i → decide (suc i))
  (λ tail → notAll (λ { zero → first ; (suc i) → tail i }))
...   | i , notPi = suc i , notPi

failed-cancellation-primitive : ∀ {n} (M : Mat n) →
  ¬ (scale γ (divideMatrix M) ≈ M) → Primitive M
failed-cancellation-primitive {n} M notAll with
  counterexample n (λ i → ∀ j → γ * divideGamma (M i j) ≡ M i j)
    (λ i → decAll n _ (λ j → (γ * divideGamma (M i j)) TC.≟ M i j)) notAll
... | i , notRow with counterexample n (λ j → γ * divideGamma (M i j) ≡ M i j)
  (λ j → (γ * divideGamma (M i j)) TC.≟ M i j) notRow
...   | j , notEntry = i , j , (λ even → notEntry (divide-complete (M i j) even))

normalizeAt-minimal : ∀ {n} k (M : Mat n) →
  0 < exponent (value (normalizeAt k M)) → Primitive (numerator (value (normalizeAt k M)))
normalizeAt-minimal zero M ()
normalizeAt-minimal (suc k) M with matrixEq (scale γ (divideMatrix M)) M
... | no notAll = λ _ → failed-cancellation-primitive M notAll
... | yes h = normalizeAt-minimal k (divideMatrix M)

normalize-minimal : ∀ {n} (A : ScaledMatrix n) →
  0 < exponent (value (normalize A)) → Primitive (numerator (value (normalize A)))
normalize-minimal A = normalizeAt-minimal (exponent A) (numerator A)

normalizeCertified : ∀ {n} → ScaledMatrix n → NormalizedMatrix n
normalizeCertified A = normalizedMatrix (value (normalize A)) (normalize-minimal A)

normalize-lower : ∀ {n} (A B : ScaledMatrix n) → Equivalent A B →
  exponent (value (normalize A)) ≤ exponent B
normalize-lower A B h = exponent-lower (normalizeCertified A) B
  (equivalent-trans {A = value (normalize A)} {B = A} {C = B}
    (equivalent (normalize A)) h)

normalize-exponent-congruent : ∀ {n} (A B : ScaledMatrix n) → Equivalent A B →
  exponent (value (normalize A)) ≡ exponent (value (normalize B))
normalize-exponent-congruent A B h = ≤-antisym
  (normalize-lower A (value (normalize B))
    (equivalent-trans {A = A} {B = B} {C = value (normalize B)} h
      (equivalent-sym {A = value (normalize B)} {B = B} (equivalent (normalize B)))))
  (normalize-lower B (value (normalize A))
    (equivalent-trans {A = B} {B = A} {C = value (normalize A)}
      (equivalent-sym {A = A} {B = B} h)
      (equivalent-sym {A = value (normalize A)} {B = A} (equivalent (normalize A)))))

normalized-exponent-unique : ∀ {n} (A B : NormalizedMatrix n) → Equivalent (representation A) (representation B) →
  exponent (representation A) ≡ exponent (representation B)
normalized-exponent-unique A B h = ≤-antisym (exponent-lower A (representation B) h)
  (exponent-lower B (representation A) (equivalent-sym {A = representation A} {B = representation B} h))

normalized-numerator-unique : ∀ {n} (A B : NormalizedMatrix n) → Equivalent (representation A) (representation B) →
  numerator (representation A) ≈ numerator (representation B)
normalized-numerator-unique A B h i j = powγ-cancel (exponent (representation B))
  (trans (h i j) (cong (λ k → powγ k * numerator (representation B) i j) (normalized-exponent-unique A B h)))
