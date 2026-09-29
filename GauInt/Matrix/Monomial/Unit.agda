{-# OPTIONS --safe --without-K #-}

-- An integral Gaussian unitary is a monomial matrix of Gaussian units.
module GauInt.Matrix.Monomial.Unit where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import Algebra.Bundles using (module CommutativeRing)
open CommutativeRing gaussianRing using () renaming (zeroʳ to *-zeroʳ)
open import GauInt.Matrix
open import GauInt.Matrix.Gram using (columnGram)
open import GauInt.Units using (unit-nonzero; conjugate-unit; conjugate-zero)
open import GauInt.Matrix.UnitSupport using (Support; unit-row; row-norm)
open import GauInt.Matrix.Monomial using (GaussianMonomial; permutation; phase; phase-unit; monomialMatrix; actRight)
open import Data.Fin using (Fin; _≟_)
import Data.Fin.Permutation as P
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

supports-monomial : ∀ {n} (M : Mat n) → (∀ i → Support (M i)) → (∀ j → Support (λ i → M i j)) →
  Σ[ C ∈ GaussianMonomial n ] M ≈ monomialMatrix C
supports-monomial M rows cols = C , represents
  where
  f = λ i → proj₁ (rows i)
  g = λ j → proj₁ (cols j)
  left : ∀ i → g (f i) ≡ i
  left i with g (f i) ≟ i
  ... | yes h = h
  ... | no h = ⊥-elim (unit-nonzero (M i (f i)) (proj₁ (proj₂ (rows i)))
    (proj₂ (proj₂ (cols (f i))) i (λ he → h (sym he))))
  right : ∀ j → f (g j) ≡ j
  right j with f (g j) ≟ j
  ... | yes h = h
  ... | no h = ⊥-elim (unit-nonzero (M (g j) j) (proj₁ (proj₂ (cols j)))
    (proj₂ (proj₂ (rows (g j))) j (λ he → h (sym he))))
  C : GaussianMonomial _
  C = record { permutation = P.permutation f g right left
             ; phase = λ i → M i (f i); phase-unit = λ i → proj₁ (proj₂ (rows i)) }
  represents : M ≈ monomialMatrix C
  represents i j with j ≟ f i
  ... | yes refl = trans (sym (*-identityʳ (M i (f i))))
    (cong (M i (f i) *_) (sym (delta-self (f i))))
  ... | no h = trans (proj₂ (proj₂ (rows i)) j h)
    (sym (trans (cong (M i (f i) *_) (delta-other (f i) j (λ he → h (sym he)))) (*-zeroʳ (M i (f i)))))

unitary-monomial : ∀ {n} (M : Mat n) → gram M ≈ identity → columnGram M ≈ identity →
  Σ[ C ∈ GaussianMonomial n ] M ≈ monomialMatrix C
unitary-monomial M hr hc = supports-monomial M
  (λ i → unit-row (M i) (row-norm M i (trans (hr i i) (delta-self i)))) columns
  where
  columns : ∀ j → Support (λ i → M i j)
  columns j = finish (unit-row (adjoint M j) (row-norm (adjoint M) j (trans (hc j j) (delta-self j))))
    where
    finish : Support (adjoint M j) → Support (λ i → M i j)
    finish (i , hu , hz) = i , conjugate-unit (M i j) hu , λ k hk → conjugate-zero (M k j) (hz k hk)

rightMonomial : ∀ {n} → GaussianMonomial n → GaussianMonomial n
rightMonomial C = record
  { permutation = P.flip (permutation C)
  ; phase = λ j → phase C (permutation C P.⟨$⟩ˡ j)
  ; phase-unit = λ j → phase-unit C (permutation C P.⟨$⟩ˡ j) }

right-representation : ∀ {n} (C : GaussianMonomial n) → monomialMatrix C ≈ actRight (rightMonomial C) identity
right-representation C i j with i ≟ (permutation C P.⟨$⟩ˡ j)
... | yes refl = cong (phase C (permutation C P.⟨$⟩ˡ j) *_)
  (trans (cong (λ k → delta k j) (P.inverseʳ (permutation C)))
    (trans (delta-self j) (sym (delta-self (permutation C P.⟨$⟩ˡ j)))))
... | no neq = trans (cong (phase C i *_) (delta-other (permutation C P.⟨$⟩ʳ i) j different))
  (trans (*-zeroʳ (phase C i)) (sym (trans
    (cong (phase C (permutation C P.⟨$⟩ˡ j) *_) (delta-other i (permutation C P.⟨$⟩ˡ j) neq))
    (*-zeroʳ (phase C (permutation C P.⟨$⟩ˡ j))))))
  where
  different : (permutation C P.⟨$⟩ʳ i) ≢ j
  different eq = neq (trans (sym (P.inverseˡ (permutation C))) (cong (permutation C P.⟨$⟩ˡ_) eq))

unitary-right-monomial : ∀ {n} (M : Mat n) → gram M ≈ identity → columnGram M ≈ identity →
  Σ[ C ∈ GaussianMonomial n ] M ≈ actRight C identity
unitary-right-monomial M hr hc = finish (unitary-monomial M hr hc)
  where
  finish : (Σ[ C ∈ GaussianMonomial _ ] M ≈ monomialMatrix C) → Σ[ C ∈ GaussianMonomial _ ] M ≈ actRight C identity
  finish (C , h) = rightMonomial C , λ i j → trans (h i j) (right-representation C i j)
