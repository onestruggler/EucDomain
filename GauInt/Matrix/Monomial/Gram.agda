{-# OPTIONS --safe --without-K #-}

-- Both Gram equations are preserved by arbitrary unit monomial actions.
module GauInt.Matrix.Monomial.Gram where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import Algebra.Bundles using (module CommutativeRing)
open CommutativeRing gaussianRing using () renaming (zeroˡ to *-zeroˡ; zeroʳ to *-zeroʳ)
open import GauInt.Matrix
open import GauInt.Matrix.Gram using (gram-cong; columnGram)
open import GauInt.Matrix.Monomial using (GaussianMonomial; permutation; phase; phase-unit; act; actRight)
import Data.Fin.Permutation as P
open import Data.Fin using (Fin; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open GaussianSolver

delta-permutation : ∀ {n} (p : P.Permutation′ n) i j → delta (p P.⟨$⟩ʳ i) j ≡ delta (p P.⟨$⟩ˡ j) i
delta-permutation p i j with (p P.⟨$⟩ʳ i) ≟ j
... | yes eq = trans (cong (λ k → delta k j) eq) (trans (delta-self j)
  (sym (trans (cong (λ k → delta k i) (trans (cong (p P.⟨$⟩ˡ_) (sym eq)) (P.inverseˡ p))) (delta-self i))))
... | no neq = trans (delta-other (p P.⟨$⟩ʳ i) j neq)
  (sym (delta-other (p P.⟨$⟩ˡ j) i (λ eq → neq (trans (cong (p P.⟨$⟩ʳ_) (sym eq)) (P.inverseʳ p)))))

sum-reindex : ∀ {n} (p : P.Permutation′ n) (f : Fin n → ZComplex) → sum (λ i → f (p P.⟨$⟩ʳ i)) ≡ sum f
sum-reindex p f = trans (sum-cong (λ i → sym (sum-delta (p P.⟨$⟩ʳ i) f)))
  (trans (sum-swap (λ i j → delta (p P.⟨$⟩ʳ i) j * f j))
    (sum-cong (λ j → trans (sum-cong (λ i → cong (_* f j) (delta-permutation p i j)))
      (sum-delta (p P.⟨$⟩ˡ j) (λ _ → f j)))))

phase-product : ∀ (u v x y : ZComplex) → (u * x) * TC.adj (v * y) ≡ (u * TC.adj v) * (x * TC.adj y)
phase-product u v x y = trans (cong ((u * x) *_) (conj-mul v y))
  (solve 4 (λ u x v y → (u :* x) :* (v :* y) := (u :* v) :* (x :* y)) refl u x (TC.adj v) (TC.adj y))

gram-left : ∀ {n} C (M : Mat n) i j → gram (act C M) i j ≡
  (phase C i * TC.adj (phase C j)) * gram M (permutation C P.⟨$⟩ʳ i) (permutation C P.⟨$⟩ʳ j)
gram-left C M i j = trans
  (sum-cong (λ k → phase-product (phase C i) (phase C j) (M (permutation C P.⟨$⟩ʳ i) k) (M (permutation C P.⟨$⟩ʳ j) k)))
  (sum-mulˡ (phase C i * TC.adj (phase C j)) (λ k → M (permutation C P.⟨$⟩ʳ i) k * TC.adj (M (permutation C P.⟨$⟩ʳ j) k)))

gram-right : ∀ {n} C (M : Mat n) → gram (actRight C M) ≈ gram M
gram-right C M i j = trans
  (sum-cong (λ k → trans (phase-product (phase C k) (phase C k) (M i (permutation C P.⟨$⟩ʳ k)) (M j (permutation C P.⟨$⟩ʳ k)))
    (trans (cong (_* (M i (permutation C P.⟨$⟩ʳ k) * TC.adj (M j (permutation C P.⟨$⟩ʳ k)))) (phase-unit C k))
      (*-identityˡ (M i (permutation C P.⟨$⟩ʳ k) * TC.adj (M j (permutation C P.⟨$⟩ʳ k)))))))
  (sum-reindex (permutation C) (λ k → M i k * TC.adj (M j k)))

monomial-delta : ∀ {n} (C : GaussianMonomial n) z i j →
  (phase C i * TC.adj (phase C j)) * (z * delta (permutation C P.⟨$⟩ʳ i) (permutation C P.⟨$⟩ʳ j)) ≡ z * delta i j
monomial-delta C z i j with i ≟ j
... | yes refl = trans (cong (λ d → (phase C i * TC.adj (phase C i)) * (z * d)) (delta-self (permutation C P.⟨$⟩ʳ i)))
  (trans (cong (_* (z * 1#)) (phase-unit C i))
    (trans (*-identityˡ (z * 1#)) (cong (z *_) (sym (delta-self i)))))
... | no neq = trans (cong (λ d → (phase C i * TC.adj (phase C j)) * (z * d))
    (delta-other (permutation C P.⟨$⟩ʳ i) (permutation C P.⟨$⟩ʳ j) distinct))
  (trans (cong ((phase C i * TC.adj (phase C j)) *_) (*-zeroʳ z))
    (trans (*-zeroʳ (phase C i * TC.adj (phase C j)))
      (sym (trans (cong (z *_) (delta-other i j neq)) (*-zeroʳ z)))))
  where
  distinct : (permutation C P.⟨$⟩ʳ i) ≢ (permutation C P.⟨$⟩ʳ j)
  distinct eq = neq (trans (sym (P.inverseˡ (permutation C)))
    (trans (cong (permutation C P.⟨$⟩ˡ_) eq) (P.inverseˡ (permutation C))))

gram-left-unitary : ∀ {n} C (M : Mat n) z → gram M ≈ scale z identity → gram (act C M) ≈ scale z identity
gram-left-unitary C M z hu i j = trans (gram-left C M i j)
  (trans (cong ((phase C i * TC.adj (phase C j)) *_)
    (hu (permutation C P.⟨$⟩ʳ i) (permutation C P.⟨$⟩ʳ j))) (monomial-delta C z i j))

gram-right-unitary : ∀ {n} C (M : Mat n) z → gram M ≈ scale z identity → gram (actRight C M) ≈ scale z identity
gram-right-unitary C M z hu i j = trans (gram-right C M i j) (hu i j)

conjugateMonomial : ∀ {n} → GaussianMonomial n → GaussianMonomial n
conjugateMonomial C = record
  { permutation = permutation C; phase = λ i → TC.adj (phase C i)
  ; phase-unit = λ i → trans (cong (TC.adj (phase C i) *_) (conj-involutive (phase C i)))
      (trans (*-comm (TC.adj (phase C i)) (phase C i)) (phase-unit C i)) }

adjoint-left : ∀ {n} C (M : Mat n) → adjoint (act C M) ≈ actRight (conjugateMonomial C) (adjoint M)
adjoint-left C M i j = conj-mul (phase C j) (M (permutation C P.⟨$⟩ʳ j) i)

adjoint-right : ∀ {n} C (M : Mat n) → adjoint (actRight C M) ≈ act (conjugateMonomial C) (adjoint M)
adjoint-right C M i j = conj-mul (phase C i) (M j (permutation C P.⟨$⟩ʳ i))

columnGram-left : ∀ {n} C (M : Mat n) → columnGram (act C M) ≈ columnGram M
columnGram-left C M i j = trans
  (gram-cong {M = adjoint (act C M)} {N = actRight (conjugateMonomial C) (adjoint M)} (adjoint-left C M) i j)
  (gram-right (conjugateMonomial C) (adjoint M) i j)

columnGram-right-unitary : ∀ {n} C (M : Mat n) z → columnGram M ≈ scale z identity → columnGram (actRight C M) ≈ scale z identity
columnGram-right-unitary C M z hu i j = trans
  (gram-cong {M = adjoint (actRight C M)} {N = act (conjugateMonomial C) (adjoint M)} (adjoint-right C M) i j)
  (gram-left-unitary (conjugateMonomial C) (adjoint M) z hu i j)
