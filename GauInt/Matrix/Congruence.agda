{-# OPTIONS --safe --without-K #-}

-- Lift gamma congruences to arbitrary finite matrices and exact division.
-- The γ-weight of a matrix counts its γ-odd entries; the entrywise
-- γ³ residue encoding is complete.
module GauInt.Matrix.Congruence where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_*_; 0#)
open import GauInt.Algebra using (Unit)
open import GauInt.Matrix
open import GauInt.Gamma using (Evenγ) renaming (gaussianParity to parity)
open import GauInt.Gamma.Residue using (Code; encode; decode; encode-spec)
open import GauInt.Matrix.Normalization using (divideMatrix)
open import Natural.Sum using (sumNat)
import GauInt.Gamma.Congruence as G
import GauInt.Parity as GP
import Natural.Sum as NS
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
import Data.Nat.Properties as NP
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; subst)

-- The number of γ-odd entries.
weight : ∀ {n} → Mat n → ℕ
weight M = sumNat (λ i → sumNat (λ j → parity (M i j)))

weight-cong : ∀ {n} {M N : Mat n} → M ≈ N → weight M ≡ weight N
weight-cong h = NS.sum-cong (λ i → NS.sum-cong (λ j → cong parity (h i j)))

weight-reindex : ∀ {n} (M : Mat n) (p q : P.Permutation′ n) →
  weight (λ i j → M (p P.⟨$⟩ʳ i) (q P.⟨$⟩ʳ j)) ≡ weight M
weight-reindex M p q = trans (NS.sum-cong (λ i → NS.sum-reindex q (λ j → parity (M (p P.⟨$⟩ʳ i) j))))
  (NS.sum-reindex p (λ i → sumNat (λ j → parity (M i j))))

weight-row-units : ∀ {n} (M : Mat n) (u : Fin n → ZComplex) → (∀ i → Unit (u i)) →
  weight (λ i j → u i * M i j) ≡ weight M
weight-row-units M u hu = NS.sum-cong (λ i → NS.sum-cong (λ j → GP.unit-parity (u i) (M i j) (hu i)))

Matrices : ∀ {d} → ℕ → Mat d → Mat d → Set
Matrices n M N = ∀ i j → G.Cong n (M i j) (N i j)

of-equality : ∀ {d} n (M N : Mat d) → M ≈ N → Matrices n M N
of-equality n M N h i j = subst (G.Cong n (M i j)) (h i j) (G.cong-refl n (M i j))

matrix-refl : ∀ {d} n (M : Mat d) → Matrices n M M
matrix-refl n M i j = G.cong-refl n (M i j)

matrix-sym : ∀ {d} n (M N : Mat d) → Matrices n M N → Matrices n N M
matrix-sym n M N h i j = G.cong-sym n (M i j) (N i j) (h i j)

matrix-trans : ∀ {d} n (M N P : Mat d) → Matrices n M N → Matrices n N P → Matrices n M P
matrix-trans n M N P h k i j = G.cong-trans n (M i j) (N i j) (P i j) (h i j) (k i j)

sum-congruent : ∀ {d} n (f g : Fin d → ZComplex) → (∀ i → G.Cong n (f i) (g i)) → G.Cong n (sum f) (sum g)
sum-congruent {zero} n f g h = G.cong-refl n 0#
sum-congruent {suc d} n f g h = G.cong-add n (f zero) (g zero) (sum (λ i → f (suc i))) (sum (λ i → g (suc i)))
  (h zero) (sum-congruent n (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

mul-congruent : ∀ {d} n (A B C D : Mat d) → Matrices n A B → Matrices n C D → Matrices n (mul A C) (mul B D)
mul-congruent n A B C D h k i j = sum-congruent n (λ t → A i t * C t j) (λ t → B i t * D t j)
  (λ t → G.cong-mul n (A i t) (B i t) (C t j) (D t j) (h i t) (k t j))

scale-congruent : ∀ {d} n z (M N : Mat d) → Matrices n M N → Matrices n (scale z M) (scale z N)
scale-congruent n z M N h i j = G.cong-mul n z z (M i j) (N i j) (G.cong-refl n z) (h i j)

adjoint-congruent : ∀ {d} n (M N : Mat d) → Matrices n M N → Matrices n (adjoint M) (adjoint N)
adjoint-congruent n M N h i j = G.cong-conj n (M j i) (N j i) (h j i)

gram-congruent : ∀ {d} n (M N : Mat d) → Matrices n M N → Matrices n (gram M) (gram N)
gram-congruent n M N h = mul-congruent n M N (adjoint M) (adjoint N) h (adjoint-congruent n M N h)

weight-congruent : ∀ {d} n (M N : Mat d) → Matrices (suc n) M N → weight M ≡ weight N
weight-congruent n M N h = NS.sum-cong (λ i → NS.sum-cong (λ j → G.parity-congruent n (M i j) (N i j) (h i j)))

zero-weight-even : ∀ {d} (M : Mat d) → weight M ≡ 0 → ∀ i j → Evenγ (M i j)
zero-weight-even M h i j = GP.zero-parity-even (M i j) (NP.≤-antisym
  (subst (parity (M i j) ≤_) h (NP.≤-trans (NS.sum-component (λ j → parity (M i j)) j)
    (NS.sum-component (λ i → sumNat (λ j → parity (M i j))) i))) z≤n)

even-zero-weight : ∀ {d} (M : Mat d) → (∀ i j → Evenγ (M i j)) → weight M ≡ 0
even-zero-weight {d} M h = trans (NS.sum-cong (λ i → trans (NS.sum-cong (λ j → GP.even-parity-zero (M i j) (h i j))) (NS.sum-zero d)))
  (NS.sum-zero d)

divide-congruent : ∀ {d} n (M N : Mat d) → Matrices (suc n) M N → (∀ i j → Evenγ (M i j)) →
  (∀ i j → Evenγ (N i j)) → Matrices n (divideMatrix M) (divideMatrix N)
divide-congruent n M N h hm hn i j = G.divide-congruent n (M i j) (N i j) (hm i j) (hn i j) (h i j)

-- Entrywise gamma-cubed residue encoding for square matrices.
matrixCode : ∀ {d} → Mat d → Fin d → Fin d → Code
matrixCode M i j = encode (M i j)

matrix-spec : ∀ {d} (M : Mat d) → Matrices 3 M (λ i j → decode (matrixCode M i j))
matrix-spec M i j = encode-spec (M i j)
