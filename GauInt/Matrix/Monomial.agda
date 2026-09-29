{-# OPTIONS --safe --without-K #-}

-- Monomial matrices over ℤ[i]: a permutation together with unit phases.
-- They act on rows (act) and on columns (actRight); both actions preserve
-- the γ-weight, exact γ-division and γ-presentations.
module GauInt.Matrix.Monomial where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_*_)
open import GauInt.Gamma using (γ; powγ; Evenγ; even-unscale) renaming (gaussianParity to parity)
open import GauInt.Gamma.Division using (divide-complete; divide-multiple; divideGamma)
open import GauInt.Algebra
open import GauInt.Algebra.Swap using (swap)
open import GauInt.Parity using (unit-parity)
open import GauInt.Matrix
open import GauInt.Matrix.Presentation using (ScaledMatrix; scaled; numerator; exponent; Equivalent; scaledMul)
open import GauInt.Matrix.Normalization using (divideMatrix)
open import GauInt.Matrix.Denominator using (Primitive; NormalizedMatrix; normalizedMatrix; representation; minimal)
open import GauInt.Matrix.Congruence using (weight; weight-row-units; zero-weight-even)
import Natural.Sum as NS
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin.Permutation as P
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

record GaussianMonomial (n : ℕ) : Set where
  field
    permutation : P.Permutation′ n
    phase : Fin n → ZComplex
    phase-unit : ∀ i → Unit (phase i)
open GaussianMonomial public

act : ∀ {n} → GaussianMonomial n → Mat n → Mat n
act C M i j = phase C i * M (permutation C P.⟨$⟩ʳ i) j

actRight : ∀ {n} → GaussianMonomial n → Mat n → Mat n
actRight C M i j = phase C j * M i (permutation C P.⟨$⟩ʳ j)

actScaled : ∀ {n} → GaussianMonomial n → ScaledMatrix n → ScaledMatrix n
actScaled C A = scaled (act C (numerator A)) (exponent A)

act-equivalent : ∀ {n} C (A B : ScaledMatrix n) → Equivalent A B → Equivalent (actScaled C A) (actScaled C B)
act-equivalent C A B h i j = trans (swap (powγ (exponent B)) (phase C i) (numerator A (permutation C P.⟨$⟩ʳ i) j))
  (trans (cong (phase C i *_) (h (permutation C P.⟨$⟩ʳ i) j))
    (swap (phase C i) (powγ (exponent A)) (numerator B (permutation C P.⟨$⟩ʳ i) j)))

act-primitive : ∀ {n} C (M : Mat n) → Primitive M → Primitive (act C M)
act-primitive C M (i , j , hOdd) = k , j , λ he → hOdd
  (subst (λ l → Evenγ (M l j)) (P.inverseʳ (permutation C))
    (even-unscale (phase C k) (M (permutation C P.⟨$⟩ʳ k) j) (phase-unit C k) he))
  where k = permutation C P.⟨$⟩ˡ i

act-normalized : ∀ {n} → GaussianMonomial n → NormalizedMatrix n → NormalizedMatrix n
act-normalized C A = normalizedMatrix (actScaled C (representation A))
  (λ h → act-primitive C (numerator (representation A)) (minimal A h))

matrix-acts : ∀ {n} C (G M : Mat n) → (∀ i j → G i j ≡ phase C i * delta (permutation C P.⟨$⟩ʳ i) j) → mul G M ≈ act C M
matrix-acts C G M h i j = trans (sum-cong (λ k → cong (_* M k j) (h i k)))
  (trans (sum-cong (λ k → *-assoc (phase C i) (delta (permutation C P.⟨$⟩ʳ i) k) (M k j)))
    (trans (sum-mulˡ (phase C i) (λ k → delta (permutation C P.⟨$⟩ʳ i) k * M k j))
      (cong (phase C i *_) (sum-delta (permutation C P.⟨$⟩ʳ i) (λ k → M k j)))))

act-mul : ∀ {n} C (M N : Mat n) → act C (mul M N) ≈ mul (act C M) N
act-mul C M N i j = trans (sym (sum-mulˡ (phase C i) (λ k → M (permutation C P.⟨$⟩ʳ i) k * N k j)))
  (sum-cong (λ k → sym (*-assoc (phase C i) (M (permutation C P.⟨$⟩ʳ i) k) (N k j))))

actScaled-mul : ∀ {n} C (A B : ScaledMatrix n) → Equivalent (actScaled C (scaledMul A B)) (scaledMul (actScaled C A) B)
actScaled-mul C A B = scale-cong (powγ (exponent (scaledMul A B))) (act-mul C (numerator A) (numerator B))

act-cong : ∀ {n} C (M N : Mat n) → M ≈ N → act C M ≈ act C N
act-cong C M N h i j = cong (phase C i *_) (h (permutation C P.⟨$⟩ʳ i) j)

mul-actRight : ∀ {n} C (L M : Mat n) → mul L (actRight C M) ≈ actRight C (mul L M)
mul-actRight C L M i j = trans
  (sum-cong (λ k → trans (sym (*-assoc (L i k) (phase C j) (M k (permutation C P.⟨$⟩ʳ j))))
    (trans (cong (_* M k (permutation C P.⟨$⟩ʳ j)) (*-comm (L i k) (phase C j)))
      (*-assoc (phase C j) (L i k) (M k (permutation C P.⟨$⟩ʳ j))))))
  (sum-mulˡ (phase C j) (λ k → L i k * M k (permutation C P.⟨$⟩ʳ j)))

monomialMatrix : ∀ {n} → GaussianMonomial n → Mat n
monomialMatrix C = act C identity

monomial-mul : ∀ {n} C (M : Mat n) → mul (monomialMatrix C) M ≈ act C M
monomial-mul C M i j = trans (sym (act-mul C identity M i j))
  (act-cong C (mul identity M) M (identity-mul M) i j)

intertwine-mul : ∀ {n} C D (L M : Mat n) → mul L (monomialMatrix C) ≈ act D L →
  mul L (act C M) ≈ act D (mul L M)
intertwine-mul C D L M he i j = trans
  (mul-cong {A = L} {B = L} {C = act C M} {D = mul (monomialMatrix C) M}
    ≈-refl (λ a b → sym (monomial-mul C M a b)) i j)
  (trans (sym (mul-assoc L (monomialMatrix C) M i j))
    (trans (mul-cong {A = mul L (monomialMatrix C)} {B = act D L} {C = M} {D = M} he ≈-refl i j)
      (sym (act-mul D L M i j))))

-- The γ-weight is invariant under both actions.
weight-monomial : ∀ {n} (M : Mat n) (p : P.Permutation′ n) (u : Fin n → ZComplex) → (∀ i → Unit (u i)) →
  weight (λ i j → u i * M (p P.⟨$⟩ʳ i) j) ≡ weight M
weight-monomial M p u hu = trans (weight-row-units (λ i j → M (p P.⟨$⟩ʳ i) j) u hu)
  (NS.sum-reindex p (λ i → NS.sumNat (λ j → parity (M i j))))

weight-left : ∀ {n} C (M : Mat n) → weight (act C M) ≡ weight M
weight-left C M = weight-monomial M (permutation C) (phase C) (phase-unit C)

weight-right : ∀ {n} C (M : Mat n) → weight (actRight C M) ≡ weight M
weight-right C M = NS.sum-cong (λ i → trans
  (NS.sum-cong (λ j → unit-parity (phase C j) (M i (permutation C P.⟨$⟩ʳ j)) (phase-unit C j)))
  (NS.sum-reindex (permutation C) (λ j → parity (M i j))))

-- Exact γ-division commutes with both actions on matrices of weight zero.
divide-factor : ∀ u z → Evenγ z → divideGamma (u * z) ≡ u * divideGamma z
divide-factor u z he = trans
  (cong divideGamma (trans (cong (u *_) (sym (divide-complete z he)))
    (trans (cong (u *_) (*-comm γ (divideGamma z))) (sym (*-assoc u (divideGamma z) γ)))))
  (divide-multiple (u * divideGamma z))

divide-left : ∀ {n} C (M : Mat n) → weight M ≡ 0 → divideMatrix (act C M) ≈ act C (divideMatrix M)
divide-left C M h i j = divide-factor (phase C i) (M (permutation C P.⟨$⟩ʳ i) j)
  (zero-weight-even M h (permutation C P.⟨$⟩ʳ i) j)

divide-right : ∀ {n} C (M : Mat n) → weight M ≡ 0 → divideMatrix (actRight C M) ≈ actRight C (divideMatrix M)
divide-right C M h i j = divide-factor (phase C j) (M i (permutation C P.⟨$⟩ʳ j))
  (zero-weight-even M h i (permutation C P.⟨$⟩ʳ j))
