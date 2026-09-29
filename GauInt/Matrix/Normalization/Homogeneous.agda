{-# OPTIONS --safe --without-K --termination-depth=2 #-}

-- Homogeneous integer form survives least-denominator normalization.
module GauInt.Matrix.Normalization.Homogeneous where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Gamma
open import GauInt.TwoPower using (two; twoPower; four-not-two)
open import GauInt.Matrix
open import GauInt.Matrix.Gram
open import GauInt.Matrix.Integer
open import GauInt.Matrix.Homogeneous
open import GauInt.Matrix.Presentation
open import GauInt.Matrix.Normalization
open import GauInt.Matrix.Normalization.Minimal
open import GauInt.Matrix.Denominator
open import GauInt.Matrix.Normalization.Gram using (gram-equivalent)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using () renaming (+-comm to nat+-comm)
open import Data.Fin.Patterns using (0F)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

factor-two-equivalent : ∀ {n} (M R : Mat n) k → M ≈ scale (powγ 2) R →
  Equivalent (scaled R k) (scaled M (suc (suc k)))
factor-two-equivalent M R k h i j = trans
  (cong (_* R i j) (trans (cong powγ (nat+-comm 2 k)) (powγ-add k 2)))
  (trans (*-assoc (powγ k) (powγ 2) (R i j)) (cong (powγ k *_) (sym (h i j))))

factor-at-one-impossible : ∀ (M R : Mat 6) → gram M ≈ scale (twoPower 1) identity →
  M ≈ scale (powγ 2) R → ⊥
factor-at-one-impossible M R hGram eq = four-not-two (gram R 0F 0F) h
  where
  h : (two * two) * gram R 0F 0F ≡ two
  h = trans (sym (gram-scale (powγ 2) R 0F 0F))
    (trans (sym (gram-cong {M = M} {N = scale (powγ 2) R} eq 0F 0F))
      (trans (hGram 0F 0F) (*-identityʳ two)))

one-even-impossible : ∀ (M : Mat 6) → gram M ≈ scale (twoPower 1) identity →
  Homogeneous M → ¬ (scale γ (divideMatrix M) ≈ M)
one-even-impossible M hGram hHom he = reject (homogeneous-even-factor M hHom he)
  where
  reject : (Σ[ R ∈ Mat 6 ] Homogeneous R × (M ≈ scale (powγ 2) R)) → ⊥
  reject (R , hR , eq) = factor-at-one-impossible M R hGram eq

record HomogeneousNormalForm (M : Mat 6) (k : ℕ) : Set where
  constructor normalForm
  field
    normalMatrix : NormalizedMatrix 6
    represents : Equivalent (representation normalMatrix) (scaled M k)
    homogeneous : Homogeneous (numerator (representation normalMatrix))

normalize-two-step : ∀ k M → gram M ≈ scale (twoPower (suc (suc k))) identity → Homogeneous M →
  (∀ R → gram R ≈ scale (twoPower k) identity → Homogeneous R → HomogeneousNormalForm R k) →
  Dec (scale γ (divideMatrix M) ≈ M) → HomogeneousNormalForm M (suc (suc k))
normalize-two-step k M hG hH recurse (no notAll) = normalForm
  (normalizedMatrix (scaled M (suc (suc k))) (λ _ → failed-cancellation-primitive M notAll))
  (equivalent-refl (scaled M (suc (suc k)))) hH
normalize-two-step k M hG hH recurse (yes hEven) = build (homogeneous-even-factor M hH hEven)
  where
  build : (Σ[ R ∈ Mat 6 ] Homogeneous R × (M ≈ scale (powγ 2) R)) → HomogeneousNormalForm M (suc (suc k))
  build (R , hR , hFactor) = normalForm (HomogeneousNormalForm.normalMatrix rec)
    (equivalent-trans {A = representation (HomogeneousNormalForm.normalMatrix rec)}
      {B = scaled R k} {C = scaled M (suc (suc k))} (HomogeneousNormalForm.represents rec) hE)
    (HomogeneousNormalForm.homogeneous rec)
    where
    hE = factor-two-equivalent M R k hFactor
    hRG = gram-equivalent (scaled R k) (scaled M (suc (suc k))) hE hG
    rec = recurse R hRG hR

homogeneous-normal-form : ∀ k (M : Mat 6) → gram M ≈ scale (twoPower k) identity →
  Homogeneous M → HomogeneousNormalForm M k
homogeneous-normal-form zero M hG hH = normalForm (normalizedMatrix (scaled M zero) (λ ()))
  (equivalent-refl (scaled M zero)) hH
homogeneous-normal-form (suc zero) M hG hH = normalForm
  (normalizedMatrix (scaled M 1) (λ _ → failed-cancellation-primitive M (one-even-impossible M hG hH)))
  (equivalent-refl (scaled M 1)) hH
homogeneous-normal-form (suc (suc k)) M hG hH = normalize-two-step k M hG hH
  (homogeneous-normal-form k) (matrixEq (scale γ (divideMatrix M)) M)

normalization-homogeneous : ∀ k (M : Mat 6) → gram M ≈ scale (twoPower k) identity →
  Homogeneous M → Homogeneous (numerator (value (normalizeAt k M)))
normalization-homogeneous k M hG hH = homogeneous-cong
  (normalized-numerator-unique (normalizeCertified (scaled M k)) (HomogeneousNormalForm.normalMatrix result) hE)
  (HomogeneousNormalForm.homogeneous result)
  where
  result = homogeneous-normal-form k M hG hH
  hE : Equivalent (representation (normalizeCertified (scaled M k))) (representation (HomogeneousNormalForm.normalMatrix result))
  hE = equivalent-trans {A = representation (normalizeCertified (scaled M k))} {B = scaled M k}
    {C = representation (HomogeneousNormalForm.normalMatrix result)} (equivalent (normalizeAt k M))
    (equivalent-sym {A = representation (HomogeneousNormalForm.normalMatrix result)} {B = scaled M k}
      (HomogeneousNormalForm.represents result))
