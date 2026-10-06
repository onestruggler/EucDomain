{-# OPTIONS --safe --without-K #-}

-- Gaussian Gram equations imply even binary row and column overlaps.
module GauInt.Matrix.ResidueArithmetic where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.Matrix.Gram using (columnGram)
open import Natural.Sum using (sumNat)
open import GauInt.Parity
open import GauInt.Gamma using (Evenγ; even-mul) renaming (gaussianParity to parity)
open import GauInt.TwoPower using (twoPower)
open import Integer.Sum using (intSum)
open import Integer.Congruence
import Integer.Parity as IP
open import Integer.Parity using (parity-congruent)
open import Integer.Residues using (multiple2-natural)
import Natural.Sum as NS
open import Data.Nat using (ℕ; zero; suc; _%_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

coordinates : ZComplex → ℤ
coordinates z = re z Z.+ im z

residue-congruence : ∀ z → Cong (+ 2) (coordinates z) (+ (parity z))
residue-congruence z = subst (λ k → Cong (+ 2) (coordinates z) (+ k))
  (sym (parity-integer z)) (IP.parity-congruence (coordinates z))

conjugate-parity : ∀ z → parity (TC.adj z) ≡ parity z
conjugate-parity (Cplx a b) = trans (parity-integer (TC.adj (Cplx a b)))
  (trans (parity-congruent (a Z.- b) (a Z.+ b)
    (Z.- b , solve 2 (λ a b → a :- b := (a :+ b) :+ con (+ 2) :* (:- b)) refl a b))
    (sym (parity-integer (Cplx a b))))

product-congruence : ∀ z w → Cong (+ 2) (coordinates (z * TC.adj w)) (+ (parity z) Z.* + (parity w))
product-congruence z@(Cplx a b) w@(Cplx c d) = cong-trans (+ 2)
  (coordinates (z * TC.adj w)) (coordinates z Z.* coordinates w) (+ (parity z) Z.* + (parity w))
  (Z.- (a Z.* d) , solve 4 (λ a b c d → (a :* c :- b :* (:- d)) :+ (a :* (:- d) :+ b :* c)
    := (a :+ b) :* (c :+ d) :+ con (+ 2) :* (:- (a :* d))) refl a b c d)
  (cong-mul (+ 2) (coordinates z) (+ (parity z)) (coordinates w) (+ (parity w))
    (residue-congruence z) (residue-congruence w))

coordinates-sum : ∀ {n} (f : Fin n → ZComplex) → coordinates (sum f) ≡ intSum (λ i → coordinates (f i))
coordinates-sum {zero} f = refl
coordinates-sum {suc n} f = trans
  (solve 4 (λ a b c d → (a :+ c) :+ (b :+ d) := (a :+ b) :+ (c :+ d)) refl
    (re (f zero)) (im (f zero)) (re (sum (λ i → f (suc i)))) (im (sum (λ i → f (suc i)))))
  (cong (λ x → coordinates (f zero) Z.+ x) (coordinates-sum (λ i → f (suc i))))

positive-sum : ∀ {n} (f : Fin n → ℕ) → intSum (λ i → + (f i)) ≡ + (sumNat f)
positive-sum {zero} f = refl
positive-sum {suc n} f = trans (cong (λ x → + (f zero) Z.+ x) (positive-sum (λ i → f (suc i))))
  (sym (ZP.pos-+ (f zero) (sumNat (λ i → f (suc i)))))

rowOverlap : ∀ {n} → Mat n → Fin n → Fin n → ℕ
rowOverlap M i j = sumNat (λ k → parity (M i k) * parity (M j k))

columnOverlap : ∀ {n} → Mat n → Fin n → Fin n → ℕ
columnOverlap M i j = sumNat (λ k → parity (M k i) * parity (M k j))

gram-overlap-congruence : ∀ {n} (M : Mat n) i j → Cong (+ 2) (coordinates (gram M i j)) (+ (rowOverlap M i j))
gram-overlap-congruence M i j = subst (λ x → Cong (+ 2) x (+ (rowOverlap M i j)))
  (sym (coordinates-sum (λ k → M i k * TC.adj (M j k))))
  (subst (λ y → Cong (+ 2) (intSum (λ k → coordinates (M i k * TC.adj (M j k)))) y)
    (positive-sum (λ k → parity (M i k) * parity (M j k)))
    (cong-sum (+ 2) (λ k → coordinates (M i k * TC.adj (M j k)))
      (λ k → + (parity (M i k) * parity (M j k)))
      (λ k → subst (Cong (+ 2) (coordinates (M i k * TC.adj (M j k))))
        (sym (ZP.pos-* (parity (M i k)) (parity (M j k)))) (product-congruence (M i k) (M j k)))))

twoPower-even : ∀ k → Evenγ (twoPower (suc k))
twoPower-even k = subst Evenγ (*-comm (twoPower k) (1# + 1#))
  (even-mul (twoPower k) (1# + 1#) (Cplx (+ 1) (Z.- (+ 1)) , refl))

gram-entry-zero : ∀ {n} (M : Mat n) k → gram M ≈ scale (twoPower (suc k)) identity → ∀ i j → parity (gram M i j) ≡ 0
gram-entry-zero M k h i j = even-parity-zero (gram M i j)
  (subst Evenγ (sym (h i j)) (subst Evenγ (*-comm (identity i j) (twoPower (suc k)))
    (even-mul (identity i j) (twoPower (suc k)) (twoPower-even k))))

gram-even-overlap : ∀ {n} (M : Mat n) k → gram M ≈ scale (twoPower (suc k)) identity → ∀ i j → rowOverlap M i j % 2 ≡ 0
gram-even-overlap M k h i j = multiple2-natural (rowOverlap M i j)
  (cong-trans (+ 2) (+ (rowOverlap M i j)) (coordinates (gram M i j)) (+ 0)
    (cong-sym (+ 2) (coordinates (gram M i j)) (+ (rowOverlap M i j)) (gram-overlap-congruence M i j))
    (subst (λ r → Cong (+ 2) (coordinates (gram M i j)) (+ r)) (gram-entry-zero M k h i j)
      (residue-congruence (gram M i j))))

column-overlap-correct : ∀ {n} (M : Mat n) i j → rowOverlap (adjoint M) i j ≡ columnOverlap M i j
column-overlap-correct M i j = NS.sum-cong (λ k → cong₂ _*_ (conjugate-parity (M k i)) (conjugate-parity (M k j)))

gram-even-column-overlap : ∀ {n} (M : Mat n) k → columnGram M ≈ scale (twoPower (suc k)) identity →
  ∀ i j → columnOverlap M i j % 2 ≡ 0
gram-even-column-overlap M k h i j = trans (cong (_% 2) (sym (column-overlap-correct M i j)))
  (gram-even-overlap (adjoint M) k h i j)
