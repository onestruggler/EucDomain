{-# OPTIONS --safe --without-K #-}

module GauInt.Matrix.Integer.Orthogonality where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.TwoPower using (twoPower; twoPowerInt; twoPower-lift)
open import GauInt.Matrix.Integer
open import Integer.Sum using (intSum)
open import GauInt.Matrix.Gram using (columnGram)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
import Data.Integer as Z
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

intTranspose : ∀ {n} → IntMat n → IntMat n
intTranspose N i j = N j i

identity-lift : ∀ {n} → identity {n} ≈ liftMatrix intIdentity
identity-lift zero zero = refl
identity-lift zero (suc j) = refl
identity-lift (suc i) zero = refl
identity-lift (suc i) (suc j) = identity-lift i j

intOrthogonal : ∀ {n} → IntMat n → ℕ → Set
intOrthogonal N k = ∀ i j → intSum (λ l → N i l Z.* N j l) ≡ twoPowerInt k Z.* intIdentity i j

adjoint-lift : ∀ {n} (N : IntMat n) → adjoint (liftMatrix N) ≈ liftMatrix (intTranspose N)
adjoint-lift N i j = refl

gram-lift : ∀ {n} (N : IntMat n) → gram (liftMatrix N) ≈ liftMatrix (intMul N (intTranspose N))
gram-lift N = ≈-trans
  (mul-cong {A = liftMatrix N} {B = liftMatrix N} ≈-refl (adjoint-lift N))
  (≈-sym (liftMatrix-mul N (intTranspose N)))

orthogonal-from-gram : ∀ {n} (N : IntMat n) k → gram (liftMatrix N) ≈ scale (twoPower k) identity →
  intOrthogonal N k
orthogonal-from-gram N k h i j = cong re
  (trans (sym (gram-lift N i j))
    (trans (h i j)
      (trans (cong₂ _*_ (twoPower-lift k) (identity-lift i j))
        (sym (lift-mul (twoPowerInt k) (intIdentity i j))))))

column-orthogonal-from-gram : ∀ {n} (N : IntMat n) k →
  columnGram (liftMatrix N) ≈ scale (twoPower k) identity → intOrthogonal (intTranspose N) k
column-orthogonal-from-gram N k h = orthogonal-from-gram (intTranspose N) k h
