{-# OPTIONS --safe --without-K #-}

-- A common gamma factor in a unit-phase integer matrix is actually a
-- common factor of two. Removing gamma squared preserves homogeneity.
module GauInt.Matrix.Homogeneous where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Gamma
open import GauInt.Matrix
open import GauInt.Matrix.Normalization using (divideMatrix)
open import GauInt.Gamma.Division using (divideGamma)
open import GauInt.Matrix.Integer
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import GauInt.Gamma.Integer using (halfReal; even-integer-factor)

homogeneous-even-factor : ∀ {n} (M : Mat n) → Homogeneous M → scale γ (divideMatrix M) ≈ M →
  Σ[ R ∈ Mat n ] Homogeneous R × (M ≈ scale (powγ 2) R)
homogeneous-even-factor M (u , N , hu , hN) he = R ,
  ((- TC.i) * u , Q , unit-product (- TC.i) u refl hu , ≈-refl) , factor
  where
  evenM : ∀ i j → Evenγ (M i j)
  evenM i j = divideGamma (M i j) , trans (sym (he i j)) (*-comm γ (divideGamma (M i j)))
  evenN : ∀ i j → Evenγ (lift (N i j))
  evenN i j = even-unscale u (lift (N i j)) hu (subst Evenγ (hN i j) (evenM i j))
  Q : IntMat _
  Q i j = halfReal (N i j)
  R : Mat _
  R = scale ((- TC.i) * u) (liftMatrix Q)
  factor : M ≈ scale (powγ 2) R
  factor i j = trans (hN i j)
    (trans (cong (u *_) (even-integer-factor (N i j) (evenN i j)))
      (GaussianSolver.solve 2 (λ u x → u GaussianSolver.:* (GaussianSolver.con (1# + 1#) GaussianSolver.:* x)
        GaussianSolver.:= GaussianSolver.con (powγ 2) GaussianSolver.:*
          ((GaussianSolver.con (- TC.i) GaussianSolver.:* u) GaussianSolver.:* x)) refl u (lift (Q i j))))
