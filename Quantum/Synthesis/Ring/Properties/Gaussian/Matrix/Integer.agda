{-# OPTIONS --safe --without-K #-}

module Quantum.Synthesis.Ring.Properties.Gaussian.Matrix.Integer where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra
open import Integer.Sum using (intSum)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Matrix
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

IntMat : ℕ → Set
IntMat n = Fin n → Fin n → ℤ

lift-sum : ∀ {n} (f : Fin n → ℤ) → lift (intSum f) ≡ sum (λ i → lift (f i))
lift-sum {zero} f = refl
lift-sum {suc n} f = trans (lift-add (f zero) (intSum (λ i → f (suc i))))
  (cong (lift (f zero) TC.+_) (lift-sum (λ i → f (suc i))))

liftMatrix : ∀ {n} → IntMat n → Mat n
liftMatrix M i j = lift (M i j)

intMul : ∀ {n} → IntMat n → IntMat n → IntMat n
intMul M N i j = intSum (λ k → M i k Z.* N k j)

liftMatrix-mul : ∀ {n} (M N : IntMat n) → liftMatrix (intMul M N) ≈ mul (liftMatrix M) (liftMatrix N)
liftMatrix-mul M N i j = trans (lift-sum (λ k → M i k Z.* N k j))
  (sum-cong (λ k → lift-mul (M i k) (N k j)))

Homogeneous : ∀ {n} → Mat n → Set
Homogeneous {n} M = Σ[ u ∈ ZComplex ] Σ[ N ∈ IntMat n ] Unit u × (M ≈ scale u (liftMatrix N))

homogeneous-cong : ∀ {n} {M N : Mat n} → M ≈ N → Homogeneous N → Homogeneous M
homogeneous-cong h (u , R , hu , hR) = u , R , hu , ≈-trans h hR

homogeneous-mul : ∀ {n} (M N : Mat n) → Homogeneous M → Homogeneous N → Homogeneous (mul M N)
homogeneous-mul M N (u , R , hu , hM) (v , S , hv , hN) = u * v , intMul R S , unit-product u v hu hv ,
  ≈-trans (mul-cong {A = M} {B = scale u (liftMatrix R)} {C = N} {D = scale v (liftMatrix S)} hM hN)
    (≈-trans (mul-scaled u v (liftMatrix R) (liftMatrix S))
      (scale-cong (u * v) (≈-sym (liftMatrix-mul R S))))

intIdentity : ∀ {n} → IntMat n
intIdentity zero zero = + 1
intIdentity zero (suc j) = + 0
intIdentity (suc i) zero = + 0
intIdentity (suc i) (suc j) = intIdentity i j

identity-homogeneous : ∀ {n} → Homogeneous (identity {n})
identity-homogeneous {n} = 1# , intIdentity , refl , (λ i j → trans (eq i j) (sym (*-identityˡ (lift (intIdentity i j)))))
  where
  eq : ∀ {m} (i j : Fin m) → identity i j ≡ lift (intIdentity i j)
  eq zero zero = refl
  eq zero (suc j) = refl
  eq (suc i) zero = refl
  eq (suc i) (suc j) = eq i j
