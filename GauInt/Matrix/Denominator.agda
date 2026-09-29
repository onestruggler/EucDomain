{-# OPTIONS --safe --without-K #-}

-- Minimal-denominator lower bound, for any finite matrix dimension.
-- Corresponds to Lean's UnitaryDi.lde_le_exponent and NormalizedMat6.exponent_le.
module GauInt.Matrix.Denominator where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Gamma
open import GauInt.Matrix
open import GauInt.Matrix.Presentation using (ScaledMatrix; scaled; numerator; exponent; Equivalent)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

Primitive : ∀ {n} → Mat n → Set
Primitive {n} M = Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] Oddγ (M i j)

factor-suc : ∀ k z → powγ (suc k) * z ≡ γ * (powγ k * z)
factor-suc k z = trans (cong (_* z) (*-comm (powγ k) γ)) (*-assoc γ (powγ k) z)

primitive-bound : ∀ {n} a b (M N : Mat n) → (0 < a → Primitive M) →
  Equivalent (scaled M a) (scaled N b) → a ≤ b
primitive-bound zero b M N prim eq = z≤n
primitive-bound (suc a) zero M N prim eq with prim (s≤s z≤n)
... | i , j , odd = ⊥-elim (odd (powγ a * N i j , trans (sym (*-identityˡ (M i j)))
  (trans (eq i j) (trans (factor-suc a (N i j)) (*-comm γ (powγ a * N i j))))))
primitive-bound (suc a) (suc b) M N prim eq = s≤s
  (primitive-bound a b M N (λ _ → prim (s≤s z≤n))
    (λ i j → γ-cancel (trans (sym (factor-suc b (M i j))) (trans (eq i j) (factor-suc a (N i j))))))

record NormalizedMatrix (n : ℕ) : Set where
  constructor normalizedMatrix
  field
    representation : ScaledMatrix n
    minimal : 0 < exponent representation → Primitive (numerator representation)
open NormalizedMatrix public

exponent-lower : ∀ {n} (A : NormalizedMatrix n) (B : ScaledMatrix n) →
  Equivalent (representation A) B → exponent (representation A) ≤ exponent B
exponent-lower A B = primitive-bound (exponent (representation A)) (exponent B)
  (numerator (representation A)) (numerator B) (minimal A)
