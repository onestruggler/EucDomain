{-# OPTIONS --safe --without-K #-}

module GauInt.Gamma where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.GeneralisedArithmetic as Iteration
import Data.Nat.Properties as NP
open import Data.Integer using (+_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (subst)

γ : ZComplex
γ = Cplx (+ 1) (+ 1)

-- Scalar divisibility belongs below the matrix and circuit layers.
Evenγ : ZComplex → Set
Evenγ z = Σ[ q ∈ ZComplex ] z ≡ q * γ

Oddγ : ZComplex → Set
Oddγ z = ¬ Evenγ z

gaussianParity : ZComplex → ℕ
gaussianParity z = Z.∣ re z Z.+ im z ∣ Data.Nat.% 2

even-mul : ∀ z x → Evenγ x → Evenγ (z * x)
even-mul z x (q , h) = z * q , trans (cong (z *_) h) (sym (*-assoc z q γ))

even-unscale : ∀ u x → Unit u → Evenγ (u * x) → Evenγ x
even-unscale u x hu h = subst Evenγ (unit-unscale u x hu) (even-mul (TC.adj u) (u * x) h)

-- The generic fold shares recursive values while retaining the linear equation.
powγ : ℕ → ZComplex
powγ = Iteration.fold 1# (_* γ)

γ-square : γ * γ ≡ (Cplx (+ 2) (+ 0)) * TC.i
γ-square = refl

powγ-add : ∀ m n → powγ (m + n) ≡ powγ m * powγ n
powγ-add m zero = trans (cong powγ (NP.+-identityʳ m)) (sym (*-identityʳ (powγ m)))
powγ-add m (suc n) = trans (cong powγ (NP.+-suc m n))
  (trans (cong (_* γ) (powγ-add m n)) (*-assoc (powγ m) (powγ n) γ))

recover-re : ∀ a b → (a Z.- b) Z.+ (a Z.+ b) ≡ (+ 2) Z.* a
recover-re = solve 2 (λ a b → (a :- b) :+ (a :+ b) := con (+ 2) :* a) refl

recover-im : ∀ a b → (a Z.+ b) Z.- (a Z.- b) ≡ (+ 2) Z.* b
recover-im = solve 2 (λ a b → (a :+ b) :- (a :- b) := con (+ 2) :* b) refl

γ-mul-coordinates : ∀ a b → γ * Cplx a b ≡ Cplx (a Z.- b) (a Z.+ b)
γ-mul-coordinates a b = cong₂ Cplx
  (solve 2 (λ a b → con (+ 1) :* a :- con (+ 1) :* b := a :- b) refl a b)
  (solve 2 (λ a b → con (+ 1) :* b :+ con (+ 1) :* a := a :+ b) refl a b)

γ-cancel : ∀ {x y} → γ * x ≡ γ * y → x ≡ y
γ-cancel {Cplx a b} {Cplx c d} h = cong₂ Cplx
  (ZP.*-cancelˡ-≡ (+ 2) a c
    (trans (sym (recover-re a b)) (trans (cong₂ Z._+_ hr hi) (recover-re c d))))
  (ZP.*-cancelˡ-≡ (+ 2) b d
    (trans (sym (recover-im a b)) (trans (cong₂ Z._-_ hi hr) (recover-im c d))))
  where
  hc = trans (sym (γ-mul-coordinates a b)) (trans h (γ-mul-coordinates c d))
  hr = cong re hc
  hi = cong im hc

powγ-cancel : ∀ n {x y} → powγ n * x ≡ powγ n * y → x ≡ y
powγ-cancel zero {x} {y} h = trans (sym (*-identityˡ x)) (trans h (*-identityˡ y))
powγ-cancel (suc n) {x} {y} h = powγ-cancel n (γ-cancel
  (trans (swap x) (trans h (sym (swap y)))))
  where
  swap : ∀ z → γ * (powγ n * z) ≡ (powγ n * γ) * z
  swap z = trans (sym (*-assoc γ (powγ n) z)) (cong (_* z) (*-comm γ (powγ n)))
