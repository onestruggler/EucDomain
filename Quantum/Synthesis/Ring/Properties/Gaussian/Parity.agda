{-# OPTIONS --safe --without-K #-}

-- The executable Gaussian residue agrees with divisibility by gamma.
module Quantum.Synthesis.Ring.Properties.Gaussian.Parity where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma using (γ; powγ; Evenγ; even-mul; even-unscale)
  renaming (gaussianParity to parity)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra using (Unit)
open import Integer.Congruence
import Integer.Parity as IP
open import Integer.Parity using (parity-congruent)
open import Quantum.Synthesis.Ring.Properties.Gaussian.NormParity using (equal-parities-even)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (ℕ; suc; _%_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

integer-neg-parity : ∀ x → IP.parity (Z.- x) ≡ IP.parity x
integer-neg-parity x = parity-congruent (Z.- x) x
  (Z.- x , solve 1 (λ x → :- x := x :+ con (+ 2) :* (:- x)) refl x)

absolute-parity : ∀ x → ∣ x ∣ % 2 ≡ IP.parity x
absolute-parity (+ n) = refl
absolute-parity -[1+ n ] = sym (integer-neg-parity (+ suc n))

parity-integer : ∀ z → parity z ≡ IP.parity (re z Z.+ im z)
parity-integer z = absolute-parity (re z Z.+ im z)

parity-cases : ∀ z → parity z ≡ 0 ⊎ parity z ≡ 1
parity-cases z with IP.parity-cases (re z Z.+ im z)
... | inj₁ h = inj₁ (trans (parity-integer z) h)
... | inj₂ h = inj₂ (trans (parity-integer z) h)

even-parity-zero : ∀ z → Evenγ z → parity z ≡ 0
even-parity-zero z (Cplx a b , h) = trans (cong parity h)
  (trans (parity-integer (Cplx a b * γ)) (parity-congruent _ (+ 0)
    (a , solve 2 (λ a b → (a :* con (+ 1) :- b :* con (+ 1)) :+
      (a :* con (+ 1) :+ b :* con (+ 1)) := con (+ 0) :+ con (+ 2) :* a) refl a b)))

sum-zero-equal : ∀ a b → IP.parity (a Z.+ b) ≡ 0 → IP.parity a ≡ IP.parity b
sum-zero-equal a b h = finish hs
  where
  hs : IP.parity (+ (IP.parity a) Z.+ + (IP.parity b)) ≡ 0
  hs = trans (sym (parity-congruent (a Z.+ b) (+ (IP.parity a) Z.+ + (IP.parity b))
    (cong-add (+ 2) a (+ (IP.parity a)) b (+ (IP.parity b))
      (IP.parity-congruence a) (IP.parity-congruence b)))) h
  bad : 1 ≡ 0 → ⊥
  bad ()
  finish : IP.parity (+ (IP.parity a) Z.+ + (IP.parity b)) ≡ 0 → IP.parity a ≡ IP.parity b
  finish h with IP.parity-cases a | IP.parity-cases b
  ... | inj₁ ha | inj₁ hb = trans ha (sym hb)
  ... | inj₂ ha | inj₂ hb = trans ha (sym hb)
  ... | inj₁ ha | inj₂ hb = ⊥-elim (bad (trans (sym (cong IP.parity (cong₂ (λ x y → + x Z.+ + y) ha hb))) h))
  ... | inj₂ ha | inj₁ hb = ⊥-elim (bad (trans (sym (cong IP.parity (cong₂ (λ x y → + x Z.+ + y) ha hb))) h))

zero-parity-even : ∀ z → parity z ≡ 0 → Evenγ z
zero-parity-even (Cplx a b) h = equal-parities-even a b
  (sum-zero-equal a b (trans (sym (parity-integer (Cplx a b))) h))

unit-parity : ∀ u z → Unit u → parity (u * z) ≡ parity z
unit-parity u z hu with parity-cases (u * z) | parity-cases z
... | inj₁ hx | inj₁ hy = trans hx (sym hy)
... | inj₂ hx | inj₂ hy = trans hx (sym hy)
... | inj₁ hx | inj₂ hy = ⊥-elim (bad (trans (sym hy)
  (even-parity-zero z (even-unscale u z hu (zero-parity-even (u * z) hx)))))
  where bad : 1 ≡ 0 → ⊥; bad ()
... | inj₂ hx | inj₁ hy = ⊥-elim (bad (trans (sym hx)
  (even-parity-zero (u * z) (even-mul u z (zero-parity-even z hy)))))
  where bad : 1 ≡ 0 → ⊥; bad ()
