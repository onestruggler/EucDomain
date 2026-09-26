{-# OPTIONS --safe --without-K #-}

-- Norm-one Gaussian integers are exactly the four scalar Clifford phases.
module Quantum.Synthesis.Ring.Properties.Gaussian.Units where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra using (Unit)
open import Quantum.Synthesis.Ring.Properties.Gaussian.NormParity using (norm-product-real)
open import Integer.Squares using (square-nonnegative; small-square)
open import Finite.Check using (checkFin; decAll)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Fin using (Fin; #_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F)
open import Data.Vec.Base using (Vec; lookup; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

phaseToZI : Fin 4 → ZComplex
phaseToZI 0F = 1#
phaseToZI 1F = TC.i
phaseToZI 2F = Cplx (- (+ 1)) (+ 0)
phaseToZI 3F = Cplx (+ 0) (- (+ 1))

smallCode : ℤ → Set
smallCode x = (x ≡ + 0) ⊎ (x ≡ + 1) ⊎ (x ≡ -[1+ 0 ])

small-unit : ∀ a b → smallCode a → smallCode b → a Z.* a Z.+ b Z.* b ≡ + 1 →
  Σ[ p ∈ Fin 4 ] Cplx a b ≡ phaseToZI p
small-unit .(+ 0) .(+ 0) (inj₁ refl) (inj₁ refl) ()
small-unit .(+ 0) .(+ 1) (inj₁ refl) (inj₂ (inj₁ refl)) h = 1F , refl
small-unit .(+ 0) .(-[1+ 0 ]) (inj₁ refl) (inj₂ (inj₂ refl)) h = 3F , refl
small-unit .(+ 1) .(+ 0) (inj₂ (inj₁ refl)) (inj₁ refl) h = 0F , refl
small-unit .(+ 1) .(+ 1) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) ()
small-unit .(+ 1) .(-[1+ 0 ]) (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) ()
small-unit .(-[1+ 0 ]) .(+ 0) (inj₂ (inj₂ refl)) (inj₁ refl) h = 2F , refl
small-unit .(-[1+ 0 ]) .(+ 1) (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) ()
small-unit .(-[1+ 0 ]) .(-[1+ 0 ]) (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) ()

norm-one-phase : ∀ z → TC.norm z ≡ + 1 → Σ[ p ∈ Fin 4 ] z ≡ phaseToZI p
norm-one-phase (Cplx a b) h = small-unit a b (small-square a aBound) (small-square b bBound) h
  where
  aBound : a Z.* a Z.≤ + 1
  aBound = subst (λ x → a Z.* a Z.≤ x) h
    (subst (λ x → x Z.≤ a Z.* a Z.+ b Z.* b) (ZP.+-identityʳ (a Z.* a))
      (ZP.+-monoʳ-≤ (a Z.* a) (square-nonnegative b)))
  bBound : b Z.* b Z.≤ + 1
  bBound = subst (λ x → b Z.* b Z.≤ x) h
    (subst (λ x → x Z.≤ a Z.* a Z.+ b Z.* b) (ZP.+-identityˡ (b Z.* b))
      (ZP.+-monoˡ-≤ (b Z.* b) (square-nonnegative a)))

unit-phase : ∀ z → z * TC.adj z ≡ 1# → Σ[ p ∈ Fin 4 ] z ≡ phaseToZI p
unit-phase z h = norm-one-phase z (trans (sym (norm-product-real z)) (cong re h))

abstract
  phaseToZI-unit : ∀ p → Unit (phaseToZI p)
  phaseToZI-unit = checkFin 4 _ (λ p → (phaseToZI p * TC.adj (phaseToZI p)) TC.≟ 1#) tt

-- Multiplication of the four phases, as addition of their exponents mod 4.
phaseAddData : Vec (Vec (Fin 4) 4) 4
phaseAddData = ((# 0) ∷ (# 1) ∷ (# 2) ∷ (# 3) ∷ []) ∷
  ((# 1) ∷ (# 2) ∷ (# 3) ∷ (# 0) ∷ []) ∷
  ((# 2) ∷ (# 3) ∷ (# 0) ∷ (# 1) ∷ []) ∷
  ((# 3) ∷ (# 0) ∷ (# 1) ∷ (# 2) ∷ []) ∷ []

phaseAdd : Fin 4 → Fin 4 → Fin 4
phaseAdd k l = lookup (lookup phaseAddData k) l

abstract
  phase-add : ∀ k l → phaseToZI (phaseAdd k l) ≡ phaseToZI k * phaseToZI l
  phase-add = checkFin 4 _ (λ k → decAll 4 _ (λ l → phaseToZI (phaseAdd k l) TC.≟ (phaseToZI k * phaseToZI l))) tt
