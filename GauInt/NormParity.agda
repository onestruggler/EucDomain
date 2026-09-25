{-# OPTIONS --safe --without-K #-}

-- Even norm forces gamma divisibility, including negative coordinates.
module GauInt.NormParity where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (Evenγ)
open import GauInt.TwoPower using (twoPower; twoPowerInt; twoPower-lift)
open import Integer.Parity
open import Integer.Congruence
open import Integer.Residues using (four-to-two)
open import Integer.Parity using (parity-congruent)
open import Data.Nat using (suc)
open import Data.Integer using (ℤ; +_; _/ℕ_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

equal-parities-even : ∀ a b → parity a ≡ parity b → Evenγ (Cplx a b)
equal-parities-even a b hp = Cplx (p Z.+ x Z.+ y) (y Z.- x) , cong₂ Cplx
  (trans (parity-decomposition a) (solve 3 (λ p x y → p :+ con (+ 2) :* x :=
    (p :+ x :+ y) :* con (+ 1) :- (y :- x) :* con (+ 1)) refl p x y))
  (trans hb (solve 3 (λ p x y → p :+ con (+ 2) :* y :=
    (p :+ x :+ y) :* con (+ 1) :+ (y :- x) :* con (+ 1)) refl p x y))
  where
  p = + (parity a)
  x = a /ℕ 2
  y = b /ℕ 2
  hb = trans (parity-decomposition b) (cong (λ n → + n Z.+ (+ 2) Z.* y) (sym hp))

norm-parity-congruence : ∀ a b → Cong (+ 2) (TC.norm (Cplx a b)) (+ (parity a) Z.+ + (parity b))
norm-parity-congruence a b = cong-add (+ 2) (a Z.* a) (+ (parity a)) (b Z.* b) (+ (parity b))
  (four-to-two (a Z.* a) (+ (parity a)) (square-congruence a))
  (four-to-two (b Z.* b) (+ (parity b)) (square-congruence b))

even-norm-divisible : ∀ z → Cong (+ 2) (TC.norm z) (+ 0) → Evenγ z
even-norm-divisible (Cplx a b) h = equal-parities-even a b equal
  where
  paritySum : parity (+ (parity a) Z.+ + (parity b)) ≡ 0
  paritySum = parity-congruent (+ (parity a) Z.+ + (parity b)) (+ 0)
    (cong-trans (+ 2) (+ (parity a) Z.+ + (parity b)) (TC.norm (Cplx a b)) (+ 0)
      (cong-sym (+ 2) (TC.norm (Cplx a b)) (+ (parity a) Z.+ + (parity b)) (norm-parity-congruence a b)) h)
  impossible : 1 ≡ 0 → ⊥
  impossible ()
  check : parity (+ (parity a) Z.+ + (parity b)) ≡ 0 → parity a ≡ parity b
  check hs with parity-cases a | parity-cases b
  ... | inj₁ ha | inj₁ hb = trans ha (sym hb)
  ... | inj₂ ha | inj₂ hb = trans ha (sym hb)
  ... | inj₁ ha | inj₂ hb = ⊥-elim (impossible (trans (sym (cong parity (cong₂ (λ x y → + x Z.+ + y) ha hb))) hs))
  ... | inj₂ ha | inj₁ hb = ⊥-elim (impossible (trans (sym (cong parity (cong₂ (λ x y → + x Z.+ + y) ha hb))) hs))
  equal = check paritySum

norm-product-real : ∀ z → re (z * TC.adj z) ≡ TC.norm z
norm-product-real (Cplx a b) = solve 2 (λ a b → a :* a :- b :* (:- b) := a :* a :+ b :* b) refl a b

positive-scalar-even : ∀ z n → z * TC.adj z ≡ twoPower (suc n) → Evenγ z
positive-scalar-even z n h = even-norm-divisible z (twoPowerInt n , trans hn
  (sym (ZP.+-identityˡ ((+ 2) Z.* twoPowerInt n))))
  where
  hn : TC.norm z ≡ (+ 2) Z.* twoPowerInt n
  hn = trans (sym (norm-product-real z)) (cong re (trans h (twoPower-lift (suc n))))
