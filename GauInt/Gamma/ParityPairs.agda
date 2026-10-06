{-# OPTIONS --safe --without-K #-}

-- Equal binary residues make integer sums and differences gamma-divisible.
module GauInt.Gamma.ParityPairs where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (lift)
open import Integer.Parity
open import GauInt.Gamma using (Evenγ)
open import Data.Integer using (ℤ; +_; _/ℕ_)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

double-even : ∀ q → Evenγ (lift ((+ 2) Z.* q))
double-even q = Cplx q (Z.- q) , cong₂ Cplx
  (solve 1 (λ q → con (+ 2) :* q := q :* con (+ 1) :- (:- q) :* con (+ 1)) refl q)
  (solve 1 (λ q → con (+ 0) := q :* con (+ 1) :+ (:- q) :* con (+ 1)) refl q)

sum-even : ∀ x y → parity x ≡ parity y → Evenγ (lift (x Z.+ y))
sum-even x y h = subst (λ z → Evenγ (lift z)) (sym eq) (double-even q)
  where
  p = + (parity x)
  a = x /ℕ 2
  b = y /ℕ 2
  q = p Z.+ a Z.+ b
  hx = parity-decomposition x
  hy = trans (parity-decomposition y) (cong (λ n → + n Z.+ (+ 2) Z.* b) (sym h))
  eq : x Z.+ y ≡ (+ 2) Z.* q
  eq = trans (cong₂ Z._+_ hx hy)
    (solve 3 (λ p a b → (p :+ con (+ 2) :* a) :+ (p :+ con (+ 2) :* b)
      := con (+ 2) :* (p :+ a :+ b)) refl p a b)

difference-even : ∀ x y → parity x ≡ parity y → Evenγ (lift (x Z.- y))
difference-even x y h = subst (λ z → Evenγ (lift z)) (sym eq) (double-even q)
  where
  p = + (parity x)
  a = x /ℕ 2
  b = y /ℕ 2
  q = a Z.- b
  hx = parity-decomposition x
  hy = trans (parity-decomposition y) (cong (λ n → + n Z.+ (+ 2) Z.* b) (sym h))
  eq : x Z.- y ≡ (+ 2) Z.* q
  eq = trans (cong₂ Z._-_ hx hy)
    (solve 3 (λ p a b → (p :+ con (+ 2) :* a) :- (p :+ con (+ 2) :* b)
      := con (+ 2) :* (a :- b)) refl p a b)
