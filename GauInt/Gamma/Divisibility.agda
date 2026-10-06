{-# OPTIONS --safe --without-K #-}

-- Divisibility by powers of gamma: exact quotients, sums and differences of
-- congruent values, lowering the exponent, and the integer criterion modulo 4.
module GauInt.Gamma.Divisibility where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (module GaussianSolver; *-comm; +-identityˡ)
open import GauInt.Gamma using (γ; powγ; Evenγ)
open import GauInt.Gamma.Congruence using (Cong; cong?; cong-refl; cong-add; cong-trans; lower; quotient; quotient-multiple)
import Integer.Congruence as IC
open import Data.Nat using (_≤_; _≤′_; ≤′-refl; ≤′-step)
import Data.Nat.Properties as NP
open import Data.Integer using (+_)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

-- Congruence at a lower exponent follows from congruence at a higher one.
lower-to : ∀ m n a b → m ≤ n → Cong n a b → Cong m a b
lower-to m n a b hm = go (NP.≤⇒≤′ hm)
  where
  go : ∀ {n} → m ≤′ n → Cong n a b → Cong m a b
  go ≤′-refl h = h
  go (≤′-step {n} p) h = go p (lower n a b h)

abstract
  divisible-reconstruct : ∀ n z → Cong n z 0# → z ≡ powγ n * quotient n z
  divisible-reconstruct n z (q , h) = trans hz
    (trans (*-comm q (powγ n)) (cong (powγ n *_) (sym hq)))
    where
    hz : z ≡ q * powγ n
    hz = trans h (+-identityˡ (q * powγ n))
    hq : quotient n z ≡ q
    hq = trans (cong (quotient n) hz) (quotient-multiple n q)

  difference-divisible : ∀ n a b → Cong n a b → Cong n (a - b) 0#
  difference-divisible n a b (q , h) = q , trans (cong (_- b) h)
    (solve 3 (λ b q p → (b :+ q :* p) :- b := con 0# :+ q :* p) refl b q (powγ n))
    where open GaussianSolver

  -- Two is divisible by gamma squared, so congruent values have a
  -- divisible sum at every exponent up to two.
  two-divisible : ∀ b → Cong 2 (b + b) 0#
  two-divisible b = (- TC.i) * b ,
    solve 1 (λ b → b :+ b := con 0# :+ (con (- TC.i) :* b) :* con (powγ 2)) refl b
    where open GaussianSolver

  sum-divisible : ∀ n a b → n ≤ 2 → Cong n a b → Cong n (a + b) 0#
  sum-divisible n a b hn h = cong-trans n (a + b) (b + b) 0#
    (cong-add n a b b b h (cong-refl n b)) (lower-to n 2 (b + b) 0# hn (two-divisible b))

even-factor : ∀ z → Evenγ z → Cong 2 (γ * z) 0#
even-factor z (q , h) = q , trans (cong (γ *_) h)
  (solve 1 (λ q → con γ :* (q :* con γ) := con 0# :+ q :* con (powγ 2)) refl q)
  where open GaussianSolver

-- An integer is divisible by four exactly when it is divisible by gamma⁴ = -4.
four-to-gamma : ∀ x → IC.Cong (+ 4) x (+ 0) → Cong 4 (Cplx x (+ 0)) 0#
four-to-gamma x (q , h) = Cplx (Z.- q) (+ 0) , cong₂ Cplx
  (trans h (solve 1 (λ q → con (+ 0) :+ con (+ 4) :* q :=
    con (+ 0) :+ ((:- q) :* con (Z.- (+ 4)) :- con (+ 0))) refl q))
  (solve 1 (λ q → con (+ 0) := con (+ 0) :+ ((:- q) :* con (+ 0) :+ con (+ 0))) refl q)
  where open +-*-Solver

gamma-to-four : ∀ x → Cong 4 (Cplx x (+ 0)) 0# → IC.Cong (+ 4) x (+ 0)
gamma-to-four x (Cplx u v , h) = Z.- u , trans (cong re h)
  (solve 2 (λ u v → con (+ 0) :+ (u :* con (Z.- (+ 4)) :- v :* con (+ 0)) :=
    con (+ 0) :+ con (+ 4) :* (:- u)) refl u v)
  where open +-*-Solver

four? : ∀ x → Dec (IC.Cong (+ 4) x (+ 0))
four? x = map′ (gamma-to-four x) (four-to-gamma x) (cong? 4 (Cplx x (+ 0)) 0#)
