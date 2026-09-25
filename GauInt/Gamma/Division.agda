{-# OPTIONS --safe --without-K #-}

-- The executable quotient is the exact quotient whenever γ divides z.
module GauInt.Gamma.Division where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; _/_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (γ; powγ; Evenγ)
open import GauInt.Algebra
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Z
import Data.Integer.Properties as ZP
import Data.Integer.DivMod as ZD
open import Data.Nat using (suc)
import Data.Nat as N
import Data.Nat.DivMod as ND
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

divideGamma : ZComplex → ZComplex
divideGamma (Cplx a b) = Cplx ((a + b) / (+ 2)) ((b - a) / (+ 2))

mod-double : ∀ n → (n N.* 2) ND.% 2 ≡ 0
mod-double n = ND.m*n%n≡0 n 2

quotient-double : ∀ n → (n N.* 2) ND./ 2 ≡ n
quotient-double n = ND.m*n/n≡m n 2

half-double : ∀ x → (x * (+ 2)) / (+ 2) ≡ x
half-double (+ n) rewrite ZD.div-pos-is-/ℕ ((+ n) Z.* (+ 2)) 2 {{_}}
  | sym (ZP.pos-* n 2) = cong +_ (ND.m*n/n≡m n 2)
half-double -[1+ n ]
  rewrite ZD.div-pos-is-/ℕ (-[1+ n ] Z.* (+ 2)) 2 {{_}}
  | mod-double (suc n) | quotient-double (suc n) = refl

divide-multiple : ∀ q → divideGamma (q * γ) ≡ q
divide-multiple (Cplx a b) = cong₂ Cplx
  (trans (cong (λ z → z / (+ 2)) (solve 2 (λ a b →
    (a :* con (+ 1) :- b :* con (+ 1)) :+ (a :* con (+ 1) :+ b :* con (+ 1)) := a :* con (+ 2)) refl a b))
    (half-double a))
  (trans (cong (λ z → z / (+ 2)) (solve 2 (λ a b →
    (a :* con (+ 1) :+ b :* con (+ 1)) :- (a :* con (+ 1) :- b :* con (+ 1)) := b :* con (+ 2)) refl a b))
    (half-double b))

divide-complete : ∀ z → Evenγ z → γ * divideGamma z ≡ z
divide-complete z (q , eq) = trans
  (cong (λ w → γ * divideGamma w) eq)
  (trans (cong (γ *_) (divide-multiple q)) (trans (*-comm γ q) (sym eq)))
