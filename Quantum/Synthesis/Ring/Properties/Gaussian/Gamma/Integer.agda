{-# OPTIONS --safe --without-K #-}
module Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.Integer where
open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; _/_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma using (γ; powγ; Evenγ)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra
open import Data.Integer using (ℤ; +_; -[1+_]; _/ℕ_)
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

open import Integer.Parity
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.Division using (divideGamma; divide-complete)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma using (Oddγ; γ-mul-coordinates; recover-re)

zero-parity-even : ∀ x → parity x ≡ 0 → Evenγ (lift x)
zero-parity-even x hp = Cplx q (Z.- q) , trans (cong lift hx) product
  where
  q = x /ℕ 2
  hx : x ≡ (+ 2) Z.* q
  hx = trans (parity-decomposition x) (trans (cong (λ p → + p Z.+ (+ 2) Z.* q) hp) (ZP.+-identityˡ ((+ 2) Z.* q)))
  product : lift ((+ 2) Z.* q) ≡ Cplx q (Z.- q) * γ
  product = cong₂ Cplx
    (solve 1 (λ q → con (+ 2) :* q := q :* con (+ 1) :- (:- q) :* con (+ 1)) refl q)
    (solve 1 (λ q → con (+ 0) := q :* con (+ 1) :+ (:- q) :* con (+ 1)) refl q)

odd-parity-one : ∀ x → Oddγ (lift x) → parity x ≡ 1
odd-parity-one x h with parity-cases x
... | inj₁ hp = ⊥-elim (h (zero-parity-even x hp))
... | inj₂ hp = hp

halfReal : ℤ → ℤ
halfReal x = re (divideGamma (lift x))

even-integer-double : ∀ x → Evenγ (lift x) → x ≡ (+ 2) Z.* halfReal x
even-integer-double x hx = trans (sym hr)
  (trans (sym (ZP.+-identityʳ (a Z.- b)))
    (trans (cong (λ z → (a Z.- b) Z.+ z) (sym hi)) (recover-re a b)))
  where
  a = re (divideGamma (lift x))
  b = im (divideGamma (lift x))
  eq : Cplx (a Z.- b) (a Z.+ b) ≡ lift x
  eq = trans (sym (γ-mul-coordinates a b)) (divide-complete (lift x) hx)
  hr = cong re eq
  hi = cong im eq

even-integer-factor : ∀ x → Evenγ (lift x) → lift x ≡ (1# + 1#) * lift (halfReal x)
even-integer-factor x hx = trans (cong lift (even-integer-double x hx)) (lift-mul (+ 2) (halfReal x))

