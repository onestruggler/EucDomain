{-# OPTIONS --safe --without-K #-}

-- Powers of two in the Gaussian integers, their integer counterparts, and
-- their relation to the norms of powers of gamma.
module Quantum.Synthesis.Ring.Properties.Gaussian.TwoPower where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _*_; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra using (*-assoc; *-identityˡ; *-identityʳ; conj-mul; lift; lift-mul; module GaussianSolver)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma using (γ; powγ; powγ-cancel)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.GeneralisedArithmetic as Iteration
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open GaussianSolver

two : ZComplex
two = Cplx (+ 2) (+ 0)

two-cancel : ∀ {x y} → two * x ≡ two * y → x ≡ y
two-cancel {x} {y} h = powγ-cancel 2 (trans (sym (factor x)) (trans (cong (TC.i *_) h) (factor y)))
  where
  factor : ∀ z → TC.i * (two * z) ≡ powγ 2 * z
  factor z = sym (*-assoc TC.i two z)

twoPower : ℕ → ZComplex
twoPower = Iteration.fold 1# ((1# + 1#) *_)

twoPower-add : ∀ a b → twoPower (a + b) ≡ twoPower a * twoPower b
twoPower-add zero b = sym (*-identityˡ (twoPower b))
twoPower-add (suc a) b = trans (cong ((1# + 1#) *_) (twoPower-add a b))
  (sym (*-assoc (1# + 1#) (twoPower a) (twoPower b)))

twoPower-cancel : ∀ k {x y} → twoPower k * x ≡ twoPower k * y → x ≡ y
twoPower-cancel zero {x} {y} h = trans (sym (*-identityˡ x)) (trans h (*-identityˡ y))
twoPower-cancel (suc k) {x} {y} h = twoPower-cancel k
  (two-cancel (trans (sym (*-assoc (1# + 1#) (twoPower k) x))
    (trans h (*-assoc (1# + 1#) (twoPower k) y))))

powγ-norm : ∀ k → powγ k * TC.adj (powγ k) ≡ twoPower k
powγ-norm zero = refl
powγ-norm (suc k) = trans (cong (powγ (suc k) *_) (conj-mul (powγ k) γ))
  (trans (solve 2 (λ a b → (a :* con γ) :* (b :* con (TC.adj γ)) :=
    con (1# + 1#) :* (a :* b)) refl (powγ k) (TC.adj (powγ k)))
    (cong ((1# + 1#) *_) (powγ-norm k)))

twoPowerInt : ℕ → ℤ
twoPowerInt zero = + 1
twoPowerInt (suc k) = (+ 2) Z.* twoPowerInt k

twoPower-lift : ∀ k → twoPower k ≡ lift (twoPowerInt k)
twoPower-lift zero = refl
twoPower-lift (suc k) = trans (cong ((1# + 1#) *_) (twoPower-lift k))
  (sym (lift-mul (+ 2) (twoPowerInt k)))

twoPower-real : ∀ n → TC.adj (twoPower n) ≡ twoPower n
twoPower-real n = trans (cong TC.adj (twoPower-lift n)) (sym (twoPower-lift n))

twice-not-one : ∀ x → x Z.* (+ 2) ≢ (+ 1)
twice-not-one (+ zero) ()
twice-not-one (+ suc n) ()
twice-not-one -[1+ n ] ()

four-not-two : ∀ z → (two * two) * z ≢ two
four-not-two z h = twice-not-one (re z) (trans (sym hr) (cong re h2))
  where
  h2 : two * z ≡ 1#
  h2 = two-cancel (trans (sym (*-assoc two two z)) (trans h (sym (*-identityʳ two))))
  hr : re (two * z) ≡ re z Z.* (+ 2)
  hr = trans (cong (λ w → (+ 2) Z.* re z Z.- w) (ZP.*-zeroˡ (im z)))
    (trans (ZP.+-identityʳ ((+ 2) Z.* re z)) (ZP.*-comm (+ 2) (re z)))
