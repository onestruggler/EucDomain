{-# OPTIONS --safe --without-K #-}

-- The residue of a Gaussian integer modulo gamma as a Boolean bit.
module GauInt.Gamma.Bit where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (module GaussianSolver)
open import GauInt.Gamma using (Evenγ) renaming (gaussianParity to parity)
open import GauInt.Gamma.Congruence using (Cong; parity-congruent)
open import GauInt.Parity using (parity-integer; parity-cases; zero-parity-even; even-parity-zero)
open import Integer.Parity using (parityBit; parityBit-sum; parityBit-neg)
open import Data.Bool using (Bool; false; true; _xor_)
open import Data.Bool.Properties using (xor-same)
open import Data.Nat using (_≟_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; does)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

bit : ZComplex → Bool
bit z = does (parity z ≟ 1)

bit-integer : ∀ z → bit z ≡ parityBit (re z Z.+ im z)
bit-integer z = cong (λ n → does (n ≟ 1)) (parity-integer z)

bit-add : ∀ z w → bit (z + w) ≡ bit z xor bit w
bit-add (Cplx a b) (Cplx c d) = trans (bit-integer (Cplx a b + Cplx c d))
  (trans (cong parityBit (solve 4 (λ a b c d → (a :+ c) :+ (b :+ d) := (a :+ b) :+ (c :+ d)) refl a b c d))
    (trans (parityBit-sum (a Z.+ b) (c Z.+ d))
      (cong₂ _xor_ (sym (bit-integer (Cplx a b))) (sym (bit-integer (Cplx c d))))))
  where open +-*-Solver

bit-neg : ∀ z → bit (- z) ≡ bit z
bit-neg (Cplx a b) = trans (bit-integer (- Cplx a b))
  (trans (cong parityBit (sym (ZP.neg-distrib-+ a b)))
    (trans (parityBit-neg (a Z.+ b)) (sym (bit-integer (Cplx a b)))))

bit-sub : ∀ z w → bit (z - w) ≡ bit z xor bit w
bit-sub z w = trans (bit-add z (- w)) (cong (bit z xor_) (bit-neg w))

bit-false-even : ∀ z → bit z ≡ false → Evenγ z
bit-false-even z h with parity-cases z
... | inj₁ hz = zero-parity-even z hz
... | inj₂ ho = ⊥-elim (bad (trans (sym h) (cong (λ n → does (n ≟ 1)) ho)))
  where bad : false ≡ true → ⊥; bad ()

same-bit-congruent : ∀ a b → bit a ≡ bit b → Cong 1 a b
same-bit-congruent a b h = finish (bit-false-even (a - b)
  (trans (bit-sub a b) (trans (cong (_xor bit b) h) (xor-same (bit b)))))
  where
  open GaussianSolver
  finish : Evenγ (a - b) → Cong 1 a b
  finish (q , hq) = q , trans (solve 2 (λ a b → a := b :+ (a :- b)) refl a b) (cong (b TC.+_) hq)

congruent-same-bit : ∀ a b → Cong 1 a b → bit a ≡ bit b
congruent-same-bit a b h = cong (λ n → does (n ≟ 1)) (parity-congruent 0 a b h)

-- Divisibility by gamma is decidable through the parity.
even? : ∀ z → Dec (Evenγ z)
even? z = map′ (zero-parity-even z) (even-parity-zero z) (parity z ≟ 0)
