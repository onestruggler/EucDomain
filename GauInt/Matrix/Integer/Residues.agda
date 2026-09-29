{-# OPTIONS --safe --without-K #-}

-- Unbounded row/column binary constraints derived from integer Gram equations.
module GauInt.Matrix.Integer.Residues where

open import GauInt.Matrix.Integer
open import GauInt.Matrix.Integer.Orthogonality
open import GauInt.TwoPower using (twoPowerInt)
open import Integer.Sum using (intSum; intSum-cong; intSum-mono)
open import Natural.Sum using (sumNat; natSum-cast; natSum-bound)
open import Integer.Congruence
open import Integer.Parity
import Integer.Residues as RA
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; +≤+)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

parity-le-square : ∀ x → + (parity x) Z.≤ x Z.* x
parity-le-square (+ zero) = +≤+ z≤n
parity-le-square (+ suc n) = +≤+ (NP.≤-trans (parity-bound (+ suc n)) (s≤s z≤n))
parity-le-square -[1+ n ] = +≤+ (NP.≤-trans (parity-bound -[1+ n ]) (s≤s z≤n))

rowWeight : ∀ {n} → IntMat n → Fin n → ℕ
rowWeight M i = sumNat (λ j → parity (M i j))

rowOverlap : ∀ {n} → IntMat n → Fin n → Fin n → ℕ
rowOverlap M i j = sumNat (λ k → parity (M i k) * parity (M j k))

intIdentity-diagonal : ∀ {n} (i : Fin n) → intIdentity i i ≡ + 1
intIdentity-diagonal zero = refl
intIdentity-diagonal (suc i) = intIdentity-diagonal i

row-norm : ∀ {n} (M : IntMat n) k → intOrthogonal M k → ∀ i → intSum (λ j → M i j Z.* M i j) ≡ twoPowerInt k
row-norm M k h i = trans (h i i)
  (trans (cong (λ x → twoPowerInt k Z.* x) (intIdentity-diagonal i)) (ZP.*-identityʳ (twoPowerInt k)))

rowWeight-bound : ∀ {n} (M : IntMat n) i → rowWeight M i ≤ n
rowWeight-bound M i = natSum-bound (λ j → parity (M i j)) (λ j → parity-bound (M i j))

rowWeight-le-norm : ∀ {n} (M : IntMat n) k → intOrthogonal M k → ∀ i → + (rowWeight M i) Z.≤ twoPowerInt k
rowWeight-le-norm M k h i = subst (λ x → x Z.≤ twoPowerInt k) (sym (natSum-cast (λ j → parity (M i j))))
  (subst (λ x → intSum (λ j → + (parity (M i j))) Z.≤ x) (row-norm M k h i)
    (intSum-mono (λ j → + (parity (M i j))) (λ j → M i j Z.* M i j) (λ j → parity-le-square (M i j))))

rowWeight-congruence : ∀ {n} (M : IntMat n) k → intOrthogonal M k → ∀ i → Cong (+ 4) (+ (rowWeight M i)) (twoPowerInt k)
rowWeight-congruence M k h i = subst (λ y → Cong (+ 4) (+ (rowWeight M i)) y) (row-norm M k h i)
  (subst (λ x → Cong (+ 4) x (intSum (λ j → M i j Z.* M i j))) (sym (natSum-cast (λ j → parity (M i j))))
    (cong-sym (+ 4) (intSum (λ j → M i j Z.* M i j)) (intSum (λ j → + (parity (M i j))))
      (cong-sum (+ 4) (λ j → M i j Z.* M i j) (λ j → + (parity (M i j))) (λ j → square-congruence (M i j)))))

power-four : ∀ k → Cong (+ 4) (twoPowerInt (suc (suc k))) (+ 0)
power-four k = twoPowerInt k , solve 1 (λ x → con (+ 2) :* (con (+ 2) :* x) := con (+ 0) :+ con (+ 4) :* x) refl (twoPowerInt k)

rowWeight-high : ∀ (M : IntMat 6) k → intOrthogonal M (suc (suc k)) → ∀ i → rowWeight M i ≡ 0 ⊎ rowWeight M i ≡ 4
rowWeight-high M k h i = RA.weight-high (rowWeight M i) (rowWeight-bound M i)
  (cong-trans (+ 4) (+ (rowWeight M i)) (twoPowerInt (suc (suc k))) (+ 0)
    (rowWeight-congruence M (suc (suc k)) h i) (power-four k))

rowWeight-one : ∀ (M : IntMat 6) → intOrthogonal M 1 → ∀ i → rowWeight M i ≡ 2
rowWeight-one M h i = RA.weight-one (rowWeight M i)
  (ZP.drop‿+≤+ (rowWeight-le-norm M 1 h i)) (rowWeight-congruence M 1 h i)

power-two : ∀ k z → Cong (+ 2) (twoPowerInt (suc k) Z.* z) (+ 0)
power-two k z = twoPowerInt k Z.* z , solve 2 (λ x z → (con (+ 2) :* x) :* z := con (+ 0) :+ con (+ 2) :* (x :* z)) refl (twoPowerInt k) z

rowOverlap-even : ∀ {n} (M : IntMat n) k → intOrthogonal M (suc k) → ∀ i j → rowOverlap M i j Data.Nat.% 2 ≡ 0
rowOverlap-even M k h i j = RA.multiple2-natural (rowOverlap M i j)
  (cong-trans (+ 2) (+ (rowOverlap M i j)) (twoPowerInt (suc k) Z.* intIdentity i j) (+ 0) hc (power-two k (intIdentity i j)))
  where
  cast-product : intSum (λ l → + (parity (M i l)) Z.* + (parity (M j l))) ≡ + (rowOverlap M i j)
  cast-product = trans
    (intSum-cong (λ l → + (parity (M i l)) Z.* + (parity (M j l))) (λ l → + (parity (M i l) * parity (M j l)))
      (λ l → sym (ZP.pos-* (parity (M i l)) (parity (M j l)))))
    (sym (natSum-cast (λ l → parity (M i l) * parity (M j l))))
  original = intSum (λ l → M i l Z.* M j l)
  reduced = intSum (λ l → + (parity (M i l)) Z.* + (parity (M j l)))
  reduced-congruence : Cong (+ 2) original reduced
  reduced-congruence = cong-sum (+ 2) (λ l → M i l Z.* M j l)
    (λ l → + (parity (M i l)) Z.* + (parity (M j l)))
    (λ l → cong-mul (+ 2) (M i l) (+ (parity (M i l))) (M j l) (+ (parity (M j l)))
      (parity-congruence (M i l)) (parity-congruence (M j l)))
  hc : Cong (+ 2) (+ (rowOverlap M i j)) (twoPowerInt (suc k) Z.* intIdentity i j)
  hc = subst (λ x → Cong (+ 2) x (twoPowerInt (suc k) Z.* intIdentity i j)) cast-product
    (subst (Cong (+ 2) reduced) (h i j) (cong-sym (+ 2) original reduced reduced-congruence))
