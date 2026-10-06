{-# OPTIONS --safe --without-K #-}
-- Generated finite caches; each equality below is checked by the kernel.
module GauInt.Gamma.Residue.Tables where
import GauInt.Gamma.Residue as R
open import GauInt.Gamma.Residue using (Code; decode)
open import GauInt.Gamma using () renaming (gaussianParity to parity)
open import GauInt.Gamma.Congruence using (quotient)
open import Finite.Check using (checkFin; decAll)
open import Data.Nat using (ℕ)
import Data.Nat as N
open import Data.Fin using (Fin; #_; toℕ; _≟_)
open import Data.Vec.Base using (Vec; lookup; []; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

addTable multiplyTable : Vec (Vec Code 8) 8
addTable = (((# 0) ∷ (# 1) ∷ (# 2) ∷ (# 3) ∷ (# 4) ∷ (# 5) ∷ (# 6) ∷ (# 7) ∷ []) ∷ ((# 1) ∷ (# 4) ∷ (# 3) ∷ (# 6) ∷ (# 5) ∷ (# 0) ∷ (# 7) ∷ (# 2) ∷ []) ∷ ((# 2) ∷ (# 3) ∷ (# 0) ∷ (# 1) ∷ (# 6) ∷ (# 7) ∷ (# 4) ∷ (# 5) ∷ []) ∷ ((# 3) ∷ (# 6) ∷ (# 1) ∷ (# 4) ∷ (# 7) ∷ (# 2) ∷ (# 5) ∷ (# 0) ∷ []) ∷ ((# 4) ∷ (# 5) ∷ (# 6) ∷ (# 7) ∷ (# 0) ∷ (# 1) ∷ (# 2) ∷ (# 3) ∷ []) ∷ ((# 5) ∷ (# 0) ∷ (# 7) ∷ (# 2) ∷ (# 1) ∷ (# 4) ∷ (# 3) ∷ (# 6) ∷ []) ∷ ((# 6) ∷ (# 7) ∷ (# 4) ∷ (# 5) ∷ (# 2) ∷ (# 3) ∷ (# 0) ∷ (# 1) ∷ []) ∷ ((# 7) ∷ (# 2) ∷ (# 5) ∷ (# 0) ∷ (# 3) ∷ (# 6) ∷ (# 1) ∷ (# 4) ∷ []) ∷ [])
multiplyTable = (((# 0) ∷ (# 0) ∷ (# 0) ∷ (# 0) ∷ (# 0) ∷ (# 0) ∷ (# 0) ∷ (# 0) ∷ []) ∷ ((# 0) ∷ (# 1) ∷ (# 2) ∷ (# 3) ∷ (# 4) ∷ (# 5) ∷ (# 6) ∷ (# 7) ∷ []) ∷ ((# 0) ∷ (# 2) ∷ (# 4) ∷ (# 6) ∷ (# 0) ∷ (# 2) ∷ (# 4) ∷ (# 6) ∷ []) ∷ ((# 0) ∷ (# 3) ∷ (# 6) ∷ (# 5) ∷ (# 4) ∷ (# 7) ∷ (# 2) ∷ (# 1) ∷ []) ∷ ((# 0) ∷ (# 4) ∷ (# 0) ∷ (# 4) ∷ (# 0) ∷ (# 4) ∷ (# 0) ∷ (# 4) ∷ []) ∷ ((# 0) ∷ (# 5) ∷ (# 2) ∷ (# 7) ∷ (# 4) ∷ (# 1) ∷ (# 6) ∷ (# 3) ∷ []) ∷ ((# 0) ∷ (# 6) ∷ (# 4) ∷ (# 2) ∷ (# 0) ∷ (# 6) ∷ (# 4) ∷ (# 2) ∷ []) ∷ ((# 0) ∷ (# 7) ∷ (# 6) ∷ (# 1) ∷ (# 4) ∷ (# 3) ∷ (# 2) ∷ (# 5) ∷ []) ∷ [])
conjugateTable : Vec Code 8
conjugateTable = ((# 0) ∷ (# 1) ∷ (# 6) ∷ (# 7) ∷ (# 4) ∷ (# 5) ∷ (# 2) ∷ (# 3) ∷ [])
bitTable : Vec (Vec ℕ 8) 3
bitTable = ((0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ []) ∷ [])

add multiply : Code → Code → Code
add a b = lookup (lookup addTable a) b
multiply a b = lookup (lookup multiplyTable a) b
star : Code → Code
star = lookup conjugateTable
bit : Fin 3 → Code → ℕ
bit d c = lookup (lookup bitTable d) c

abstract
  add-correct : ∀ a b → add a b ≡ R.addCode a b
  add-correct = checkFin 8 _ (λ a → decAll 8 _ (λ b → add a b ≟ R.addCode a b)) tt
  multiply-correct : ∀ a b → multiply a b ≡ R.multiplyCode a b
  multiply-correct = checkFin 8 _ (λ a → decAll 8 _ (λ b → multiply a b ≟ R.multiplyCode a b)) tt
  star-correct : ∀ a → star a ≡ R.conjugateCode a
  star-correct = checkFin 8 _ (λ a → star a ≟ R.conjugateCode a) tt
  bit-correct : ∀ d c → bit d c ≡ parity (quotient (toℕ d) (decode c))
  bit-correct = checkFin 3 _ (λ d → decAll 8 _ (λ c → bit d c N.≟ parity (quotient (toℕ d) (decode c)))) tt
