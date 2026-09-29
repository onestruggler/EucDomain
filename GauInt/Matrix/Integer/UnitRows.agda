{-# OPTIONS --safe --without-K #-}

-- An integer matrix with orthonormal rows has entries in {0, 1, -1}.
module GauInt.Matrix.Integer.UnitRows where

open import GauInt.Matrix.Integer using (IntMat)
open import GauInt.Matrix.Integer.Orthogonality using (intOrthogonal)
open import GauInt.Matrix.Integer.Residues using (row-norm)
open import Integer.Sum using (term-le-sum)
open import Integer.Squares using (square-nonnegative; small-square)
open import Data.Integer using (+_; -[1+_])
import Data.Integer as Z
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

unit-entry-small : ∀ {n} (M : IntMat n) → intOrthogonal M 0 → ∀ i j →
  (M i j ≡ + 0) ⊎ (M i j ≡ + 1) ⊎ (M i j ≡ -[1+ 0 ])
unit-entry-small M h i j = small-square (M i j)
  (subst (λ x → M i j Z.* M i j Z.≤ x) (row-norm M 0 h i)
    (term-le-sum (λ k → M i k Z.* M i k) (λ k → square-nonnegative (M i k)) j))
