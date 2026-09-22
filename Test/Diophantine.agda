-- Tests for Quantum.Synthesis.Diophantine, checked by evaluation (small
-- cases only; see Test.DiophantineRun for the compiled tests). The
-- expected values were computed with the Haskell newsynth reference
-- implementation.
--
-- Note: do not use "with" on a step computation of this module in
-- type-checked code (e.g. "f x with run (diophantine g x)"): the
-- with-abstraction normalizes the computation, which explodes. Use a
-- helper function that pattern matches instead.

{-# OPTIONS --without-K --safe --guardedness #-}

module Test.Diophantine where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.EuclideanDomain
open import Quantum.Synthesis.StepComp
open import Quantum.Synthesis.Random
open import Quantum.Synthesis.Diophantine

_ : power-mod 3 100 7 ≡ 4
_ = refl

_ : power-mod 12345 6789 1000003 ≡ 644220
_ = refl

_ : power-mod 2 0 5 ≡ 1
_ = refl

_ : relatively-prime-factors (ℤ ∋ 12) 18 ≡ (1 , (3 , 3) ∷ (2 , 3) ∷ [])
_ = refl

_ : relatively-prime-factors (ℤ ∋ 360) 84 ≡ (1 , (7 , 1) ∷ (5 , 1) ∷ (2 , 5) ∷ (3 , 3) ∷ [])
_ = refl

_ : relatively-prime-factors (ZRootTwo ∋ 7) (RootTwo 3 1) ≡ (1 , (RootTwo 3 1 , 2) ∷ (RootTwo 3 -1 , 1) ∷ [])
_ = refl

g : StdGen
g = mkStdGen 1

_ : run-with-steps (root-of-negative-one g 13) ≡ just (5 , 2)
_ = refl

_ : run-with-steps (root-mod g 17 2) ≡ just (6 , 1)
_ = refl

_ : run-with-steps (find-factor g 91) ≡ just (13 , 2)
_ = refl

_ : run-with-steps (diophantine g 13) ≡ just (just (Omega 0 -3 0 -2) , 1)
_ = refl

_ : run-with-steps (diophantine g (RootTwo 2 1)) ≡ just (just (Omega 0 0 1 1) , 1)
_ = refl

-- 3 + √2 is a prime of norm 7 ≡ 7 (mod 8): no solution.
_ : run-with-steps (diophantine g (RootTwo 3 1)) ≡ just (nothing , 0)
_ = refl

-- 1 - √2 < 0: no solution.
_ : run-with-steps (diophantine g (RootTwo 1 -1)) ≡ just (nothing , 0)
_ = refl

_ : run-with-steps (diophantine g 7) ≡ just (nothing , 2)
_ = refl
