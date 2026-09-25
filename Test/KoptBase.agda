-- Checks of Kopt.Base (γ, lde, residues) against the paper and the
-- authors' data file (Kopt/Haskell/experiment_data.dat).

{-# OPTIONS --without-K --safe #-}

module Test.KoptBase where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (_∷_ ; [])
open import Data.Product.Base using (_,_)
open import Function.Base using (_∋_)
open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base

-- γ² = 2i, and γ γ† = 2.
_ : (ZComplex ∋ γ ^2) ≡ 2 * i
_ = refl
_ : (ZComplex ∋ γ * γ†) ≡ 2
_ = refl
_ : (DComplex ∋ γ * 1/γ) ≡ 1
_ = refl

-- Parity: 1 + 2i is odd, 1 + 3i is even (paper, after Definition II.4).
_ : parity (ZComplex ∋ 1 + 2 * i) ≡ Odd
_ = refl
_ : parity (ZComplex ∋ 1 + 3 * i) ≡ Even
_ = refl

-- The ρ₃ table of Section II B.
_ : ρ 3 1 ≡ Odd ∷ Even ∷ Even ∷ []
_ = refl
_ : ρ 3 (- 1) ≡ Odd ∷ Even ∷ Odd ∷ []
_ = refl
_ : ρ 3 i ≡ Odd ∷ Odd ∷ Odd ∷ []
_ = refl
_ : ρ 3 (- i) ≡ Odd ∷ Odd ∷ Even ∷ []
_ = refl
_ : ρ 3 0 ≡ Even ∷ Even ∷ Even ∷ []
_ = refl
_ : ρ 3 (1 + i) ≡ Even ∷ Odd ∷ Even ∷ []
_ = refl
_ : ρ 3 (1 - i) ≡ Even ∷ Odd ∷ Odd ∷ []
_ = refl
_ : ρ 3 2 ≡ Even ∷ Even ∷ Odd ∷ []
_ = refl

-- lde of scalars: lde (1/γᵏ) = k.
_ : lde (DComplex ∋ 1) ≡ 0
_ = refl
_ : lde (DComplex ∋ 1/γ) ≡ 1
_ = refl
_ : lde (DComplex ∋ 1/γ ^ 5) ≡ 5
_ = refl
_ : lde (DComplex ∋ half) ≡ 2
_ = refl

-- The first record of experiment_data.dat has lde 2 and integral
-- matrix M; the operator is U = M/γ².
U1 : Matrix 4 4 DComplex
U1 = matrix-map (λ x -> from-whole x * 1/γ ^ 2) M
  where
    M : Matrix 4 4 ZComplex
    M = matrix4x4 (2 * i , 0 , 0 , 0)
                  (0 , 1 + i , 0 , 1 + i)
                  (0 , - i , 1 - i , i)
                  (0 , i , 1 - i , - i)

_ : lde U1 ≡ 2
_ = refl
