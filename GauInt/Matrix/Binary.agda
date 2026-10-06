{-# OPTIONS --safe --without-K #-}

-- The binary residue of a Gaussian matrix modulo gamma; Gram equations at a
-- positive level make its row and column overlaps even.
module GauInt.Matrix.Binary where

open import GauInt.Matrix using (Mat; _≈_; gram; scale; identity)
open import GauInt.Matrix.Gram using (columnGram)
open import GauInt.Matrix.Congruence using (weight)
open import GauInt.Matrix.ResidueArithmetic using (rowOverlap; columnOverlap; gram-even-overlap; gram-even-column-overlap)
open import GauInt.Gamma using () renaming (gaussianParity to parity)
open import GauInt.Gamma.Bit using (bit)
open import GauInt.Parity using (parity-cases)
open import GauInt.TwoPower using (twoPower)
import Finite.BinaryMatrix as B
open import Natural.Sum using (sum-cong)
open import Data.Nat using (suc; _*_; _%_; _≟_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

binary : ∀ {n} → Mat n → B.Binary n
binary M i j = bit (M i j)

bit-correct : ∀ z → B.bitNat (does (parity z ≟ 1)) ≡ parity z
bit-correct z with parity-cases z
... | inj₁ h rewrite h = refl
... | inj₂ h rewrite h = refl

binary-row-overlap : ∀ {n} (M : Mat n) i j → B.overlapCount (binary M) i j ≡ rowOverlap M i j
binary-row-overlap M i j = sum-cong (λ k → cong₂ _*_ (bit-correct (M i k)) (bit-correct (M j k)))

binary-column-overlap : ∀ {n} (M : Mat n) i j → B.overlapCount (B.transpose (binary M)) i j ≡ columnOverlap M i j
binary-column-overlap M i j = sum-cong (λ k → cong₂ _*_ (bit-correct (M k i)) (bit-correct (M k j)))

binary-weight : ∀ {n} (M : Mat n) → B.weight (binary M) ≡ weight M
binary-weight M = sum-cong (λ i → sum-cong (λ j → bit-correct (M i j)))

binary-constraints : ∀ {n} (M : Mat n) k → gram M ≈ scale (twoPower (suc k)) identity →
  columnGram M ≈ scale (twoPower (suc k)) identity → B.Constraints (binary M)
binary-constraints M k hr hc =
  (λ i j → trans (cong (_% 2) (binary-row-overlap M i j)) (gram-even-overlap M k hr i j)) ,
  (λ i j → trans (cong (_% 2) (binary-column-overlap M i j)) (gram-even-column-overlap M k hc i j))
