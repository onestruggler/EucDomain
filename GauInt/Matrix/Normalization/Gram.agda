{-# OPTIONS --safe --without-K #-}

-- Row and column Gram equations transport along γ-presentation equivalence,
-- in particular through normalization.
module GauInt.Matrix.Normalization.Gram where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_*_)
open import GauInt.Gamma using (powγ)
open import GauInt.Matrix
open import GauInt.Matrix.Gram using (gram-cong; gram-scale; columnGram; columnGram-cong; columnGram-scale)
open import GauInt.Matrix.Presentation using (ScaledMatrix; scaled; numerator; exponent; Equivalent; equivalent-sym; multiple-equivalent)
open import GauInt.TwoPower using (twoPower; twoPower-cancel; powγ-norm)
open import GauInt.Algebra.Swap using (swap)
open import Data.Nat using (_+_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

gram-equivalent : ∀ {n} (A B : ScaledMatrix n) → Equivalent A B →
  gram (numerator B) ≈ scale (twoPower (exponent B)) identity →
  gram (numerator A) ≈ scale (twoPower (exponent A)) identity
gram-equivalent A B h hB i j = twoPower-cancel (exponent B)
  (trans (sym (cong (_* gram (numerator A) i j) (powγ-norm (exponent B))))
    (trans (sym (gram-scale (powγ (exponent B)) (numerator A) i j))
      (trans (gram-cong {M = scale (powγ (exponent B)) (numerator A)}
        {N = scale (powγ (exponent A)) (numerator B)} h i j)
        (trans (gram-scale (powγ (exponent A)) (numerator B) i j)
          (trans (cong (_* gram (numerator B) i j) (powγ-norm (exponent A)))
            (trans (cong (twoPower (exponent A) *_) (hB i j))
              (swap (twoPower (exponent A)) (twoPower (exponent B)) (identity i j))))))))

columnGram-equivalent : ∀ {n} (A B : ScaledMatrix n) → Equivalent A B →
  columnGram (numerator B) ≈ scale (twoPower (exponent B)) identity →
  columnGram (numerator A) ≈ scale (twoPower (exponent A)) identity
columnGram-equivalent A B h hB i j = twoPower-cancel (exponent B)
  (trans (sym (cong (_* columnGram (numerator A) i j) (powγ-norm (exponent B))))
    (trans (sym (columnGram-scale (powγ (exponent B)) (numerator A) i j))
      (trans (columnGram-cong {M = scale (powγ (exponent B)) (numerator A)}
        {N = scale (powγ (exponent A)) (numerator B)} h i j)
        (trans (columnGram-scale (powγ (exponent A)) (numerator B) i j)
          (trans (cong (_* columnGram (numerator B) i j) (powγ-norm (exponent A)))
            (trans (cong (twoPower (exponent A) *_) (hB i j))
              (swap (twoPower (exponent A)) (twoPower (exponent B)) (identity i j))))))))

-- Numerator form: M = γ^d·N moves both Gram equations from level d + k
-- (for M) to level k (for N).
gram-multiple : ∀ {n} (M N : Mat n) d k l → l ≡ d + k → M ≈ scale (powγ d) N →
  gram M ≈ scale (twoPower l) identity → gram N ≈ scale (twoPower k) identity
gram-multiple M N d k l hl h = gram-equivalent (scaled N k) (scaled M l)
  (equivalent-sym {A = scaled M l} {B = scaled N k}
    (multiple-equivalent {M = M} {N = N} {k = l} {l = k} d (trans hl (NP.+-comm d k)) h))

columnGram-multiple : ∀ {n} (M N : Mat n) d k l → l ≡ d + k → M ≈ scale (powγ d) N →
  columnGram M ≈ scale (twoPower l) identity → columnGram N ≈ scale (twoPower k) identity
columnGram-multiple M N d k l hl h = columnGram-equivalent (scaled N k) (scaled M l)
  (equivalent-sym {A = scaled M l} {B = scaled N k}
    (multiple-equivalent {M = M} {N = N} {k = l} {l = k} d (trans hl (NP.+-comm d k)) h))
