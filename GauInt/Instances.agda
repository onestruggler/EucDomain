-- Instances of Gaussian integers.

{-# OPTIONS --without-K --safe  #-}

module GauInt.Instances where

open import Data.Integer using (+_ ; -[1+_] ; +[1+_])
open import Data.Nat using (suc )

open import Instances
open import GauInt.Base renaming (-_ to -𝔾_ ; _-_ to _-𝔾_ ; _+_ to _+𝔾_ ; _*_ to _*𝔾_ ; NonZero to NonZero𝔾 ; rank to rank𝔾)

-- Instances to overload operations.
instance
  sr𝔾 : SemiRing 𝔾
  _+_ {{sr𝔾}} = _+𝔾_
  _*_ {{sr𝔾}} = _*𝔾_
  0# {{sr𝔾}} = 0𝔾
  1# {{sr𝔾}} = 1𝔾

instance
  ring𝔾 : Ring 𝔾 
  ring𝔾 .sra = sr𝔾
  ring𝔾 .-_ = -𝔾_

instance
  Rank𝔾 : Rank 𝔾
  Rank𝔾 .rank = rank𝔾

-- This depends on how the boolean equality on 𝔾 is defined. To be
-- precise, it depends on the order of comparing the components.
instance
  nzp : ∀ {n} {y} -> NonZero𝔾 (+ suc n + y i)
  nzp = _

  nzn : ∀ {n} {y} -> NonZero𝔾 (-[1+ n ] + y i)
  nzn = _

  nzpi : ∀ {n} -> NonZero𝔾 (0# + (+ suc n) i)
  nzpi = _

  nzni : ∀ {n} -> NonZero𝔾 (0# + (-[1+ n ]) i)
  nzni = _

instance
  NZT𝔾 : NonZeroTypeclass 𝔾
  NZT𝔾 .NonZero = NonZero𝔾 


{-

-- Translation from NonZero predicate to non-equality.
test-t : ∀ (x : 𝔾) -> .{{NonZero x}} -> ¬ x ≡ 0#
test-t (+_ zero + +[1+ n ] i) = λ {()}
test-t (+_ zero + -[1+_] n i) = λ {()}
test-t (+[1+ n ] + x₁ i) = λ {()}
test-t (-[1+_] n + x₁ i) = λ {()}


open import Relation.Binary.Structures 
open IsDecEquivalence {{...}}
open IsDecTotalOrder {{...}}
open import Data.Nat.Instances
open import Data.Integer.Instances
test : {!!} 
test = 0ℤ ≤? 0ℤ

-}
