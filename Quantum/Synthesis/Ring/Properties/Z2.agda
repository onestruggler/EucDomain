-- The integers modulo 2 form a commutative ring.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Z2 where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Quantum.Synthesis.Ring using (Z2 ; Even ; Odd ; SemiRingZ2 ; RingZ2)
open import Quantum.Synthesis.Ring.Properties.Common using (isCommutativeRing-from-laws)

+-assoc-Z2 : ∀ (x y z : Z2) -> (x + y) + z ≡ x + (y + z)
+-assoc-Z2 Even y z = refl
+-assoc-Z2 Odd Even z = refl
+-assoc-Z2 Odd Odd Even = refl
+-assoc-Z2 Odd Odd Odd = refl

+-comm-Z2 : ∀ (x y : Z2) -> x + y ≡ y + x
+-comm-Z2 Even Even = refl
+-comm-Z2 Even Odd = refl
+-comm-Z2 Odd Even = refl
+-comm-Z2 Odd Odd = refl

+-identityˡ-Z2 : ∀ (x : Z2) -> 0# + x ≡ x
+-identityˡ-Z2 x = refl

-‿inverseˡ-Z2 : ∀ (x : Z2) -> (- x) + x ≡ 0#
-‿inverseˡ-Z2 Even = refl
-‿inverseˡ-Z2 Odd = refl

*-assoc-Z2 : ∀ (x y z : Z2) -> (x * y) * z ≡ x * (y * z)
*-assoc-Z2 Even y z = refl
*-assoc-Z2 Odd y z = refl

*-comm-Z2 : ∀ (x y : Z2) -> x * y ≡ y * x
*-comm-Z2 Even Even = refl
*-comm-Z2 Even Odd = refl
*-comm-Z2 Odd Even = refl
*-comm-Z2 Odd Odd = refl

*-identityˡ-Z2 : ∀ (x : Z2) -> 1# * x ≡ x
*-identityˡ-Z2 x = refl

distribʳ-Z2 : ∀ (x y z : Z2) -> (y + z) * x ≡ y * x + z * x
distribʳ-Z2 Even Even z = refl
distribʳ-Z2 Even Odd Even = refl
distribʳ-Z2 Even Odd Odd = refl
distribʳ-Z2 Odd Even z = refl
distribʳ-Z2 Odd Odd Even = refl
distribʳ-Z2 Odd Odd Odd = refl

isCommutativeRing-Z2 : IsCommutativeRing (_≡_ {A = Z2}) _+_ _*_ -_ 0# 1#
isCommutativeRing-Z2 = isCommutativeRing-from-laws _ _ _ _ _ record
  { +-assoc = +-assoc-Z2
  ; +-comm = +-comm-Z2
  ; +-identityˡ = +-identityˡ-Z2
  ; -‿inverseˡ = -‿inverseˡ-Z2
  ; *-assoc = *-assoc-Z2
  ; *-comm = *-comm-Z2
  ; *-identityˡ = *-identityˡ-Z2
  ; distribʳ = distribʳ-Z2
  }

commutativeRing-Z2 : CommutativeRing 0ℓ 0ℓ
commutativeRing-Z2 = record { isCommutativeRing = isCommutativeRing-Z2 }
