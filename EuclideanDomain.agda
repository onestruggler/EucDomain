-- This file defines the Euclidean Domain structure.

{-# OPTIONS --without-K --safe #-}

module EuclideanDomain where
-- We comply to the definition format in stdlib, i.e. define an
-- IsSomething predicate then define the bundle.

  open import Relation.Binary using (Rel; Setoid; IsEquivalence)

  module Structures 
    {a ℓ} {A : Set a}  -- The underlying set
    (_≈_ : Rel A ℓ)    -- The underlying equality relation
    where

    open import Algebra.Structures _≈_
    open import Algebra.Core
    open import Algebra.Definitions _≈_
    import Algebra.Consequences.Setoid as Consequences
    open import Data.Product using (_,_; proj₁; proj₂)
    open import Level using (_⊔_)

    open import Data.Nat using (ℕ ; _<_)
    open import Data.Product using (∃ ; _×_)
    open import Relation.Nullary using (¬_)

    -- We only require leftcancellative since we have required the
    -- domain to be commutative. An Euclidean domain is a commutative
    -- domain with a div, mod, and rank function satisfy euc-eq and
    -- euc-rank.
    record IsEuclideanDomain
             (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
      field
        isCommutativeRing : IsCommutativeRing + * - 0# 1#
        *-alc : AlmostLeftCancellative 0# *
        div : ∀ (n d : A) -> ¬ d ≈ 0# -> A
        mod : ∀ (n d : A) -> ¬ d ≈ 0# -> A
        rank : A → ℕ
        euc-eq : ∀ (n d : A) -> (n0 : ¬ d ≈ 0#) ->
                   let r = mod n d n0 in let q = div n d n0 in 
                   n ≈ + r (* q d) 
        euc-rank : ∀ (n d : A) -> (n0 : ¬ d ≈ 0#) ->
                   let r = mod n d n0 in let q = div n d n0 in 
                   rank r < rank d

  module Bundles where

    open Structures
    open import Algebra.Core
    open import Algebra.Structures
    open import Relation.Binary
    open import Function.Base
    import Relation.Nullary as N
    open import Level

    record EuclideanDomainBundle c ℓ : Set (suc (c ⊔ ℓ)) where
      infix  8 -_
      infixl 7 _*_
      infixl 6 _+_
      infix  4 _≈_
      field
        Carrier           : Set c
        _≈_               : Rel Carrier ℓ
        _+_               : Op₂ Carrier
        _*_               : Op₂ Carrier
        -_                : Op₁ Carrier
        0#                : Carrier
        1#                : Carrier
        isEuclideanDomain : IsEuclideanDomain _≈_ _+_ _*_ -_ 0# 1#

      open IsEuclideanDomain isEuclideanDomain public

