-- The adjoint of a generalized permutation is its inverse, and
-- multiplying on the left by one is multiplying on the right by its
-- inverse, read through the adjoint.
--
-- Why this is worth a module of its own: multiplying a matrix on the
-- RIGHT by a generalized permutation is a computation that goes through
-- with the permutation data still a variable -- the columns of gp-mat G
-- are unit vectors, and Kopt.Descent's lcomb-unit selects one of the
-- columns of the other factor. Multiplying on the LEFT is not: the
-- result's entry at a given row is the entry of the other factor at the
-- row that the permutation sends there, and finding that row means
-- knowing the permutation. Rather than analyse the 4⁴ possibilities, use
--
--   G·A = (A†·G†)†   with   G† = G⁻¹,
--
-- which needs only the anti-multiplicativity of the adjoint
-- (Kopt.MatAdj) and the unitarity of a generalized permutation
-- (Kopt.GateUnitary). The identity G† = G⁻¹ is uniqueness of inverses:
-- G† is a left inverse of G because G is unitary, gp-mat (gp-inverse G)
-- is a right inverse of it by Kopt.Descent, and in a monoid a left and a
-- right inverse of the same element agree.

{-# OPTIONS --without-K --safe #-}

module Kopt.PermAdj where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Descent
  using (Op ; GP ; gp-mat ; gp-inverse ; gp-inverse-left ; gp-inverse-right
        ; mat-*-assoc ; mat-*-identityˡ ; mat-*-identityʳ)
open import Kopt.Unitary using (IsUnitary ; u-left ; u-right)
open import Kopt.MatAdj using (adjoint-* ; adjoint-invol)
open import Kopt.GateUnitary using (gp-unitary)

-- ----------------------------------------------------------------------
-- * Uniqueness of inverses

-- x·a = 1 and a·y = 1 force x = y: x = x·(a·y) = (x·a)·y = y.
inv-unique : (a x y : Op) -> x * a ≡ 1# -> a * y ≡ 1# -> x ≡ y
inv-unique a x y hx hy = begin
  x              ≡⟨ sym (mat-*-identityʳ x) ⟩
  x * 1#         ≡⟨ cong (λ m -> x * m) (sym hy) ⟩
  x * (a * y)    ≡⟨ sym (mat-*-assoc x a y) ⟩
  (x * a) * y    ≡⟨ cong (λ m -> m * y) hx ⟩
  1# * y         ≡⟨ mat-*-identityˡ y ⟩
  y ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * The adjoint of a generalized permutation

gp-adjoint : (G : GP) -> adjoint (gp-mat G) ≡ gp-mat (gp-inverse G)
gp-adjoint G = inv-unique (gp-mat G) (adjoint (gp-mat G)) (gp-mat (gp-inverse G))
                          (u-left (gp-unitary G)) (gp-inverse-right G)

-- G⁻¹⁻¹ = G, at the level of the matrices (which is all that is used).
gp-inverse-invol : (G : GP) -> gp-mat (gp-inverse (gp-inverse G)) ≡ gp-mat G
gp-inverse-invol G =
  inv-unique (gp-mat (gp-inverse G)) (gp-mat (gp-inverse (gp-inverse G))) (gp-mat G)
             (gp-inverse-left (gp-inverse G)) (gp-inverse-left G)

-- ----------------------------------------------------------------------
-- * Left multiplication as right multiplication by the inverse

-- G·A = (A†·G⁻¹)†. The right-hand side multiplies on the right, which is
-- the case that computes.
gp-mul-left : (G : GP) (A : Op) ->
              gp-mat G * A ≡ adjoint (adjoint A * gp-mat (gp-inverse G))
gp-mul-left G A = begin
  gp-mat G * A
    ≡⟨ cong (λ m -> m * A) (sym (gp-inverse-invol G)) ⟩
  gp-mat (gp-inverse (gp-inverse G)) * A
    ≡⟨ cong (λ m -> m * A) (sym (gp-adjoint (gp-inverse G))) ⟩
  adjoint (gp-mat (gp-inverse G)) * A
    ≡⟨ cong (λ m -> adjoint (gp-mat (gp-inverse G)) * m) (sym (adjoint-invol A)) ⟩
  adjoint (gp-mat (gp-inverse G)) * adjoint (adjoint A)
    ≡⟨ sym (adjoint-* (adjoint A) (gp-mat (gp-inverse G))) ⟩
  adjoint (adjoint A * gp-mat (gp-inverse G)) ∎
  where open ≡-Reasoning
