-- The adjoint of a product of 4×4 matrices, and unitarity of products,
-- for
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026).
--
-- The paper's operators are unitaries, and the algorithm multiplies
-- them by gates and by generalized permutations; to know that what it
-- reaches is still unitary one needs (X·Y)† = Y†·X†, which the library
-- does not prove. That is this module.
--
-- Performance: the proofs are stated for an ABSTRACT commutative ring
-- with an involutive adjoint and instantiated at 𝔻[i] afterwards, for
-- the reason recorded in Kopt.Unitary: over an abstract ring the
-- conversion checker compares the four-term sums of a matrix product
-- structurally, while over 𝔻[i] it would unfold each product into the
-- dyadic arithmetic. The matrix arguments are variables throughout, so
-- the concrete-matrix trap of the top-level README does not apply. The
-- 𝔻[i] instances are `abstract`, so that a caller multiplying concrete
-- matrices never unfolds them.

{-# OPTIONS --without-K --safe #-}

module Kopt.MatAdj where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Descent using (Op ; vec4-≡ ; mat4-≡ ; mat-*-assoc ; mat-*-identityˡ)
open import Kopt.Unitary using (sum4 ; IsUnitary ; is-unitary ; u-left ; u-right)

-- ----------------------------------------------------------------------
-- * The generic part

module Generic {A : Set} {{RA : Ring A}} {{_ : Adjoint A}}
               (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
               (F : IsInvolutiveRingEndo {A} adj) where
  private
    module R = IsCommutativeRing isCR
    module E = IsInvolutiveRingEndo F

    -- (Σₖ yₖ·xₖ)† = Σₖ (xₖ)†·(yₖ)†. This is the (r,c) entry of the
    -- statement below: the entries of X·Y are four-term sums in which
    -- the factor from the right matrix comes first (Kopt.Unitary.sum4),
    -- and taking the adjoint both conjugates and swaps the two factors.
    adj-ip : (y₀ x₀ y₁ x₁ y₂ x₂ y₃ x₃ : A) ->
             adj (sum4 (y₀ * x₀) (y₁ * x₁) (y₂ * x₂) (y₃ * x₃))
               ≡ sum4 (adj x₀ * adj y₀) (adj x₁ * adj y₁) (adj x₂ * adj y₂) (adj x₃ * adj y₃)
    adj-ip y₀ x₀ y₁ x₁ y₂ x₂ y₃ x₃ =
      trans (E.f-+ (y₀ * x₀) ((y₁ * x₁) + ((y₂ * x₂) + (y₃ * x₃))))
            (cong₂ (λ u v -> u + v) (tm y₀ x₀)
              (trans (E.f-+ (y₁ * x₁) ((y₂ * x₂) + (y₃ * x₃)))
                (cong₂ (λ u v -> u + v) (tm y₁ x₁)
                  (trans (E.f-+ (y₂ * x₂) (y₃ * x₃))
                    (cong₂ (λ u v -> u + v) (tm y₂ x₂) (tm y₃ x₃))))))
      where
        tm : (y x : A) -> adj (y * x) ≡ adj x * adj y
        tm y x = trans (E.f-* y x) (R.*-comm (adj y) (adj x))

  -- (X·Y)† = Y†·X†. The sixteen entry equations are the sixteen
  -- instances of adj-ip; xᵣ꜀ is the entry of X in row r and column c.
  adjoint-*′ : (X Y : Matrix 4 4 A) -> adjoint (X * Y) ≡ adjoint Y * adjoint X
  adjoint-*′ (Matrix' ((x00 ∷ x10 ∷ x20 ∷ x30 ∷ []) ∷ (x01 ∷ x11 ∷ x21 ∷ x31 ∷ [])
                     ∷ (x02 ∷ x12 ∷ x22 ∷ x32 ∷ []) ∷ (x03 ∷ x13 ∷ x23 ∷ x33 ∷ []) ∷ []))
             (Matrix' ((y00 ∷ y10 ∷ y20 ∷ y30 ∷ []) ∷ (y01 ∷ y11 ∷ y21 ∷ y31 ∷ [])
                     ∷ (y02 ∷ y12 ∷ y22 ∷ y32 ∷ []) ∷ (y03 ∷ y13 ∷ y23 ∷ y33 ∷ []) ∷ [])) =
    mat4-≡ (vec4-≡ (adj-ip y00 x00 y10 x01 y20 x02 y30 x03)
                   (adj-ip y01 x00 y11 x01 y21 x02 y31 x03)
                   (adj-ip y02 x00 y12 x01 y22 x02 y32 x03)
                   (adj-ip y03 x00 y13 x01 y23 x02 y33 x03))
           (vec4-≡ (adj-ip y00 x10 y10 x11 y20 x12 y30 x13)
                   (adj-ip y01 x10 y11 x11 y21 x12 y31 x13)
                   (adj-ip y02 x10 y12 x11 y22 x12 y32 x13)
                   (adj-ip y03 x10 y13 x11 y23 x12 y33 x13))
           (vec4-≡ (adj-ip y00 x20 y10 x21 y20 x22 y30 x23)
                   (adj-ip y01 x20 y11 x21 y21 x22 y31 x23)
                   (adj-ip y02 x20 y12 x21 y22 x22 y32 x23)
                   (adj-ip y03 x20 y13 x21 y23 x22 y33 x23))
           (vec4-≡ (adj-ip y00 x30 y10 x31 y20 x32 y30 x33)
                   (adj-ip y01 x30 y11 x31 y21 x32 y31 x33)
                   (adj-ip y02 x30 y12 x31 y22 x32 y32 x33)
                   (adj-ip y03 x30 y13 x31 y23 x32 y33 x33))

  -- (X†)† = X.
  adjoint-invol′ : (X : Matrix 4 4 A) -> adjoint (adjoint X) ≡ X
  adjoint-invol′ (Matrix' ((x00 ∷ x10 ∷ x20 ∷ x30 ∷ []) ∷ (x01 ∷ x11 ∷ x21 ∷ x31 ∷ [])
                         ∷ (x02 ∷ x12 ∷ x22 ∷ x32 ∷ []) ∷ (x03 ∷ x13 ∷ x23 ∷ x33 ∷ []) ∷ [])) =
    mat4-≡ (vec4-≡ (E.involutive x00) (E.involutive x10) (E.involutive x20) (E.involutive x30))
           (vec4-≡ (E.involutive x01) (E.involutive x11) (E.involutive x21) (E.involutive x31))
           (vec4-≡ (E.involutive x02) (E.involutive x12) (E.involutive x22) (E.involutive x32))
           (vec4-≡ (E.involutive x03) (E.involutive x13) (E.involutive x23) (E.involutive x33))

-- ----------------------------------------------------------------------
-- * At 𝔻[i]

private
  module G = Generic isCommutativeRing-DComplex adj-DComplex

abstract
  adjoint-* : (X Y : Op) -> adjoint (X * Y) ≡ adjoint Y * adjoint X
  adjoint-* = G.adjoint-*′

  adjoint-invol : (X : Op) -> adjoint (adjoint X) ≡ X
  adjoint-invol = G.adjoint-invol′

-- ----------------------------------------------------------------------
-- * Unitarity is closed under products and adjoints

unitary-* : {X Y : Op} -> IsUnitary X -> IsUnitary Y -> IsUnitary (X * Y)
unitary-* {X} {Y} hx hy = is-unitary left right
  where
    open ≡-Reasoning
    left : adjoint (X * Y) * (X * Y) ≡ 1#
    left = begin
      adjoint (X * Y) * (X * Y)
        ≡⟨ cong (λ z -> z * (X * Y)) (adjoint-* X Y) ⟩
      (adjoint Y * adjoint X) * (X * Y)
        ≡⟨ mat-*-assoc (adjoint Y) (adjoint X) (X * Y) ⟩
      adjoint Y * (adjoint X * (X * Y))
        ≡⟨ cong (λ z -> adjoint Y * z) (sym (mat-*-assoc (adjoint X) X Y)) ⟩
      adjoint Y * ((adjoint X * X) * Y)
        ≡⟨ cong (λ z -> adjoint Y * (z * Y)) (u-left hx) ⟩
      adjoint Y * (1# * Y)
        ≡⟨ cong (λ z -> adjoint Y * z) (mat-*-identityˡ Y) ⟩
      adjoint Y * Y
        ≡⟨ u-left hy ⟩
      1# ∎

    right : (X * Y) * adjoint (X * Y) ≡ 1#
    right = begin
      (X * Y) * adjoint (X * Y)
        ≡⟨ cong (λ z -> (X * Y) * z) (adjoint-* X Y) ⟩
      (X * Y) * (adjoint Y * adjoint X)
        ≡⟨ mat-*-assoc X Y (adjoint Y * adjoint X) ⟩
      X * (Y * (adjoint Y * adjoint X))
        ≡⟨ cong (λ z -> X * z) (sym (mat-*-assoc Y (adjoint Y) (adjoint X))) ⟩
      X * ((Y * adjoint Y) * adjoint X)
        ≡⟨ cong (λ z -> X * (z * adjoint X)) (u-right hy) ⟩
      X * (1# * adjoint X)
        ≡⟨ cong (λ z -> X * z) (mat-*-identityˡ (adjoint X)) ⟩
      X * adjoint X
        ≡⟨ u-right hx ⟩
      1# ∎

unitary-adj : {X : Op} -> IsUnitary X -> IsUnitary (adjoint X)
unitary-adj {X} hx = is-unitary left right
  where
    left : adjoint (adjoint X) * adjoint X ≡ 1#
    left = trans (cong (λ z -> z * adjoint X) (adjoint-invol X)) (u-right hx)

    right : adjoint X * adjoint (adjoint X) ≡ 1#
    right = trans (cong (λ z -> adjoint X * z) (adjoint-invol X)) (u-left hx)
