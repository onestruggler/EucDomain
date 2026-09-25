-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the definitions of the optimality theory -- Definition V.1 (the
-- optimal gate counts kc, cs, len) and Definition V.2 (lde-descents).
-- The results proved about these definitions are in Kopt.Optimality.
--
-- Contents:
--
--  * matrix algebra: 4×4 matrices over a commutative ring form a
--    monoid under multiplication. This is what the semantics of a
--    circuit needs: ⟦C ++ D⟧ = ⟦C⟧·⟦D⟧.
--  * the lde of a matrix: it is the maximum of the ldes of the
--    entries, and it is subadditive (Lemma II.8 for matrices).
--  * generalized permutations, intrinsically: a matrix whose columns
--    are i^k·e_r with distinct r (Section III C). They form a group,
--    they all have lde 0, and multiplying by one does not change the
--    lde.
--  * Definition V.1: the minimal counts are not computable, so
--    "n is a K-count of A" is a relation HasKCount, and being the
--    minimal one is the predicate IsMinimalKCount.
--  * Definition V.2: a descent is a list of steps, each of which
--    multiplies by a generalized permutation or by K₁, on the left or
--    on the right; with sub-descents, exteriors, n-descents, the
--    K-count of a descent, and K-optimality.

{-# OPTIONS --without-K --safe #-}

module Kopt.Descent where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
import Data.List.Properties as ListP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Base using (_∋_)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Patterns using (SixCases ; I ; II ; III ; IV ; IVt ; V ; VI ; patof ; DecEqSixCases)
open import Kopt.Properties.LdeLemmas using (lemma-II-8 ; lde-+ ; lde-i ; max-≤ˡ ; max-≤ʳ ; max-lub)

-- ----------------------------------------------------------------------
-- * Matrix algebra
--
-- The library's matrix multiplication computes the columns of A·B as
-- linear combinations of the columns of A, using local helper
-- functions. We repeat them here (lcomb is the uniform version of the
-- library's mmv, which stops one step earlier) and prove that the two
-- agree on 4×4 matrices.

module _ {A : Set} {{_ : Ring A}} where

  -- x·v, entrywise.
  smul : {n : ℕ} -> A -> Vector n A -> Vector n A
  smul x v = vector-map (x *_) v

  -- v + w, entrywise.
  vadd : {n : ℕ} -> Vector n A -> Vector n A -> Vector n A
  vadd = vector-zipwith _+_

  -- The linear combination Σⱼ wⱼ·aⱼ of the vectors aⱼ.
  lcomb : {m n : ℕ} -> Vector n (Vector m A) -> Vector n A -> Vector m A
  lcomb [] [] = vector-repeat 0#
  lcomb (a ∷ as) (w ∷ ws) = vadd (smul w a) (lcomb as ws)

  -- Matrix multiplication, in the same column form as the library's.
  mmul : {m n p : ℕ} -> Matrix m n A -> Matrix n p A -> Matrix m p A
  mmul (Matrix' a) (Matrix' b) = Matrix' (vector-map (lcomb a) b)

-- Equality of 4-vectors and of 4×4 matrices, entry by entry.
vec4-≡ : {A : Set} {a b c d a' b' c' d' : A} ->
         a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
         (Vector 4 A ∋ (a ∷ b ∷ c ∷ d ∷ [])) ≡ (a' ∷ b' ∷ c' ∷ d' ∷ [])
vec4-≡ refl refl refl refl = refl

mat4-≡ : {A : Set} {a b c d a' b' c' d' : Vector 4 A} ->
         a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
         Matrix' {4} {4} (a ∷ b ∷ c ∷ d ∷ []) ≡ Matrix' (a' ∷ b' ∷ c' ∷ d' ∷ [])
mat4-≡ refl refl refl refl = refl

-- ----------------------------------------------------------------------
-- ** The vector lemmas

module VecLemmas {A : Set} {{_ : Ring A}}
                 (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  private
    module R = IsCommutativeRing isCR

    -- (x+y)+(z+w) = (x+z)+(y+w). (The same rearrangement is in
    -- Kopt.Properties.Lde, in the module CRLemmas; it is repeated
    -- here to keep the dependencies of this module small.)
    +-interchange : (x y z w : A) -> (x + y) + (z + w) ≡ (x + z) + (y + w)
    +-interchange x y z w = trans (R.+-assoc x y (z + w))
      (trans (cong (λ u -> x + u) (+-swapˡ y z w)) (sym (R.+-assoc x z (y + w))))
      where
        +-swapˡ : (p q r : A) -> p + (q + r) ≡ q + (p + r)
        +-swapˡ p q r = trans (sym (R.+-assoc p q r))
                              (trans (cong (λ u -> u + r) (R.+-comm p q)) (R.+-assoc q p r))

  zero-vec : {n : ℕ} -> Vector n A
  zero-vec = vector-repeat 0#

  vadd-0ˡ : {n : ℕ} (v : Vector n A) -> vadd zero-vec v ≡ v
  vadd-0ˡ [] = refl
  vadd-0ˡ (x ∷ xs) = cong₂ _∷_ (R.+-identityˡ x) (vadd-0ˡ xs)

  vadd-0ʳ : {n : ℕ} (v : Vector n A) -> vadd v zero-vec ≡ v
  vadd-0ʳ [] = refl
  vadd-0ʳ (x ∷ xs) = cong₂ _∷_ (R.+-identityʳ x) (vadd-0ʳ xs)

  vadd-interchange : {n : ℕ} (a b c d : Vector n A) ->
                     vadd (vadd a b) (vadd c d) ≡ vadd (vadd a c) (vadd b d)
  vadd-interchange [] [] [] [] = refl
  vadd-interchange (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) =
    cong₂ _∷_ (+-interchange a b c d) (vadd-interchange as bs cs ds)

  smul-1 : {n : ℕ} (v : Vector n A) -> smul 1# v ≡ v
  smul-1 [] = refl
  smul-1 (x ∷ xs) = cong₂ _∷_ (R.*-identityˡ x) (smul-1 xs)

  smul-0ˡ : {n : ℕ} (v : Vector n A) -> smul 0# v ≡ zero-vec
  smul-0ˡ [] = refl
  smul-0ˡ (x ∷ xs) = cong₂ _∷_ (R.zeroˡ x) (smul-0ˡ xs)

  smul-0ʳ : {n : ℕ} (x : A) -> smul x (zero-vec {n}) ≡ zero-vec
  smul-0ʳ {zero} x = refl
  smul-0ʳ {suc n} x = cong₂ _∷_ (R.zeroʳ x) (smul-0ʳ {n} x)

  smul-+ : {n : ℕ} (x y : A) (v : Vector n A) -> smul (x + y) v ≡ vadd (smul x v) (smul y v)
  smul-+ x y [] = refl
  smul-+ x y (z ∷ zs) = cong₂ _∷_ (R.distribʳ z x y) (smul-+ x y zs)

  smul-vadd : {n : ℕ} (x : A) (v w : Vector n A) -> smul x (vadd v w) ≡ vadd (smul x v) (smul x w)
  smul-vadd x [] [] = refl
  smul-vadd x (a ∷ as) (b ∷ bs) = cong₂ _∷_ (R.distribˡ x a b) (smul-vadd x as bs)

  smul-* : {n : ℕ} (x y : A) (v : Vector n A) -> smul (x * y) v ≡ smul x (smul y v)
  smul-* x y [] = refl
  smul-* x y (z ∷ zs) = cong₂ _∷_ (R.*-assoc x y z) (smul-* x y zs)

  -- Σⱼ 0·aⱼ = 0.
  lcomb-0 : {m n : ℕ} (a : Vector n (Vector m A)) -> lcomb a zero-vec ≡ zero-vec
  lcomb-0 [] = refl
  lcomb-0 (h ∷ t) = trans (cong₂ vadd (smul-0ˡ h) (lcomb-0 t)) (vadd-0ˡ zero-vec)

  -- Linearity of the linear combination in its coefficients.
  lcomb-vadd : {m n : ℕ} (a : Vector n (Vector m A)) (v w : Vector n A) ->
               lcomb a (vadd v w) ≡ vadd (lcomb a v) (lcomb a w)
  lcomb-vadd [] [] [] = sym (vadd-0ˡ zero-vec)
  lcomb-vadd (h ∷ t) (v ∷ vs) (w ∷ ws) =
    trans (cong₂ vadd (smul-+ v w h) (lcomb-vadd t vs ws))
          (vadd-interchange (smul v h) (smul w h) (lcomb t vs) (lcomb t ws))

  lcomb-smul : {m n : ℕ} (a : Vector n (Vector m A)) (x : A) (v : Vector n A) ->
               lcomb a (smul x v) ≡ smul x (lcomb a v)
  lcomb-smul [] x [] = sym (smul-0ʳ x)
  lcomb-smul (h ∷ t) x (v ∷ vs) =
    trans (cong₂ vadd (smul-* x v h) (lcomb-smul t x vs))
          (sym (smul-vadd x (smul v h) (lcomb t vs)))

  -- The associativity of matrix multiplication, in column form.
  lcomb-lcomb : {m n p : ℕ} (a : Vector n (Vector m A)) (b : Vector p (Vector n A)) (w : Vector p A) ->
                lcomb (vector-map (lcomb a) b) w ≡ lcomb a (lcomb b w)
  lcomb-lcomb a [] [] = sym (lcomb-0 a)
  lcomb-lcomb a (b ∷ bs) (w ∷ ws) = begin
    vadd (smul w (lcomb a b)) (lcomb (vector-map (lcomb a) bs) ws)
      ≡⟨ cong (λ z -> vadd (smul w (lcomb a b)) z) (lcomb-lcomb a bs ws) ⟩
    vadd (smul w (lcomb a b)) (lcomb a (lcomb bs ws))
      ≡⟨ cong (λ z -> vadd z (lcomb a (lcomb bs ws))) (sym (lcomb-smul a w b)) ⟩
    vadd (lcomb a (smul w b)) (lcomb a (lcomb bs ws))
      ≡⟨ sym (lcomb-vadd a (smul w b) (lcomb bs ws)) ⟩
    lcomb a (vadd (smul w b) (lcomb bs ws)) ∎
    where open ≡-Reasoning

  -- mmul is associative.
  mmul-assoc : {m n p q : ℕ} (x : Matrix m n A) (y : Matrix n p A) (z : Matrix p q A) ->
               mmul (mmul x y) z ≡ mmul x (mmul y z)
  mmul-assoc (Matrix' a) (Matrix' b) (Matrix' c) = cong Matrix' (go c)
    where
      go : {q : ℕ} (c : Vector q (Vector _ A)) ->
           vector-map (lcomb (vector-map (lcomb a) b)) c ≡ vector-map (lcomb a) (vector-map (lcomb b) c)
      go [] = refl
      go (w ∷ ws) = cong₂ _∷_ (lcomb-lcomb a b w) (go ws)

  -- ** Picking one summand out of a four-term sum

  private
    zero3 : (r s : A) -> r ≡ 0# -> s ≡ 0# -> r + (s + 0#) ≡ 0#
    zero3 r s hr hs =
      trans (cong₂ _+_ hr (trans (cong (λ u -> u + 0#) hs) (R.+-identityˡ 0#))) (R.+-identityˡ 0#)

    zero4 : (q r s : A) -> q ≡ 0# -> r ≡ 0# -> s ≡ 0# -> q + (r + (s + 0#)) ≡ 0#
    zero4 q r s hq hr hs = trans (cong₂ _+_ hq (zero3 r s hr hs)) (R.+-identityˡ 0#)

  pick0 : (p q r s : A) -> q ≡ 0# -> r ≡ 0# -> s ≡ 0# -> p + (q + (r + (s + 0#))) ≡ p
  pick0 p q r s hq hr hs =
    trans (cong (λ u -> p + u) (zero4 q r s hq hr hs)) (R.+-identityʳ p)

  pick1 : (p q r s : A) -> p ≡ 0# -> r ≡ 0# -> s ≡ 0# -> p + (q + (r + (s + 0#))) ≡ q
  pick1 p q r s hp hr hs =
    trans (cong₂ _+_ hp (trans (cong (λ u -> q + u) (zero3 r s hr hs)) (R.+-identityʳ q)))
          (R.+-identityˡ q)

  pick2 : (p q r s : A) -> p ≡ 0# -> q ≡ 0# -> s ≡ 0# -> p + (q + (r + (s + 0#))) ≡ r
  pick2 p q r s hp hq hs =
    trans (cong₂ _+_ hp
            (trans (cong₂ _+_ hq
                     (trans (cong (λ u -> r + u) (trans (R.+-identityʳ s) hs)) (R.+-identityʳ r)))
                   (R.+-identityˡ r)))
          (R.+-identityˡ r)

  pick3 : (p q r s : A) -> p ≡ 0# -> q ≡ 0# -> r ≡ 0# -> p + (q + (r + (s + 0#))) ≡ s
  pick3 p q r s hp hq hr =
    trans (cong₂ _+_ hp (trans (cong₂ _+_ hq (trans (cong₂ _+_ hr (R.+-identityʳ s))
                                                    (R.+-identityˡ s)))
                               (R.+-identityˡ s)))
          (R.+-identityˡ s)

-- ----------------------------------------------------------------------
-- ** The 4×4 matrices form a monoid

module Mat4 {A : Set} {{_ : Ring A}}
            (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  private
    module R = IsCommutativeRing isCR
  open VecLemmas isCR public

  -- The library's multiplication agrees with mmul.
  mmul-≡′ : (x y : Matrix 4 4 A) -> x * y ≡ mmul x y
  mmul-≡′ (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []))
         (Matrix' ((x₀ ∷ y₀ ∷ z₀ ∷ w₀ ∷ []) ∷ (x₁ ∷ y₁ ∷ z₁ ∷ w₁ ∷ []) ∷
                   (x₂ ∷ y₂ ∷ z₂ ∷ w₂ ∷ []) ∷ (x₃ ∷ y₃ ∷ z₃ ∷ w₃ ∷ []) ∷ [])) =
    mat4-≡ (go x₀ y₀ z₀ w₀) (go x₁ y₁ z₁ w₁) (go x₂ y₂ z₂ w₂) (go x₃ y₃ z₃ w₃)
    where
      go : (x y z w : A) ->
           vadd (smul x a₀) (vadd (smul y a₁) (vadd (smul z a₂) (smul w a₃)))
             ≡ lcomb (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (x ∷ y ∷ z ∷ w ∷ [])
      go x y z w =
        cong (λ v -> vadd (smul x a₀) (vadd (smul y a₁) (vadd (smul z a₂) v)))
             (sym (vadd-0ʳ (smul w a₃)))

  -- Multiplication of 4×4 matrices is associative.
  mat-*-assoc′ : (x y z : Matrix 4 4 A) -> (x * y) * z ≡ x * (y * z)
  mat-*-assoc′ x y z = begin
    (x * y) * z        ≡⟨ mmul-≡′ (x * y) z ⟩
    mmul (x * y) z     ≡⟨ cong (λ u -> mmul u z) (mmul-≡′ x y) ⟩
    mmul (mmul x y) z  ≡⟨ mmul-assoc x y z ⟩
    mmul x (mmul y z)  ≡⟨ cong (λ u -> mmul x u) (sym (mmul-≡′ y z)) ⟩
    mmul x (y * z)     ≡⟨ sym (mmul-≡′ x (y * z)) ⟩
    x * (y * z)        ∎
    where open ≡-Reasoning

  private
    one-cols : Vector 4 (Vector 4 A)
    one-cols = unMatrix (1# {A = Matrix 4 4 A})

    mmul-idˡ : (x : Matrix 4 4 A) -> mmul 1# x ≡ x
    mmul-idˡ (Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) = mat4-≡ (col c₀) (col c₁) (col c₂) (col c₃)
      where
        col : (v : Vector 4 A) -> lcomb one-cols v ≡ v
        col (x ∷ y ∷ z ∷ w ∷ []) =
          vec4-≡ (trans (pick0 (x * 1#) (y * 0#) (z * 0#) (w * 0#)
                               (R.zeroʳ y) (R.zeroʳ z) (R.zeroʳ w)) (R.*-identityʳ x))
                 (trans (pick1 (x * 0#) (y * 1#) (z * 0#) (w * 0#)
                               (R.zeroʳ x) (R.zeroʳ z) (R.zeroʳ w)) (R.*-identityʳ y))
                 (trans (pick2 (x * 0#) (y * 0#) (z * 1#) (w * 0#)
                               (R.zeroʳ x) (R.zeroʳ y) (R.zeroʳ w)) (R.*-identityʳ z))
                 (trans (pick3 (x * 0#) (y * 0#) (z * 0#) (w * 1#)
                               (R.zeroʳ x) (R.zeroʳ y) (R.zeroʳ z)) (R.*-identityʳ w))

    mmul-idʳ : (x : Matrix 4 4 A) -> mmul x 1# ≡ x
    mmul-idʳ (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = mat4-≡ (c0 a₀ a₁ a₂ a₃) (c1 a₀ a₁ a₂ a₃)
                                                         (c2 a₀ a₁ a₂ a₃) (c3 a₀ a₁ a₂ a₃)
      where
        c0 : (b₀ b₁ b₂ b₃ : Vector 4 A) ->
             vadd (smul 1# b₀) (vadd (smul 0# b₁) (vadd (smul 0# b₂) (vadd (smul 0# b₃) zero-vec))) ≡ b₀
        c0 b₀ b₁ b₂ b₃ =
          trans (cong₂ vadd (smul-1 b₀)
                (trans (cong₂ vadd (smul-0ˡ b₁)
                       (trans (cong₂ vadd (smul-0ˡ b₂)
                              (trans (cong (λ u -> vadd u zero-vec) (smul-0ˡ b₃)) (vadd-0ʳ zero-vec)))
                              (vadd-0ˡ zero-vec)))
                       (vadd-0ˡ zero-vec)))
                (vadd-0ʳ b₀)
        c1 : (b₀ b₁ b₂ b₃ : Vector 4 A) ->
             vadd (smul 0# b₀) (vadd (smul 1# b₁) (vadd (smul 0# b₂) (vadd (smul 0# b₃) zero-vec))) ≡ b₁
        c1 b₀ b₁ b₂ b₃ =
          trans (cong₂ vadd (smul-0ˡ b₀)
                (trans (cong₂ vadd (smul-1 b₁)
                       (trans (cong₂ vadd (smul-0ˡ b₂)
                              (trans (cong (λ u -> vadd u zero-vec) (smul-0ˡ b₃)) (vadd-0ʳ zero-vec)))
                              (vadd-0ˡ zero-vec)))
                       (vadd-0ʳ b₁)))
                (vadd-0ˡ b₁)
        c2 : (b₀ b₁ b₂ b₃ : Vector 4 A) ->
             vadd (smul 0# b₀) (vadd (smul 0# b₁) (vadd (smul 1# b₂) (vadd (smul 0# b₃) zero-vec))) ≡ b₂
        c2 b₀ b₁ b₂ b₃ =
          trans (cong₂ vadd (smul-0ˡ b₀)
                (trans (cong₂ vadd (smul-0ˡ b₁)
                       (trans (cong₂ vadd (smul-1 b₂)
                              (trans (cong (λ u -> vadd u zero-vec) (smul-0ˡ b₃)) (vadd-0ʳ zero-vec)))
                              (vadd-0ʳ b₂)))
                       (vadd-0ˡ b₂)))
                (vadd-0ˡ b₂)
        c3 : (b₀ b₁ b₂ b₃ : Vector 4 A) ->
             vadd (smul 0# b₀) (vadd (smul 0# b₁) (vadd (smul 0# b₂) (vadd (smul 1# b₃) zero-vec))) ≡ b₃
        c3 b₀ b₁ b₂ b₃ =
          trans (cong₂ vadd (smul-0ˡ b₀)
                (trans (cong₂ vadd (smul-0ˡ b₁)
                       (trans (cong₂ vadd (smul-0ˡ b₂)
                              (trans (cong (λ u -> vadd u zero-vec) (smul-1 b₃)) (vadd-0ʳ b₃)))
                              (vadd-0ˡ b₃)))
                       (vadd-0ˡ b₃)))
                (vadd-0ˡ b₃)

  mat-*-identityˡ′ : (x : Matrix 4 4 A) -> 1# * x ≡ x
  mat-*-identityˡ′ x = trans (mmul-≡′ 1# x) (mmul-idˡ x)

  mat-*-identityʳ′ : (x : Matrix 4 4 A) -> x * 1# ≡ x
  mat-*-identityʳ′ x = trans (mmul-≡′ x 1#) (mmul-idʳ x)

  -- The interface is abstract: unfolding these proofs on concrete
  -- matrices makes the type checker normalise 4×4 products of dyadic
  -- complex numbers, which is very slow.
  abstract
    mmul-≡ : (x y : Matrix 4 4 A) -> x * y ≡ mmul x y
    mmul-≡ = mmul-≡′

    mat-*-assoc : (x y z : Matrix 4 4 A) -> (x * y) * z ≡ x * (y * z)
    mat-*-assoc = mat-*-assoc′

    mat-*-identityˡ : (x : Matrix 4 4 A) -> 1# * x ≡ x
    mat-*-identityˡ = mat-*-identityˡ′

    mat-*-identityʳ : (x : Matrix 4 4 A) -> x * 1# ≡ x
    mat-*-identityʳ = mat-*-identityʳ′

-- The instance we use: 4×4 matrices over 𝔻[i].
module M4 = Mat4 isCommutativeRing-DComplex
open M4 public using (mat-*-assoc ; mat-*-identityˡ ; mat-*-identityʳ ; mmul-≡)

Op : Set
Op = Matrix 4 4 DComplex

-- ----------------------------------------------------------------------
-- ** The semantics of a circuit is multiplicative

-- ⟦C ++ D⟧ = ⟦C⟧·⟦D⟧ (Definition I.1).
⟦⟧-++ : (c d : Circuit) -> ⟦ c ++ d ⟧ ≡ ⟦ c ⟧ * ⟦ d ⟧
⟦⟧-++ [] d = sym (mat-*-identityˡ ⟦ d ⟧)
⟦⟧-++ (g ∷ c) d =
  trans (cong (λ m -> ⟦ g ⟧g * m) (⟦⟧-++ c d)) (sym (mat-*-assoc ⟦ g ⟧g ⟦ c ⟧ ⟦ d ⟧))

-- ----------------------------------------------------------------------
-- * The lde of a matrix
--
-- lde (Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) = max (lde c₀) (max (lde c₁)
-- (max (lde c₂) (max (lde c₃) 0))), and the same for the entries of a
-- column, so the following two lemmas give both the upper and the
-- lower bounds we need.

lde-4-≤ : {T : Set} {{_ : LamDenomExp T}} {n : ℕ} (x y z w : T) ->
          lde x Nat.≤ n -> lde y Nat.≤ n -> lde z Nat.≤ n -> lde w Nat.≤ n ->
          lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ [])) Nat.≤ n
lde-4-≤ x y z w hx hy hz hw =
  max-lub hx (max-lub hy (max-lub hz (max-lub hw z≤n)))

module _ {T : Set} {{_ : LamDenomExp T}} (x y z w : T) where
  private
    M : ℕ
    M = lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ []))

  lde-4-0 : lde x Nat.≤ M
  lde-4-0 = max-≤ˡ (lde x) _

  lde-4-1 : lde y Nat.≤ M
  lde-4-1 = NatP.≤-trans (max-≤ˡ (lde y) _) (max-≤ʳ (lde x) _)

  lde-4-2 : lde z Nat.≤ M
  lde-4-2 = NatP.≤-trans (NatP.≤-trans (max-≤ˡ (lde z) _) (max-≤ʳ (lde y) _)) (max-≤ʳ (lde x) _)

  lde-4-3 : lde w Nat.≤ M
  lde-4-3 = NatP.≤-trans (NatP.≤-trans (NatP.≤-trans (max-≤ˡ (lde w) _) (max-≤ʳ (lde z) _))
                                       (max-≤ʳ (lde y) _))
                         (max-≤ʳ (lde x) _)

-- ----------------------------------------------------------------------
-- * Generalized permutations (Section III C)

-- The four coordinates.
data Pos : Set where
  p0 p1 p2 p3 : Pos

-- The four powers of i.
data Phase : Set where
  ph0 ph1 ph2 ph3 : Phase

phase-val : Phase -> DComplex
phase-val ph0 = 1#
phase-val ph1 = i
phase-val ph2 = - 1#
phase-val ph3 = - i

-- Addition of the exponents.
infixl 7 _·p_
_·p_ : Phase -> Phase -> Phase
ph0 ·p y = y
ph1 ·p ph0 = ph1
ph1 ·p ph1 = ph2
ph1 ·p ph2 = ph3
ph1 ·p ph3 = ph0
ph2 ·p ph0 = ph2
ph2 ·p ph1 = ph3
ph2 ·p ph2 = ph0
ph2 ·p ph3 = ph1
ph3 ·p ph0 = ph3
ph3 ·p ph1 = ph0
ph3 ·p ph2 = ph1
ph3 ·p ph3 = ph2

phase-inv : Phase -> Phase
phase-inv ph0 = ph0
phase-inv ph1 = ph3
phase-inv ph2 = ph2
phase-inv ph3 = ph1

phase-inv-law : (c : Phase) -> c ·p phase-inv c ≡ ph0
phase-inv-law ph0 = refl
phase-inv-law ph1 = refl
phase-inv-law ph2 = refl
phase-inv-law ph3 = refl

phase-mul : (a b : Phase) -> phase-val a * phase-val b ≡ phase-val (a ·p b)
phase-mul ph0 ph0 = refl
phase-mul ph0 ph1 = refl
phase-mul ph0 ph2 = refl
phase-mul ph0 ph3 = refl
phase-mul ph1 ph0 = refl
phase-mul ph1 ph1 = refl
phase-mul ph1 ph2 = refl
phase-mul ph1 ph3 = refl
phase-mul ph2 ph0 = refl
phase-mul ph2 ph1 = refl
phase-mul ph2 ph2 = refl
phase-mul ph2 ph3 = refl
phase-mul ph3 ph0 = refl
phase-mul ph3 ph1 = refl
phase-mul ph3 ph2 = refl
phase-mul ph3 ph3 = refl

-- The lde of a power of i is 0.
lde-phase : (c : Phase) -> lde (phase-val c) ≡ 0
lde-phase ph0 = refl
lde-phase ph1 = refl
lde-phase ph2 = refl
lde-phase ph3 = refl

-- The column i^k·e_r.
unit-vec : Pos -> Phase -> Vector 4 DComplex
unit-vec p0 c = phase-val c ∷ 0# ∷ 0# ∷ 0# ∷ []
unit-vec p1 c = 0# ∷ phase-val c ∷ 0# ∷ 0# ∷ []
unit-vec p2 c = 0# ∷ 0# ∷ phase-val c ∷ 0# ∷ []
unit-vec p3 c = 0# ∷ 0# ∷ 0# ∷ phase-val c ∷ []

-- ----------------------------------------------------------------------
-- ** Permutations of the four coordinates

Pos4 : Set
Pos4 = Pos × Pos × Pos × Pos

Phase4 : Set
Phase4 = Phase × Phase × Phase × Phase

selp : Pos4 -> Pos -> Pos
selp (a , b , c , d) p0 = a
selp (a , b , c , d) p1 = b
selp (a , b , c , d) p2 = c
selp (a , b , c , d) p3 = d

selph : Phase4 -> Pos -> Phase
selph (a , b , c , d) p0 = a
selph (a , b , c , d) p1 = b
selph (a , b , c , d) p2 = c
selph (a , b , c , d) p3 = d

infix 4 _==p_
_==p_ : Pos -> Pos -> Bool
p0 ==p p0 = true
p1 ==p p1 = true
p2 ==p p2 = true
p3 ==p p3 = true
_ ==p _ = false

==p-sound : {x y : Pos} -> (x ==p y) ≡ true -> x ≡ y
==p-sound {p0} {p0} _ = refl
==p-sound {p1} {p1} _ = refl
==p-sound {p2} {p2} _ = refl
==p-sound {p3} {p3} _ = refl

-- Is the tuple a permutation of the four coordinates?
distinct4p : Pos4 -> Bool
distinct4p (a , b , c , d) =
  not (a ==p b) ∧ not (a ==p c) ∧ not (a ==p d) ∧
  not (b ==p c) ∧ not (b ==p d) ∧ not (c ==p d)

-- The identity permutation, composition, and the inverse.
id4p : Pos4
id4p = p0 , p1 , p2 , p3

comp4p : Pos4 -> Pos4 -> Pos4
comp4p f s = selp f (selp s p0) , selp f (selp s p1) , selp f (selp s p2) , selp f (selp s p3)

inv4p : Pos4 -> Pos4
inv4p t = idx p0 , idx p1 , idx p2 , idx p3
  where
    idx : Pos -> Pos
    idx j = if selp t p0 ==p j then p0 else
            if selp t p1 ==p j then p1 else
            if selp t p2 ==p j then p2 else p3

selp-comp : (f s : Pos4) (x : Pos) -> selp (comp4p f s) x ≡ selp f (selp s x)
selp-comp f s p0 = refl
selp-comp f s p1 = refl
selp-comp f s p2 = refl
selp-comp f s p3 = refl

eq4p : Pos4 -> Pos4 -> Bool
eq4p (a , b , c , d) (a' , b' , c' , d') = (a ==p a') ∧ (b ==p b') ∧ (c ==p c') ∧ (d ==p d')

eq4p-sound : {t s : Pos4} -> eq4p t s ≡ true -> t ≡ s
eq4p-sound {a , b , c , d} {a' , b' , c' , d'} e
  with a ==p a' in ea | b ==p b' in eb | c ==p c' in ec | d ==p d' in ed
... | true | true | true | true =
      cong₂ _,_ (==p-sound ea) (cong₂ _,_ (==p-sound eb) (cong₂ _,_ (==p-sound ec) (==p-sound ed)))

-- ----------------------------------------------------------------------
-- ** Finite enumerations and exhaustive checks
--
-- A boolean check over an explicit finite list, together with the
-- membership of the element in question, is a proof of the
-- corresponding statement. This is how the finite verifications of
-- the paper ("by enumeration") are done here.

infix 4 _∈ˡ_
data _∈ˡ_ {A : Set} (x : A) : List A -> Set where
  here : {xs : List A} -> x ∈ˡ (x ∷ xs)
  there : {y : A} {xs : List A} -> x ∈ˡ xs -> x ∈ˡ (y ∷ xs)

all-of : {A : Set} -> (A -> Bool) -> List A -> Bool
all-of f [] = true
all-of f (x ∷ xs) = f x ∧ all-of f xs

∧-true : {a b : Bool} -> a ∧ b ≡ true -> a ≡ true × b ≡ true
∧-true {true} {true} _ = refl , refl

∧-true₃ : {a b c : Bool} -> a ∧ b ∧ c ≡ true -> (a ≡ true) × (b ≡ true) × (c ≡ true)
∧-true₃ {true} {true} {true} _ = refl , refl , refl

∧-true₅ : {a b c d e : Bool} -> a ∧ b ∧ c ∧ d ∧ e ≡ true ->
          (a ≡ true) × (b ≡ true) × (c ≡ true) × (d ≡ true) × (e ≡ true)
∧-true₅ {true} {true} {true} {true} {true} _ = refl , refl , refl , refl , refl

-- The point of the enumerations: an exhaustive check applies to every
-- element of the list.
all-of-∈ : {A : Set} (f : A -> Bool) (xs : List A) -> all-of f xs ≡ true ->
           {x : A} -> x ∈ˡ xs -> f x ≡ true
all-of-∈ f (y ∷ xs) e here = proj₁ (∧-true e)
all-of-∈ f (y ∷ xs) e (there m) = all-of-∈ f xs (proj₂ (∧-true e)) m

∈-map : {A B : Set} (f : A -> B) {x : A} {xs : List A} -> x ∈ˡ xs -> f x ∈ˡ List.map f xs
∈-map f here = here
∈-map f (there m) = there (∈-map f m)

∈-++ʳ : {A : Set} {x : A} (ys : List A) {xs : List A} -> x ∈ˡ xs -> x ∈ˡ (ys ++ xs)
∈-++ʳ [] m = m
∈-++ʳ (y ∷ ys) m = there (∈-++ʳ ys m)

∈-++ˡ : {A : Set} {x : A} {ys : List A} (xs : List A) -> x ∈ˡ ys -> x ∈ˡ (ys ++ xs)
∈-++ˡ xs here = here
∈-++ˡ xs (there m) = there (∈-++ˡ xs m)

-- The list of all pairs.
pairs : {A B : Set} -> List A -> List B -> List (A × B)
pairs xs ys = List.concatMap (λ x -> List.map (λ y -> (x , y)) ys) xs

∈-pairs : {A B : Set} {x : A} {y : B} {xs : List A} {ys : List B} ->
          x ∈ˡ xs -> y ∈ˡ ys -> (x , y) ∈ˡ pairs xs ys
∈-pairs {ys = ys} (here {xs = xs}) my = ∈-++ˡ _ (∈-map _ my)
∈-pairs (there mx) my = ∈-++ʳ _ (∈-pairs mx my)

-- The sublist of the elements passing a boolean test.
filt : {A : Set} -> (A -> Bool) -> List A -> List A
filt f [] = []
filt f (x ∷ xs) = if f x then x ∷ filt f xs else filt f xs

private
  ∈-filt-cons : {A : Set} (f : A -> Bool) (y : A) (xs : List A) {x : A} ->
                x ∈ˡ filt f xs -> x ∈ˡ filt f (y ∷ xs)
  ∈-filt-cons f y xs m with f y
  ... | true = there m
  ... | false = m

∈-filt : {A : Set} (f : A -> Bool) {x : A} {xs : List A} ->
         x ∈ˡ xs -> f x ≡ true -> x ∈ˡ filt f xs
∈-filt f {x} (here {xs = xs}) e =
  subst (λ b -> x ∈ˡ (if b then x ∷ filt f xs else filt f xs)) (sym e) here
∈-filt f {x} (there {y = y} {xs = xs} m) e = ∈-filt-cons f y xs (∈-filt f m e)

all-pos : List Pos
all-pos = p0 ∷ p1 ∷ p2 ∷ p3 ∷ []

∈-all-pos : (x : Pos) -> x ∈ˡ all-pos
∈-all-pos p0 = here
∈-all-pos p1 = there here
∈-all-pos p2 = there (there here)
∈-all-pos p3 = there (there (there here))

all-phase : List Phase
all-phase = ph0 ∷ ph1 ∷ ph2 ∷ ph3 ∷ []

∈-all-phase : (x : Phase) -> x ∈ˡ all-phase
∈-all-phase ph0 = here
∈-all-phase ph1 = there here
∈-all-phase ph2 = there (there here)
∈-all-phase ph3 = there (there (there here))

all-pos4 : List Pos4
all-pos4 = pairs all-pos (pairs all-pos (pairs all-pos all-pos))

∈-all-pos4 : (t : Pos4) -> t ∈ˡ all-pos4
∈-all-pos4 (a , b , c , d) =
  ∈-pairs (∈-all-pos a) (∈-pairs (∈-all-pos b) (∈-pairs (∈-all-pos c) (∈-all-pos d)))

all-phase4 : List Phase4
all-phase4 = pairs all-phase (pairs all-phase (pairs all-phase all-phase))

∈-all-phase4 : (e : Phase4) -> e ∈ˡ all-phase4
∈-all-phase4 (a , b , c , d) =
  ∈-pairs (∈-all-phase a) (∈-pairs (∈-all-phase b) (∈-pairs (∈-all-phase c) (∈-all-phase d)))

-- The 24 permutations of the four coordinates.
all-perm4 : List Pos4
all-perm4 = filt distinct4p all-pos4

∈-all-perm4 : (t : Pos4) -> distinct4p t ≡ true -> t ∈ˡ all-perm4
∈-all-perm4 t e = ∈-filt distinct4p (∈-all-pos4 t) e

-- ----------------------------------------------------------------------
-- ** The permutation group of the four coordinates, by enumeration

private
  -- Composing two permutations gives a permutation, and composition
  -- of the tuples is composition of the maps.
  comp-check : (ts : Pos4 × Pos4) -> Bool
  comp-check (t , s) = if distinct4p t ∧ distinct4p s then distinct4p (comp4p t s) else true

  comp-ok : all-of comp-check (pairs all-perm4 all-perm4) ≡ true
  comp-ok = refl

  inv-check : (t : Pos4) -> Bool
  inv-check t = distinct4p (inv4p t) ∧ eq4p (comp4p (inv4p t) t) id4p ∧ eq4p (comp4p t (inv4p t)) id4p

  inv-ok : all-of inv-check all-perm4 ≡ true
  inv-ok = refl

comp4p-distinct : (t s : Pos4) -> distinct4p t ≡ true -> distinct4p s ≡ true ->
                  distinct4p (comp4p t s) ≡ true
comp4p-distinct t s dt ds =
  subst (λ b -> (if b then distinct4p (comp4p t s) else true) ≡ true) (cong₂ _∧_ dt ds)
        (all-of-∈ comp-check (pairs all-perm4 all-perm4) comp-ok
                  (∈-pairs (∈-all-perm4 t dt) (∈-all-perm4 s ds)))

private
  inv-parts : (t : Pos4) -> distinct4p t ≡ true ->
              (distinct4p (inv4p t) ≡ true) × (eq4p (comp4p (inv4p t) t) id4p ≡ true)
                                            × (eq4p (comp4p t (inv4p t)) id4p ≡ true)
  inv-parts t d = ∧-true₃ (all-of-∈ inv-check all-perm4 inv-ok (∈-all-perm4 t d))

inv4p-distinct : (t : Pos4) -> distinct4p t ≡ true -> distinct4p (inv4p t) ≡ true
inv4p-distinct t d = proj₁ (inv-parts t d)

inv4p-left : (t : Pos4) -> distinct4p t ≡ true -> comp4p (inv4p t) t ≡ id4p
inv4p-left t d = eq4p-sound (proj₁ (proj₂ (inv-parts t d)))

inv4p-right : (t : Pos4) -> distinct4p t ≡ true -> comp4p t (inv4p t) ≡ id4p
inv4p-right t d = eq4p-sound (proj₂ (proj₂ (inv-parts t d)))

-- ----------------------------------------------------------------------
-- ** Generalized permutation matrices

-- A generalized permutation: a unitary over 𝔻[i] whose nonzero
-- pattern is that of a permutation matrix and whose nonzero entries
-- are powers of i (Section III C). Column j is i^{phases j}·e_{pos j}.
record GP : Set where
  constructor gperm
  field
    gp-pos : Pos4
    gp-ph : Phase4
    gp-distinct : distinct4p gp-pos ≡ true
open GP public

-- The matrix of a permutation/phase pair, whether or not the
-- permutation part is one.
gp-mat-of : Pos4 -> Phase4 -> Op
gp-mat-of t e =
  Matrix' (unit-vec (selp t p0) (selph e p0) ∷ unit-vec (selp t p1) (selph e p1) ∷
           unit-vec (selp t p2) (selph e p2) ∷ unit-vec (selp t p3) (selph e p3) ∷ [])

gp-mat : GP -> Op
gp-mat G = gp-mat-of (gp-pos G) (gp-ph G)

-- A matrix is a generalized permutation if it is of this form.
IsGPerm : Op -> Set
IsGPerm M = Σ[ G ∈ GP ] M ≡ gp-mat G

-- The identity is one.
gp-one : GP
gp-one = gperm id4p (ph0 , ph0 , ph0 , ph0) refl

gp-one-mat : gp-mat gp-one ≡ 1#
gp-one-mat = refl

-- The product of two generalized permutations.
gp-comp : GP -> GP -> GP
gp-comp G H = gperm (comp4p (gp-pos G) (gp-pos H)) phs
                    (comp4p-distinct (gp-pos G) (gp-pos H) (gp-distinct G) (gp-distinct H))
  where
    ph : Pos -> Phase
    ph j = selph (gp-ph H) j ·p selph (gp-ph G) (selp (gp-pos H) j)
    phs : Phase4
    phs = ph p0 , ph p1 , ph p2 , ph p3

-- The inverse of a generalized permutation.
gp-inverse : GP -> GP
gp-inverse G = gperm (inv4p (gp-pos G)) phs (inv4p-distinct (gp-pos G) (gp-distinct G))
  where
    ph : Pos -> Phase
    ph j = phase-inv (selph (gp-ph G) (selp (inv4p (gp-pos G)) j))
    phs : Phase4
    phs = ph p0 , ph p1 , ph p2 , ph p3

-- ----------------------------------------------------------------------
-- ** The group laws

private
  open M4 using (smul-0ˡ ; vadd-0ˡ ; vadd-0ʳ ; zero-vec)

  -- Σⱼ wⱼaⱼ where w = i^c·e_r is i^c·a_r.
  sel4v : Pos -> Vector 4 DComplex -> Vector 4 DComplex -> Vector 4 DComplex -> Vector 4 DComplex ->
          Vector 4 DComplex
  sel4v p0 a b c d = a
  sel4v p1 a b c d = b
  sel4v p2 a b c d = c
  sel4v p3 a b c d = d

  zeros2 : (u v : Vector 4 DComplex) ->
           vadd (smul 0# u) (vadd (smul 0# v) zero-vec) ≡ zero-vec
  zeros2 u v =
    trans (cong₂ vadd (smul-0ˡ u)
          (trans (cong (λ z -> vadd z zero-vec) (smul-0ˡ v)) (vadd-0ʳ zero-vec)))
          (vadd-0ˡ zero-vec)

  zeros3 : (u v w : Vector 4 DComplex) ->
           vadd (smul 0# u) (vadd (smul 0# v) (vadd (smul 0# w) zero-vec)) ≡ zero-vec
  zeros3 u v w =
    trans (cong₂ vadd (smul-0ˡ u)
          (trans (cong₂ vadd (smul-0ˡ v)
                 (trans (cong (λ z -> vadd z zero-vec) (smul-0ˡ w)) (vadd-0ʳ zero-vec)))
                 (vadd-0ˡ zero-vec)))
          (vadd-0ˡ zero-vec)

  lcomb-unit : (a b c d : Vector 4 DComplex) (r : Pos) (e : Phase) ->
               lcomb (a ∷ b ∷ c ∷ d ∷ []) (unit-vec r e) ≡ smul (phase-val e) (sel4v r a b c d)
  lcomb-unit a b c d p0 e =
    trans (cong (λ z -> vadd (smul (phase-val e) a) z) (zeros3 b c d))
          (vadd-0ʳ (smul (phase-val e) a))
  lcomb-unit a b c d p1 e =
    trans (cong₂ vadd (smul-0ˡ a)
          (trans (cong (λ z -> vadd (smul (phase-val e) b) z) (zeros2 c d))
                 (vadd-0ʳ (smul (phase-val e) b))))
          (vadd-0ˡ (smul (phase-val e) b))
  lcomb-unit a b c d p2 e =
    trans (cong₂ vadd (smul-0ˡ a)
          (trans (cong₂ vadd (smul-0ˡ b)
                 (trans (cong (λ z -> vadd (smul (phase-val e) c) z)
                              (trans (cong (λ z -> vadd z zero-vec) (smul-0ˡ d)) (vadd-0ʳ zero-vec)))
                        (vadd-0ʳ (smul (phase-val e) c))))
                 (vadd-0ˡ (smul (phase-val e) c))))
          (vadd-0ˡ (smul (phase-val e) c))
  lcomb-unit a b c d p3 e =
    trans (cong₂ vadd (smul-0ˡ a)
          (trans (cong₂ vadd (smul-0ˡ b)
                 (trans (cong₂ vadd (smul-0ˡ c) (vadd-0ʳ (smul (phase-val e) d)))
                        (vadd-0ˡ (smul (phase-val e) d))))
                 (vadd-0ˡ (smul (phase-val e) d))))
          (vadd-0ˡ (smul (phase-val e) d))

  smul-unit : (e : Phase) (r : Pos) (e' : Phase) ->
              smul (phase-val e) (unit-vec r e') ≡ unit-vec r (e ·p e')
  smul-unit e p0 e' = vec4-≡ (phase-mul e e') (zeroʳ' e) (zeroʳ' e) (zeroʳ' e)
    where
      zeroʳ' : (c : Phase) -> phase-val c * 0# ≡ 0#
      zeroʳ' c = IsCommutativeRing.zeroʳ isCommutativeRing-DComplex (phase-val c)
  smul-unit e p1 e' = vec4-≡ (zeroʳ' e) (phase-mul e e') (zeroʳ' e) (zeroʳ' e)
    where
      zeroʳ' : (c : Phase) -> phase-val c * 0# ≡ 0#
      zeroʳ' c = IsCommutativeRing.zeroʳ isCommutativeRing-DComplex (phase-val c)
  smul-unit e p2 e' = vec4-≡ (zeroʳ' e) (zeroʳ' e) (phase-mul e e') (zeroʳ' e)
    where
      zeroʳ' : (c : Phase) -> phase-val c * 0# ≡ 0#
      zeroʳ' c = IsCommutativeRing.zeroʳ isCommutativeRing-DComplex (phase-val c)
  smul-unit e p3 e' = vec4-≡ (zeroʳ' e) (zeroʳ' e) (zeroʳ' e) (phase-mul e e')
    where
      zeroʳ' : (c : Phase) -> phase-val c * 0# ≡ 0#
      zeroʳ' c = IsCommutativeRing.zeroʳ isCommutativeRing-DComplex (phase-val c)

  sel4v-unit : (t : Pos4) (e : Phase4) (r : Pos) ->
               sel4v r (unit-vec (selp t p0) (selph e p0)) (unit-vec (selp t p1) (selph e p1))
                       (unit-vec (selp t p2) (selph e p2)) (unit-vec (selp t p3) (selph e p3))
                 ≡ unit-vec (selp t r) (selph e r)
  sel4v-unit t e p0 = refl
  sel4v-unit t e p1 = refl
  sel4v-unit t e p2 = refl
  sel4v-unit t e p3 = refl

-- The product of the matrices of two generalized permutations is the
-- matrix of their product.
gp-mat-comp : (G H : GP) -> gp-mat G * gp-mat H ≡ gp-mat (gp-comp G H)
gp-mat-comp G H = trans (mmul-≡ (gp-mat G) (gp-mat H)) (mat4-≡ (col p0) (col p1) (col p2) (col p3))
  where
    a b c d : Vector 4 DComplex
    a = unit-vec (selp (gp-pos G) p0) (selph (gp-ph G) p0)
    b = unit-vec (selp (gp-pos G) p1) (selph (gp-ph G) p1)
    c = unit-vec (selp (gp-pos G) p2) (selph (gp-ph G) p2)
    d = unit-vec (selp (gp-pos G) p3) (selph (gp-ph G) p3)
    col : (j : Pos) ->
          lcomb (a ∷ b ∷ c ∷ d ∷ []) (unit-vec (selp (gp-pos H) j) (selph (gp-ph H) j))
            ≡ unit-vec (selp (gp-pos G) (selp (gp-pos H) j))
                       (selph (gp-ph H) j ·p selph (gp-ph G) (selp (gp-pos H) j))
    col j = begin
      lcomb (a ∷ b ∷ c ∷ d ∷ []) (unit-vec (selp (gp-pos H) j) (selph (gp-ph H) j))
        ≡⟨ lcomb-unit a b c d (selp (gp-pos H) j) (selph (gp-ph H) j) ⟩
      smul (phase-val (selph (gp-ph H) j)) (sel4v (selp (gp-pos H) j) a b c d)
        ≡⟨ cong (λ v -> smul (phase-val (selph (gp-ph H) j)) v)
                (sel4v-unit (gp-pos G) (gp-ph G) (selp (gp-pos H) j)) ⟩
      smul (phase-val (selph (gp-ph H) j))
           (unit-vec (selp (gp-pos G) (selp (gp-pos H) j)) (selph (gp-ph G) (selp (gp-pos H) j)))
        ≡⟨ smul-unit (selph (gp-ph H) j) (selp (gp-pos G) (selp (gp-pos H) j))
                     (selph (gp-ph G) (selp (gp-pos H) j)) ⟩
      unit-vec (selp (gp-pos G) (selp (gp-pos H) j))
               (selph (gp-ph H) j ·p selph (gp-ph G) (selp (gp-pos H) j)) ∎
      where open ≡-Reasoning

-- Two generalized permutations with the same data have the same matrix.
gp-mat-cong : (G H : GP) ->
              ((j : Pos) -> selp (gp-pos G) j ≡ selp (gp-pos H) j) ->
              ((j : Pos) -> selph (gp-ph G) j ≡ selph (gp-ph H) j) ->
              gp-mat G ≡ gp-mat H
gp-mat-cong G H hp he =
  mat4-≡ (cong₂ unit-vec (hp p0) (he p0)) (cong₂ unit-vec (hp p1) (he p1))
         (cong₂ unit-vec (hp p2) (he p2)) (cong₂ unit-vec (hp p3) (he p3))

-- Reading off the data of a product and of an inverse.
gp-comp-ph : (G H : GP) (j : Pos) ->
             selph (gp-ph (gp-comp G H)) j ≡ selph (gp-ph H) j ·p selph (gp-ph G) (selp (gp-pos H) j)
gp-comp-ph G H p0 = refl
gp-comp-ph G H p1 = refl
gp-comp-ph G H p2 = refl
gp-comp-ph G H p3 = refl

gp-inverse-ph : (G : GP) (j : Pos) ->
                selph (gp-ph (gp-inverse G)) j ≡ phase-inv (selph (gp-ph G) (selp (inv4p (gp-pos G)) j))
gp-inverse-ph G p0 = refl
gp-inverse-ph G p1 = refl
gp-inverse-ph G p2 = refl
gp-inverse-ph G p3 = refl

selp-id : (j : Pos) -> selp id4p j ≡ j
selp-id p0 = refl
selp-id p1 = refl
selp-id p2 = refl
selp-id p3 = refl

selph-one : (j : Pos) -> selph (gp-ph gp-one) j ≡ ph0
selph-one p0 = refl
selph-one p1 = refl
selph-one p2 = refl
selph-one p3 = refl

phase-inv-law' : (c : Phase) -> phase-inv c ·p c ≡ ph0
phase-inv-law' ph0 = refl
phase-inv-law' ph1 = refl
phase-inv-law' ph2 = refl
phase-inv-law' ph3 = refl

-- G⁻¹·G = 1 and G·G⁻¹ = 1.
gp-inverse-left : (G : GP) -> gp-mat (gp-inverse G) * gp-mat G ≡ 1#
gp-inverse-left G = trans (gp-mat-comp (gp-inverse G) G)
                          (trans (gp-mat-cong (gp-comp (gp-inverse G) G) gp-one hp he) gp-one-mat)
  where
    t : Pos4
    t = gp-pos G
    invj : (j : Pos) -> selp (inv4p t) (selp t j) ≡ j
    invj j = trans (sym (selp-comp (inv4p t) t j))
                   (trans (cong (λ s -> selp s j) (inv4p-left t (gp-distinct G))) (selp-id j))
    hp : (j : Pos) -> selp (gp-pos (gp-comp (gp-inverse G) G)) j ≡ selp (gp-pos gp-one) j
    hp j = trans (selp-comp (inv4p t) t j) (trans (invj j) (sym (selp-id j)))
    he : (j : Pos) -> selph (gp-ph (gp-comp (gp-inverse G) G)) j ≡ selph (gp-ph gp-one) j
    he j = trans (gp-comp-ph (gp-inverse G) G j)
           (trans (cong (λ c -> selph (gp-ph G) j ·p c) (gp-inverse-ph G (selp t j)))
           (trans (cong (λ x -> selph (gp-ph G) j ·p phase-inv (selph (gp-ph G) x)) (invj j))
           (trans (phase-inv-law (selph (gp-ph G) j)) (sym (selph-one j)))))

gp-inverse-right : (G : GP) -> gp-mat G * gp-mat (gp-inverse G) ≡ 1#
gp-inverse-right G = trans (gp-mat-comp G (gp-inverse G))
                           (trans (gp-mat-cong (gp-comp G (gp-inverse G)) gp-one hp he) gp-one-mat)
  where
    t : Pos4
    t = gp-pos G
    invj : (j : Pos) -> selp t (selp (inv4p t) j) ≡ j
    invj j = trans (sym (selp-comp t (inv4p t) j))
                   (trans (cong (λ s -> selp s j) (inv4p-right t (gp-distinct G))) (selp-id j))
    hp : (j : Pos) -> selp (gp-pos (gp-comp G (gp-inverse G))) j ≡ selp (gp-pos gp-one) j
    hp j = trans (selp-comp t (inv4p t) j) (trans (invj j) (sym (selp-id j)))
    he : (j : Pos) -> selph (gp-ph (gp-comp G (gp-inverse G))) j ≡ selph (gp-ph gp-one) j
    he j = trans (gp-comp-ph G (gp-inverse G) j)
           (trans (cong (λ c -> c ·p selph (gp-ph G) (selp (inv4p t) j)) (gp-inverse-ph G j))
           (trans (phase-inv-law' (selph (gp-ph G) (selp (inv4p t) j))) (sym (selph-one j))))

-- ----------------------------------------------------------------------
-- ** Generalized permutations have lde 0

lde-unit-vec : (r : Pos) (e : Phase) -> lde (unit-vec r e) ≡ 0
lde-unit-vec p0 e = NatP.≤-antisym (lde-4-≤ (phase-val e) 0# 0# 0# (NatP.≤-reflexive (lde-phase e)) z≤n z≤n z≤n) z≤n
lde-unit-vec p1 e = NatP.≤-antisym (lde-4-≤ 0# (phase-val e) 0# 0# z≤n (NatP.≤-reflexive (lde-phase e)) z≤n z≤n) z≤n
lde-unit-vec p2 e = NatP.≤-antisym (lde-4-≤ 0# 0# (phase-val e) 0# z≤n z≤n (NatP.≤-reflexive (lde-phase e)) z≤n) z≤n
lde-unit-vec p3 e = NatP.≤-antisym (lde-4-≤ 0# 0# 0# (phase-val e) z≤n z≤n z≤n (NatP.≤-reflexive (lde-phase e))) z≤n

lde-gp-of : (t : Pos4) (e : Phase4) -> lde (gp-mat-of t e) ≡ 0
lde-gp-of t e = NatP.≤-antisym
  (lde-4-≤ (unit-vec (selp t p0) (selph e p0)) (unit-vec (selp t p1) (selph e p1))
           (unit-vec (selp t p2) (selph e p2)) (unit-vec (selp t p3) (selph e p3))
                   (NatP.≤-reflexive (lde-unit-vec (selp t p0) (selph e p0)))
                   (NatP.≤-reflexive (lde-unit-vec (selp t p1) (selph e p1)))
                   (NatP.≤-reflexive (lde-unit-vec (selp t p2) (selph e p2)))
                   (NatP.≤-reflexive (lde-unit-vec (selp t p3) (selph e p3))))
  z≤n

lde-gp : (G : GP) -> lde (gp-mat G) ≡ 0
lde-gp G = lde-gp-of (gp-pos G) (gp-ph G)

-- Multiplying by a generalized permutation does not change the lde;
-- this is proved in Kopt.Optimality, where the subadditivity of the
-- lde of a matrix is available.

-- ----------------------------------------------------------------------
-- * Definition V.1: the optimal gate counts

-- A circuit implements an operator if its semantics is that operator.
-- The semantics of Kopt.Gates is exact, i.e. it includes the global
-- phase (that is what the scalar gate Ii = i·(I⊗I) is for), so this
-- is equality on the nose rather than up to a phase.
Implements : Op -> Circuit -> Set
Implements A c = ⟦ c ⟧ ≡ A

-- The gate set 𝒢 of Definition I.1 (together with the scalar gate
-- Ii = i·(I⊗I), which makes the semantics exact rather than up to a
-- global phase). The controlled-K gates CK and KC of Kopt.Gates are
-- *derived* gates (Equation (1)); they are excluded here because
-- their K-count is 2, not 0, so counting them as one gate would make
-- the counts of Definition V.1 wrong.
in-𝒢 : Gate -> Bool
in-𝒢 CK = false
in-𝒢 KC = false
in-𝒢 _ = true

over-𝒢ᵇ : Circuit -> Bool
over-𝒢ᵇ [] = true
over-𝒢ᵇ (g ∷ c) = in-𝒢 g ∧ over-𝒢ᵇ c

Over𝒢 : Circuit -> Set
Over𝒢 c = over-𝒢ᵇ c ≡ true

-- The raw counts rkc, rcs, rlen of Definition V.1 are kc, csc and
-- rlen of Kopt.Gates. The minimal counts kc(A), cs(A), len(A) are not
-- computable, so they are relations here: n is *a* K-count of A if
-- some circuit over 𝒢 implementing A has raw K-count n.
HasKCount HasCSCount HasLength : Op -> ℕ -> Set
HasKCount A n = Σ[ c ∈ Circuit ] (Over𝒢 c × Implements A c × (kc c ≡ n))
HasCSCount A n = Σ[ c ∈ Circuit ] (Over𝒢 c × Implements A c × (csc c ≡ n))
HasLength A n = Σ[ c ∈ Circuit ] (Over𝒢 c × Implements A c × (rlen c ≡ n))

-- n is the least element of a set of natural numbers.
IsMinimal : (ℕ -> Set) -> ℕ -> Set
IsMinimal P n = P n × ((m : ℕ) -> P m -> n Nat.≤ m)

-- "kc(A) = n", "cs(A) = n", "len(A) = n" of Definition V.1.
IsMinimalKCount IsMinimalCSCount IsMinimalLength : Op -> ℕ -> Set
IsMinimalKCount A = IsMinimal (HasKCount A)
IsMinimalCSCount A = IsMinimal (HasCSCount A)
IsMinimalLength A = IsMinimal (HasLength A)

-- A minimum is unique when it exists, so the notation kc(A) is
-- justified.
minimal-unique : {P : ℕ -> Set} {n m : ℕ} -> IsMinimal P n -> IsMinimal P m -> n ≡ m
minimal-unique (pn , ln) (pm , lm) = NatP.≤-antisym (ln _ pm) (lm _ pn)

kc-unique : {A : Op} {n m : ℕ} -> IsMinimalKCount A n -> IsMinimalKCount A m -> n ≡ m
kc-unique = minimal-unique

cs-unique : {A : Op} {n m : ℕ} -> IsMinimalCSCount A n -> IsMinimalCSCount A m -> n ≡ m
cs-unique = minimal-unique

len-unique : {A : Op} {n m : ℕ} -> IsMinimalLength A n -> IsMinimalLength A m -> n ≡ m
len-unique = minimal-unique

-- A circuit is K-optimal if its raw K-count is the minimal one, and
-- similarly for CS and length (Definition V.1).
K-optimal CS-optimal length-optimal : Circuit -> Set
K-optimal c = IsMinimalKCount ⟦ c ⟧ (kc c)
CS-optimal c = IsMinimalCSCount ⟦ c ⟧ (csc c)
length-optimal c = IsMinimalLength ⟦ c ⟧ (rlen c)

-- The raw counts are always attained, so a minimal count is at most
-- the raw count of any implementation.
minimal-≤-raw-kc : {A : Op} {n : ℕ} -> IsMinimalKCount A n ->
                   (c : Circuit) -> Over𝒢 c -> Implements A c -> n Nat.≤ kc c
minimal-≤-raw-kc (_ , least) c ov h = least (kc c) (c , ov , h , refl)

minimal-≤-raw-cs : {A : Op} {n : ℕ} -> IsMinimalCSCount A n ->
                   (c : Circuit) -> Over𝒢 c -> Implements A c -> n Nat.≤ csc c
minimal-≤-raw-cs (_ , least) c ov h = least (csc c) (c , ov , h , refl)

minimal-≤-raw-len : {A : Op} {n : ℕ} -> IsMinimalLength A n ->
                    (c : Circuit) -> Over𝒢 c -> Implements A c -> n Nat.≤ rlen c
minimal-≤-raw-len (_ , least) c ov h = least (rlen c) (c , ov , h , refl)

-- ----------------------------------------------------------------------
-- * Definition V.2: lde-descents

-- An lde-descent of A is a pair L,R of Clifford+CS operators with
-- lde(LAR) ≤ lde(A). By Equation (3) each of L and R is an
-- alternating sequence of generalized permutations and K₁ gates, so a
-- descent is equivalently given by a list of steps, each of which
-- multiplies by a generalized permutation or by a K₁ gate, on the
-- left or on the right.
data Step : Set where
  gp-left gp-right : GP -> Step
  K-left K-right : Step

-- The action of one step.
step-of : Step -> Op -> Op
step-of (gp-left G) A = gp-mat G * A
step-of (gp-right G) A = A * gp-mat G
step-of K-left A = ⟦ K₁ ⟧g * A
step-of K-right A = A * ⟦ K₁ ⟧g

-- The action of a list of steps, applied from the inside out: the
-- first step of the list is the innermost one, so that
-- run [gp-left L₁, K-left, gp-left L₂] A = L₂·K₁·L₁·A, as in the
-- paper's L₂K₁L₁A.
run : List Step -> Op -> Op
run [] A = A
run (s ∷ ss) A = run ss (step-of s A)

run-++ : (ss ts : List Step) (A : Op) -> run (ss ++ ts) A ≡ run ts (run ss A)
run-++ [] ts A = refl
run-++ (s ∷ ss) ts A = run-++ ss ts (step-of s A)

-- The K-count of a step and of a descent (Definition V.2).
step-kc : Step -> ℕ
step-kc (gp-left G) = 0
step-kc (gp-right G) = 0
step-kc K-left = 1
step-kc K-right = 1

steps-kc : List Step -> ℕ
steps-kc [] = 0
steps-kc (s ∷ ss) = step-kc s Nat.+ steps-kc ss

steps-kc-++ : (ss ts : List Step) -> steps-kc (ss ++ ts) ≡ steps-kc ss Nat.+ steps-kc ts
steps-kc-++ [] ts = refl
steps-kc-++ (s ∷ ss) ts =
  trans (cong (λ n -> step-kc s Nat.+ n) (steps-kc-++ ss ts))
        (sym (NatP.+-assoc (step-kc s) (steps-kc ss) (steps-kc ts)))

-- An lde-descent of A (Definition V.2).
record Descent (A : Op) : Set where
  constructor descent
  field
    d-steps : List Step
    d-≤ : lde (run d-steps A) Nat.≤ lde A
open Descent public

d-target : {A : Op} -> Descent A -> Op
d-target {A} d = run (d-steps d) A

-- The K-count rkc of a descent.
d-kc : {A : Op} -> Descent A -> ℕ
d-kc d = steps-kc (d-steps d)

-- An n-descent: the lde decreases by exactly n.
IsNDescent : {A : Op} -> Descent A -> ℕ -> Set
IsNDescent {A} d n = lde (d-target d) Nat.+ n ≡ lde A

-- The sub-descent given by the first k steps, and its exterior (the
-- remaining steps, including all of their K gates).
sub-steps exterior-steps : {A : Op} -> Descent A -> ℕ -> List Step
sub-steps d k = List.take k (d-steps d)
exterior-steps d k = List.drop k (d-steps d)

sub-target : {A : Op} -> Descent A -> ℕ -> Op
sub-target {A} d k = run (sub-steps d k) A

-- A sub-descent is a prefix that is itself a descent.
IsSubDescent : {A : Op} -> Descent A -> ℕ -> Set
IsSubDescent {A} d k = lde (sub-target d k) Nat.≤ lde A

-- The K-count of a descent splits into that of a sub-descent and that
-- of its exterior.
d-kc-split : {A : Op} (d : Descent A) (k : ℕ) ->
             steps-kc (sub-steps d k) Nat.+ steps-kc (exterior-steps d k) ≡ d-kc d
d-kc-split d k =
  trans (sym (steps-kc-++ (sub-steps d k) (exterior-steps d k)))
        (cong steps-kc (ListP.take++drop≡id k (d-steps d)))

-- The target of a descent is the target of the exterior of any of its
-- sub-descents.
d-target-split : {A : Op} (d : Descent A) (k : ℕ) ->
                 run (exterior-steps d k) (sub-target d k) ≡ d-target d
d-target-split {A} d k =
  trans (sym (run-++ (sub-steps d k) (exterior-steps d k) A))
        (cong (λ ss -> run ss A) (ListP.take++drop≡id k (d-steps d)))

-- ----------------------------------------------------------------------
-- ** K-optimality of a descent

-- The K-counts of the descents of A that reach lde ≤ m.
HasDescentKCount : Op -> ℕ -> ℕ -> Set
HasDescentKCount A m k = Σ[ ss ∈ List Step ] ((lde (run ss A) Nat.≤ m) × (steps-kc ss ≡ k))

IsMinimalDescentKCount : Op -> ℕ -> ℕ -> Set
IsMinimalDescentKCount A m = IsMinimal (HasDescentKCount A m)

-- A descent is K-optimal if no descent of A reaching the same lde
-- uses fewer K gates (Definition V.2).
K-optimal-descent : Op -> List Step -> Set
K-optimal-descent A ss = IsMinimalDescentKCount A (lde (run ss A)) (steps-kc ss)

-- ----------------------------------------------------------------------
-- ** Path descents (Figure 1)

-- The edges of Figure 1 (Lemma IV.4). A K-count-1 step either
-- decreases the lde by one along an *undashed* edge
--
--   (iii) → (i),  (iv) → (ii),  (iv) → (v),  (vi) → (iii),  (vi) → (iv)
--
-- (and the transposed forms of the (iv) edges, which act on the
-- right), or it keeps the lde along a *dashed* edge
--
--   (ii) → (iv),  (iii) → (vi),  (v) → (iv).
--
-- There is one further edge, (ii) → (i) at lde 1, which uses a CK
-- gate, that is, two K gates.
fig1-drop : SixCases -> SixCases -> Bool
fig1-drop III I = true
fig1-drop IV II = true
fig1-drop IV V = true
fig1-drop IVt II = true
fig1-drop IVt V = true
fig1-drop VI III = true
fig1-drop VI IV = true
fig1-drop VI IVt = true
fig1-drop _ _ = false

fig1-keep : SixCases -> SixCases -> Bool
fig1-keep II IV = true
fig1-keep II IVt = true
fig1-keep III VI = true
fig1-keep V IV = true
fig1-keep V IVt = true
fig1-keep _ _ = false

-- Does a step from A to B with the given K-count follow an edge of
-- Figure 1?
fig1-step-of : Maybe SixCases -> ℕ -> Maybe SixCases -> ℕ -> ℕ -> Bool
fig1-step-of (just s) l (just t) l' k =
  if k Nat.≡ᵇ 1 then
    (if l' Nat.≡ᵇ l then fig1-keep s t else
     if suc l' Nat.≡ᵇ l then fig1-drop s t else false)
  else
  -- the (ii) → (i) step at lde 1, which uses the gate CK = I ⊕ K
  (if k Nat.≡ᵇ 2 then
     (case-eq s II ∧ case-eq t I ∧ (l Nat.≡ᵇ 1) ∧ (l' Nat.≡ᵇ 0))
   else false)
  where
    case-eq : SixCases -> SixCases -> Bool
    case-eq x y = x == y
fig1-step-of _ _ _ _ _ = false

-- One step of a path descent: a list of steps with K-count 1 (or the
-- exceptional 2) whose effect on the pattern and the lde is an edge
-- of Figure 1.
IsPathStep : Op -> List Step -> Set
IsPathStep A ss =
  fig1-step-of (patof A) (lde A) (patof (run ss A)) (lde (run ss A)) (steps-kc ss) ≡ true

-- A path descent: a sequence of such steps (Definition V.2).
data IsPathDescent : Op -> List Step -> Set where
  path-nil : (A : Op) -> IsPathDescent A []
  path-cons : (A : Op) (ss ts : List Step) ->
              IsPathStep A ss -> IsPathDescent (run ss A) ts ->
              IsPathDescent A (ss ++ ts)

-- A complete path descent is a path descent whose lde reaches 0.
IsCompletePathDescent : Op -> List Step -> Set
IsCompletePathDescent A ss = IsPathDescent A ss × (lde (run ss A) ≡ 0)
