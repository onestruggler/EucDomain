-- Lemmas IV.2 and IV.3 at the second residue digit.
--
-- Kopt.Unitary2 carries them at the first digit: for a unitary U and a
-- denominator exponent l, the parities of the entries of a column and of
-- a row of the integral matrix satisfy
--
--   Σₖ Xₖ꜀·(Xₖᵣ)† = t·2ˡ   with t = 1 for r = c and t = 0 otherwise,
--
-- read through parityℤ[i]. The refinements of Section IV B need the same
-- equation read through ρ₂, because the normal forms they compute are
-- statements about ρˡ₂. Since ρ₂ is a ring homomorphism and fixes the
-- adjoint, that is the same derivation one digit up, and the right hand
-- side becomes ρ₂(2ˡ), which vanishes as soon as l is positive -- 2 is γ²
-- up to a unit, and ρ₂ is taken modulo γ².

{-# OPTIONS --without-K --safe #-}

module Kopt.Unitary3 where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Properties.Algebra
open import Kopt.Patterns using (R2 ; r2-zero)
open import Kopt.Descent using (Op)
open import Kopt.Unitary
  using (Ix ; ι0 ; ι1 ; ι2 ; ι3 ; ix/= ; ix/=-sym ; mcol ; mrow ; ipc ; ipr ; sum4
        ; u-col ; o-col ; u-row ; o-row ; IsUnitary ; u-left ; u-right)
open import Kopt.Unitary2
  using (2ℤℂ ; int-entry ; int-entry-eq ; col-ints ; row-ints ; ipr-ipc-D)

private
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex

  -- 1 and 0 of 𝔻[i] are the images of 1 and 0 of ℤ[i].
  one-D : (1# {A = DComplex}) ≡ from-whole (1# {A = ZComplex})
  one-D = sym from-whole-1

  zero-D : (0# {A = DComplex}) ≡ from-whole (0# {A = ZComplex})
  zero-D = sym from-whole-0

  mul₂-zeroˡ : (v : R2) -> mul₂ r2-zero v ≡ r2-zero
  mul₂-zeroˡ (a ∷ b ∷ []) = refl

-- ----------------------------------------------------------------------
-- * ρ₂ of a power of two
--
-- 2 = -i·γ², so ρ₂(2) vanishes, and with it every positive power.

ρ₂-2 : ρ 2 2ℤℂ ≡ r2-zero
ρ₂-2 = refl

ρ₂-2↑ : (k : ℕ) -> ρ 2 (2ℤℂ ↑ suc k) ≡ r2-zero
ρ₂-2↑ k = trans (ρ₂-* 2ℤℂ (2ℤℂ ↑ k))
                (trans (cong (λ z -> mul₂ z (ρ 2 (2ℤℂ ↑ k))) ρ₂-2)
                       (mul₂-zeroˡ (ρ 2 (2ℤℂ ↑ k))))

-- At l = 0 the right hand side is ρ₂ of t itself.
ρ₂-2↑0 : (T : ZComplex) -> ρ 2 (T * (2ℤℂ ↑ 0)) ≡ ρ 2 T
ρ₂-2↑0 T = cong (ρ 2) (ZR.*-identityʳ T)

-- ----------------------------------------------------------------------
-- * The ρ₂ inner product

-- Σₖ ρ₂(Xₖ)·ρ₂(Yₖ), in the shape the sums of Kopt.Unitary take.
r2-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ZComplex) -> R2
r2-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
  add₂ (mul₂ (ρ 2 X₀) (ρ 2 Y₀))
       (add₂ (mul₂ (ρ 2 X₁) (ρ 2 Y₁))
             (add₂ (mul₂ (ρ 2 X₂) (ρ 2 Y₂)) (mul₂ (ρ 2 X₃) (ρ 2 Y₃))))

-- ρ₂ of a four-term inner product. This is Kopt.Unitary2.parity-ip4 one
-- digit up: ρ₂ is additive and multiplicative and fixes the adjoint.
ρ₂-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ZComplex) ->
         ρ 2 (sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
           ≡ r2-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃
ρ₂-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
  trans (ρ₂-+ (X₀ * (Y₀ †)) _)
        (cong₂ add₂ (term X₀ Y₀)
          (trans (ρ₂-+ (X₁ * (Y₁ †)) _)
            (cong₂ add₂ (term X₁ Y₁)
              (trans (ρ₂-+ (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
                     (cong₂ add₂ (term X₂ Y₂) (term X₃ Y₃))))))
  where
    term : (X Y : ZComplex) -> ρ 2 (X * (Y †)) ≡ mul₂ (ρ 2 X) (ρ 2 Y)
    term X Y = trans (ρ₂-* X (Y †)) (cong (λ z -> mul₂ (ρ 2 X) z) (ρ₂-adj Y))

-- ----------------------------------------------------------------------
-- * Lemmas IV.2 and IV.3 at ρ₂

-- The ρ₂ inner product of two columns, and of two rows, of the integral
-- matrix of U at the denominator exponent l.
r2-cols : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) -> R2
r2-cols U l hl r c =
  r2-ip4 (int-entry U l hl ι0 c) (int-entry U l hl ι0 r)
         (int-entry U l hl ι1 c) (int-entry U l hl ι1 r)
         (int-entry U l hl ι2 c) (int-entry U l hl ι2 r)
         (int-entry U l hl ι3 c) (int-entry U l hl ι3 r)

r2-rows : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) -> R2
r2-rows U l hl r c =
  r2-ip4 (int-entry U l hl c ι0) (int-entry U l hl r ι0)
         (int-entry U l hl c ι1) (int-entry U l hl r ι1)
         (int-entry U l hl c ι2) (int-entry U l hl r ι2)
         (int-entry U l hl c ι3) (int-entry U l hl r ι3)

-- Each is ρ₂ of t·2ˡ, for the t of the corresponding inner product of U.
r2-col : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
         ipc (mcol c U) (mcol r U) ≡ from-whole T ->
         r2-cols U l hl r c ≡ ρ 2 (T * (2ℤℂ ↑ l))
r2-col U l hl r c T hip =
  trans (sym (ρ₂-ip4 (int-entry U l hl ι0 c) (int-entry U l hl ι0 r)
                     (int-entry U l hl ι1 c) (int-entry U l hl ι1 r)
                     (int-entry U l hl ι2 c) (int-entry U l hl ι2 r)
                     (int-entry U l hl ι3 c) (int-entry U l hl ι3 r)))
        (cong (ρ 2) (col-ints U l hl r c T hip))

r2-row : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
         ipc (mrow c U) (mrow r U) ≡ from-whole T ->
         r2-rows U l hl r c ≡ ρ 2 (T * (2ℤℂ ↑ l))
r2-row U l hl r c T hip =
  trans (sym (ρ₂-ip4 (int-entry U l hl c ι0) (int-entry U l hl r ι0)
                     (int-entry U l hl c ι1) (int-entry U l hl r ι1)
                     (int-entry U l hl c ι2) (int-entry U l hl r ι2)
                     (int-entry U l hl c ι3) (int-entry U l hl r ι3)))
        (cong (ρ 2) (row-ints U l hl r c T hip))

private
  ρ₂-0 : ρ 2 (0# {A = ZComplex}) ≡ r2-zero
  ρ₂-0 = refl

-- At a positive lde every one of the four vanishes: the ρ₂ inner product
-- of two columns, equal or not, and likewise for rows. This is the
-- constraint the refinements of Section IV B are solved against -- the
-- ρ₂-orthogonality of the columns and of the rows.
r2-col-norm : (U : Op) (k : ℕ) (hl : lde U Nat.≤ suc k) -> adjoint U * U ≡ 1# -> (c : Ix) ->
              r2-cols U (suc k) hl c c ≡ r2-zero
r2-col-norm U k hl hu c =
  trans (r2-col U (suc k) hl c c 1# (trans (u-col U hu c) one-D))
        (trans (cong (ρ 2) (ZR.*-identityˡ (2ℤℂ ↑ suc k))) (ρ₂-2↑ k))

r2-col-orth : (U : Op) (k : ℕ) (hl : lde U Nat.≤ suc k) -> adjoint U * U ≡ 1# ->
              (r c : Ix) -> ix/= r c ≡ true -> r2-cols U (suc k) hl r c ≡ r2-zero
r2-col-orth U k hl hu r c d =
  trans (r2-col U (suc k) hl r c 0# (trans (o-col U hu r c d) zero-D))
        (trans (cong (ρ 2) (ZR.zeroˡ (2ℤℂ ↑ suc k))) ρ₂-0)

r2-row-norm : (U : Op) (k : ℕ) (hl : lde U Nat.≤ suc k) -> U * adjoint U ≡ 1# -> (r : Ix) ->
              r2-rows U (suc k) hl r r ≡ r2-zero
r2-row-norm U k hl hu r =
  trans (r2-row U (suc k) hl r r 1#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow r U))) (u-row U hu r)) one-D))
        (trans (cong (ρ 2) (ZR.*-identityˡ (2ℤℂ ↑ suc k))) (ρ₂-2↑ k))

r2-row-orth : (U : Op) (k : ℕ) (hl : lde U Nat.≤ suc k) -> U * adjoint U ≡ 1# ->
              (r c : Ix) -> ix/= r c ≡ true -> r2-rows U (suc k) hl r c ≡ r2-zero
r2-row-orth U k hl hu r c d =
  trans (r2-row U (suc k) hl r c 0#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow c U)))
                        (o-row U hu c r (ix/=-sym r c d))) zero-D))
        (trans (cong (ρ 2) (ZR.zeroˡ (2ℤℂ ↑ suc k))) ρ₂-0)

-- ----------------------------------------------------------------------
-- * The same at the third digit
--
-- Two differences from ρ₂. First, ρ₃ does not fix the adjoint: it
-- conjugates, which at the level of digits is conj₃ (abc goes to
-- ab(c+b)). Second, add₃ carries -- its third digit is c+c'+a·a' -- so
-- the third digit of a sum of four terms collects the pairwise products
-- of their leading digits. Both show up below.

r3-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ZComplex) -> Residue 3
r3-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
  add₃ (mul₃ (ρ 3 X₀) (conj₃ (ρ 3 Y₀)))
       (add₃ (mul₃ (ρ 3 X₁) (conj₃ (ρ 3 Y₁)))
             (add₃ (mul₃ (ρ 3 X₂) (conj₃ (ρ 3 Y₂))) (mul₃ (ρ 3 X₃) (conj₃ (ρ 3 Y₃)))))

ρ₃-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ZComplex) ->
         ρ 3 (sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
           ≡ r3-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃
ρ₃-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
  trans (ρ₃-+ (X₀ * (Y₀ †)) _)
        (cong₂ add₃ (term X₀ Y₀)
          (trans (ρ₃-+ (X₁ * (Y₁ †)) _)
            (cong₂ add₃ (term X₁ Y₁)
              (trans (ρ₃-+ (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
                     (cong₂ add₃ (term X₂ Y₂) (term X₃ Y₃))))))
  where
    term : (X Y : ZComplex) -> ρ 3 (X * (Y †)) ≡ mul₃ (ρ 3 X) (conj₃ (ρ 3 Y))
    term X Y = trans (ρ₃-* X (Y †)) (cong (λ z -> mul₃ (ρ 3 X) z) (ρ₃-adj Y))

-- ----------------------------------------------------------------------
-- * ρ₃ of a power of two
--
-- 2 = -i·γ², so ρ₃(2) = 001: two is divisible by γ² but not by γ³. Hence
-- multiplying by it shifts a residue down to its leading digit, and two
-- factors of it vanish.

ρ₃-2 : ρ 3 2ℤℂ ≡ (Even ∷ Even ∷ Odd ∷ [])
ρ₃-2 = refl

private
  mul₃-2 : (v : Residue 3) -> mul₃ (Even ∷ Even ∷ Odd ∷ []) v ≡ (Even ∷ Even ∷ Vec.head v ∷ [])
  mul₃-2 (a ∷ b ∷ c ∷ []) = refl

  -- the leading digit of ρ₃(2ˡ) for positive l
  head-2↑ : (k : ℕ) -> Vec.head (ρ 3 (2ℤℂ ↑ suc k)) ≡ Even
  head-2↑ k = cong Vec.head
                   (trans (ρ₃-* 2ℤℂ (2ℤℂ ↑ k))
                          (trans (cong (λ z -> mul₃ z (ρ 3 (2ℤℂ ↑ k))) ρ₃-2)
                                 (mul₃-2 (ρ 3 (2ℤℂ ↑ k)))))

ρ₃-2↑0 : ρ 3 (2ℤℂ ↑ 0) ≡ (Odd ∷ Even ∷ Even ∷ [])
ρ₃-2↑0 = refl

ρ₃-2↑1 : ρ 3 (2ℤℂ ↑ 1) ≡ (Even ∷ Even ∷ Odd ∷ [])
ρ₃-2↑1 = refl

ρ₃-2↑2 : (k : ℕ) -> ρ 3 (2ℤℂ ↑ suc (suc k)) ≡ (Even ∷ Even ∷ Even ∷ [])
ρ₃-2↑2 k =
  trans (ρ₃-* 2ℤℂ (2ℤℂ ↑ suc k))
        (trans (cong (λ z -> mul₃ z (ρ 3 (2ℤℂ ↑ suc k))) ρ₃-2)
               (trans (mul₃-2 (ρ 3 (2ℤℂ ↑ suc k)))
                      (cong (λ h -> Even ∷ Even ∷ h ∷ []) (head-2↑ k))))

-- ----------------------------------------------------------------------
-- * Lemmas IV.2 and IV.3 at ρ₃

r3-cols : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) -> Residue 3
r3-cols U l hl r c =
  r3-ip4 (int-entry U l hl ι0 c) (int-entry U l hl ι0 r)
         (int-entry U l hl ι1 c) (int-entry U l hl ι1 r)
         (int-entry U l hl ι2 c) (int-entry U l hl ι2 r)
         (int-entry U l hl ι3 c) (int-entry U l hl ι3 r)

r3-rows : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) -> Residue 3
r3-rows U l hl r c =
  r3-ip4 (int-entry U l hl c ι0) (int-entry U l hl r ι0)
         (int-entry U l hl c ι1) (int-entry U l hl r ι1)
         (int-entry U l hl c ι2) (int-entry U l hl r ι2)
         (int-entry U l hl c ι3) (int-entry U l hl r ι3)

r3-col : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
         ipc (mcol c U) (mcol r U) ≡ from-whole T ->
         r3-cols U l hl r c ≡ ρ 3 (T * (2ℤℂ ↑ l))
r3-col U l hl r c T hip =
  trans (sym (ρ₃-ip4 (int-entry U l hl ι0 c) (int-entry U l hl ι0 r)
                     (int-entry U l hl ι1 c) (int-entry U l hl ι1 r)
                     (int-entry U l hl ι2 c) (int-entry U l hl ι2 r)
                     (int-entry U l hl ι3 c) (int-entry U l hl ι3 r)))
        (cong (ρ 3) (col-ints U l hl r c T hip))

r3-row : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
         ipc (mrow c U) (mrow r U) ≡ from-whole T ->
         r3-rows U l hl r c ≡ ρ 3 (T * (2ℤℂ ↑ l))
r3-row U l hl r c T hip =
  trans (sym (ρ₃-ip4 (int-entry U l hl c ι0) (int-entry U l hl r ι0)
                     (int-entry U l hl c ι1) (int-entry U l hl r ι1)
                     (int-entry U l hl c ι2) (int-entry U l hl r ι2)
                     (int-entry U l hl c ι3) (int-entry U l hl r ι3)))
        (cong (ρ 3) (row-ints U l hl r c T hip))

-- The norm of a column, at ρ₃: for l ≥ 2 it vanishes, for l = 1 it is
-- 001, and for l = 0 it is 100. This is the congruence that the ρ₂
-- normal forms of Section IV B are cut down by -- the second ρ₂ digits
-- are constrained by the third ρ₃ digit of the norm.
r3-col-norm : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> adjoint U * U ≡ 1# -> (c : Ix) ->
              r3-cols U l hl c c ≡ ρ 3 (2ℤℂ ↑ l)
r3-col-norm U l hl hu c =
  trans (r3-col U l hl c c 1# (trans (u-col U hu c) one-D))
        (cong (ρ 3) (ZR.*-identityˡ (2ℤℂ ↑ l)))

r3-row-norm : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> U * adjoint U ≡ 1# -> (r : Ix) ->
              r3-rows U l hl r r ≡ ρ 3 (2ℤℂ ↑ l)
r3-row-norm U l hl hu r =
  trans (r3-row U l hl r r 1#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow r U))) (u-row U hu r)) one-D))
        (cong (ρ 3) (ZR.*-identityˡ (2ℤℂ ↑ l)))

-- Two distinct columns, at ρ₃: the inner product vanishes identically,
-- for every l. This is the condition behind the paper's exclusion of the
-- impossible sub-case of pattern (vi).
r3-col-orth : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> adjoint U * U ≡ 1# ->
              (r c : Ix) -> ix/= r c ≡ true -> r3-cols U l hl r c ≡ (Even ∷ Even ∷ Even ∷ [])
r3-col-orth U l hl hu r c d =
  trans (r3-col U l hl r c 0# (trans (o-col U hu r c d) zero-D))
        (trans (cong (ρ 3) (ZR.zeroˡ (2ℤℂ ↑ l))) refl)

r3-row-orth : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> U * adjoint U ≡ 1# ->
              (r c : Ix) -> ix/= r c ≡ true -> r3-rows U l hl r c ≡ (Even ∷ Even ∷ Even ∷ [])
r3-row-orth U l hl hu r c d =
  trans (r3-row U l hl r c 0#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow c U)))
                        (o-row U hu c r (ix/=-sym r c d))) zero-D))
        (trans (cong (ρ 3) (ZR.zeroˡ (2ℤℂ ↑ l))) refl)

-- ----------------------------------------------------------------------
-- * Reading the digits of a norm
--
-- The norm of one entry, at ρ₃. With a = ρ₃(X) leading, b second and c
-- third, X·X† has digits a, Even and b·(a+1): the middle digit always
-- vanishes, and the third one is the second digit of X exactly when X is
-- even. Four cases on (a,b) -- c plays no part -- because a·a = a and
-- b·b = b need the digits to be known.

-- The second digit of a residue.
snd₃ : Residue 3 -> Z2
snd₃ (a ∷ b ∷ c ∷ []) = b

r3-self : (u : Residue 3) ->
          mul₃ u (conj₃ u) ≡ (Vec.head u ∷ Even ∷ (snd₃ u * (Vec.head u + Odd)) ∷ [])
r3-self (Even ∷ Even ∷ Even ∷ []) = refl
r3-self (Even ∷ Even ∷ Odd ∷ []) = refl
r3-self (Even ∷ Odd ∷ Even ∷ []) = refl
r3-self (Even ∷ Odd ∷ Odd ∷ []) = refl
r3-self (Odd ∷ Even ∷ Even ∷ []) = refl
r3-self (Odd ∷ Even ∷ Odd ∷ []) = refl
r3-self (Odd ∷ Odd ∷ Even ∷ []) = refl
r3-self (Odd ∷ Odd ∷ Odd ∷ []) = refl

-- The norm of a column, digit by digit. add₃ carries, so the third digit
-- of the four-term sum picks up the second elementary symmetric function
-- of the four leading digits as well.
-- The third digit of the sum, in exactly the shape the three add₃ steps
-- produce it: the four third digits, plus the carries, which are the
-- pairwise products of the leading digits grouped as the nesting groups
-- them. (The tidier form Σ dₖ + Σ_{j<k} pⱼpₖ differs from this only by
-- associativity and commutativity of + in ℤ₂, so it needs the ring
-- solver; nothing below cares which form it is in, because what consumes
-- it is an enumeration that computes.)
norm-digit2 : (p₀ p₁ p₂ p₃ d₀ d₁ d₂ d₃ : Z2) -> Z2
norm-digit2 p₀ p₁ p₂ p₃ d₀ d₁ d₂ d₃ =
  (d₀ + ((d₁ + ((d₂ + d₃) + p₂ * p₃)) + p₁ * (p₂ + p₃))) + p₀ * (p₁ + (p₂ + p₃))

r3-ip4-self : (X₀ X₁ X₂ X₃ : ZComplex) ->
              r3-ip4 X₀ X₀ X₁ X₁ X₂ X₂ X₃ X₃
                ≡ (sum4 (Vec.head (ρ 3 X₀)) (Vec.head (ρ 3 X₁))
                        (Vec.head (ρ 3 X₂)) (Vec.head (ρ 3 X₃))
                   ∷ Even
                   ∷ norm-digit2 (Vec.head (ρ 3 X₀)) (Vec.head (ρ 3 X₁))
                                 (Vec.head (ρ 3 X₂)) (Vec.head (ρ 3 X₃))
                                 (snd₃ (ρ 3 X₀) * (Vec.head (ρ 3 X₀) + Odd))
                                 (snd₃ (ρ 3 X₁) * (Vec.head (ρ 3 X₁) + Odd))
                                 (snd₃ (ρ 3 X₂) * (Vec.head (ρ 3 X₂) + Odd))
                                 (snd₃ (ρ 3 X₃) * (Vec.head (ρ 3 X₃) + Odd)) ∷ [])
r3-ip4-self X₀ X₁ X₂ X₃ =
  trans (cong₂ add₃ (r3-self (ρ 3 X₀))
          (cong₂ add₃ (r3-self (ρ 3 X₁))
            (cong₂ add₃ (r3-self (ρ 3 X₂)) (r3-self (ρ 3 X₃)))))
        (go (Vec.head (ρ 3 X₀)) (Vec.head (ρ 3 X₁)) (Vec.head (ρ 3 X₂)) (Vec.head (ρ 3 X₃))
            (snd₃ (ρ 3 X₀) * (Vec.head (ρ 3 X₀) + Odd)) (snd₃ (ρ 3 X₁) * (Vec.head (ρ 3 X₁) + Odd))
            (snd₃ (ρ 3 X₂) * (Vec.head (ρ 3 X₂) + Odd)) (snd₃ (ρ 3 X₃) * (Vec.head (ρ 3 X₃) + Odd)))
  where
    -- the three add₃ steps, over the eight digits as variables
    go : (p₀ p₁ p₂ p₃ d₀ d₁ d₂ d₃ : Z2) ->
         add₃ (p₀ ∷ Even ∷ d₀ ∷ [])
              (add₃ (p₁ ∷ Even ∷ d₁ ∷ [])
                    (add₃ (p₂ ∷ Even ∷ d₂ ∷ []) (p₃ ∷ Even ∷ d₃ ∷ [])))
           ≡ (sum4 p₀ p₁ p₂ p₃ ∷ Even ∷ norm-digit2 p₀ p₁ p₂ p₃ d₀ d₁ d₂ d₃ ∷ [])
    go p₀ p₁ p₂ p₃ d₀ d₁ d₂ d₃ = refl
