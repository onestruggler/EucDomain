-- Common tools for proving that the rings of the newsynth ring
-- framework (Quantum.Synthesis.Ring) are commutative rings:
--
-- * CRLaws / isCommutativeRing-from-laws: build an IsCommutativeRing
--   (with propositional equality) from a minimal set of laws.
--
-- * ZSolver R: a ring solver for an arbitrary commutative ring R with
--   integer coefficients. It is the stdlib solver Algebra.Solver.Ring
--   instantiated with the coefficient ring ℤ and the unique ring
--   homomorphism ℤ → R. Unlike Algebra.Solver.Ring.Simple, it does
--   not need decidable equality on R, so it can be used for an
--   abstract ring R.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Common where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
import Algebra.Definitions
import Algebra.Consequences.Propositional as Consequences
import Algebra.Solver.Ring as OldSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_,_)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; cong₂ ; isEquivalence)

-- ----------------------------------------------------------------------
-- * Commutative rings from a minimal set of laws

module _ {A : Set} (_+_ _*_ : A -> A -> A) (-_ : A -> A) (0# 1# : A) where
  open Algebra.Definitions (_≡_ {A = A})

  record CRLaws : Set where
    field
      +-assoc : Associative _+_
      +-comm : Commutative _+_
      +-identityˡ : LeftIdentity 0# _+_
      -‿inverseˡ : LeftInverse 0# -_ _+_
      *-assoc : Associative _*_
      *-comm : Commutative _*_
      *-identityˡ : LeftIdentity 1# _*_
      distribʳ : _*_ DistributesOverʳ _+_

  isCommutativeRing-from-laws : CRLaws -> IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1#
  isCommutativeRing-from-laws L = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _+_ }
              ; assoc = +-assoc }
            ; identity = +-identityˡ , Consequences.comm∧idˡ⇒idʳ +-comm +-identityˡ }
          ; inverse = -‿inverseˡ , Consequences.comm∧invˡ⇒invʳ +-comm -‿inverseˡ
          ; ⁻¹-cong = ≡.cong -_ }
        ; comm = +-comm }
      ; *-cong = cong₂ _*_
      ; *-assoc = *-assoc
      ; *-identity = *-identityˡ , Consequences.comm∧idˡ⇒idʳ *-comm *-identityˡ
      ; distrib = Consequences.comm∧distrʳ⇒distrˡ *-comm distribʳ , distribʳ }
    ; *-comm = *-comm }
    where open CRLaws L

-- ----------------------------------------------------------------------
-- * A ring solver with integer coefficients for any commutative ring

module ZSolver {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R
  open import Algebra.Properties.Semiring.Mult.TCOptimised semiring using (_×_ ; ×-homo-+ ; ×1-homo-* ; 1+×)
  open import Algebra.Properties.Ring ring using (-‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; [-x][-y]≈xy ; -0#≈0# ; -‿+-comm)
  open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using (medial)
  open import Relation.Binary.Reasoning.Setoid setoid

  -- The unique ring homomorphism ℤ → R. We use the multiplication
  -- _×_ optimised for type checking, so that ⟦ 0 ⟧ℤ = 0# and ⟦ 1 ⟧ℤ = 1#
  -- hold definitionally.
  ⟦_⟧ℤ : ℤ -> Carrier
  ⟦ + n ⟧ℤ = n × 1#
  ⟦ -[1+ n ] ⟧ℤ = - (suc n × 1#)

  private
    lemma-suc : ∀ x y -> x + - y ≈ (1# + x) + - (1# + y)
    lemma-suc x y = sym (begin
      (1# + x) + - (1# + y)     ≈⟨ +-congˡ (sym (-‿+-comm 1# y)) ⟩
      (1# + x) + (- 1# + - y)   ≈⟨ medial 1# x (- 1#) (- y) ⟩
      (1# + - 1#) + (x + - y)   ≈⟨ +-congʳ (-‿inverseʳ 1#) ⟩
      0# + (x + - y)            ≈⟨ +-identityˡ _ ⟩
      x + - y                   ∎)

    ⊖-homo : ∀ m n -> ⟦ m ℤ.⊖ n ⟧ℤ ≈ m × 1# + - (n × 1#)
    ⊖-homo zero zero = sym (trans (+-congˡ -0#≈0#) (+-identityʳ 0#))
    ⊖-homo zero (suc n) = sym (+-identityˡ _)
    ⊖-homo (suc m) zero = sym (trans (+-congˡ -0#≈0#) (+-identityʳ _))
    ⊖-homo (suc m) (suc n) = begin
      ⟦ suc m ℤ.⊖ suc n ⟧ℤ     ≡⟨ ≡.cong ⟦_⟧ℤ (ℤP.[1+m]⊖[1+n]≡m⊖n m n) ⟩
      ⟦ m ℤ.⊖ n ⟧ℤ             ≈⟨ ⊖-homo m n ⟩
      m × 1# + - (n × 1#)     ≈⟨ lemma-suc _ _ ⟩
      (1# + m × 1#) + - (1# + n × 1#) ≈⟨ +-cong (sym (1+× m 1#)) (-‿cong (sym (1+× n 1#))) ⟩
      suc m × 1# + - (suc n × 1#) ∎

  +-homoℤ : ∀ x y -> ⟦ x ℤ.+ y ⟧ℤ ≈ ⟦ x ⟧ℤ + ⟦ y ⟧ℤ
  +-homoℤ (+ m) (+ n) = ×-homo-+ 1# m n
  +-homoℤ (+ m) -[1+ n ] = ⊖-homo m (suc n)
  +-homoℤ -[1+ m ] (+ n) = trans (⊖-homo n (suc m)) (+-comm _ _)
  +-homoℤ -[1+ m ] -[1+ n ] = begin
    - (suc (suc (m ℕ.+ n)) × 1#)          ≡⟨ ≡.cong (λ k -> - (k × 1#)) (≡.cong suc (≡.sym (ℕP.+-suc m n))) ⟩
    - ((suc m ℕ.+ suc n) × 1#)            ≈⟨ -‿cong (×-homo-+ 1# (suc m) (suc n)) ⟩
    - (suc m × 1# + suc n × 1#)           ≈⟨ sym (-‿+-comm _ _) ⟩
    - (suc m × 1#) + - (suc n × 1#)       ∎

  -‿homoℤ : ∀ x -> ⟦ ℤ.- x ⟧ℤ ≈ - ⟦ x ⟧ℤ
  -‿homoℤ (+ zero) = sym -0#≈0#
  -‿homoℤ (+ suc n) = refl
  -‿homoℤ -[1+ n ] = sym (-‿involutive _)

  private
    pos-*-homo : ∀ m n -> ⟦ + m ℤ.* + n ⟧ℤ ≈ ⟦ + m ⟧ℤ * ⟦ + n ⟧ℤ
    pos-*-homo m n = begin
      ⟦ + m ℤ.* + n ⟧ℤ    ≡⟨ ≡.cong ⟦_⟧ℤ (≡.sym (ℤP.pos-* m n)) ⟩
      (m ℕ.* n) × 1#     ≈⟨ ×1-homo-* m n ⟩
      ⟦ + m ⟧ℤ * ⟦ + n ⟧ℤ ∎

  *-homoℤ : ∀ x y -> ⟦ x ℤ.* y ⟧ℤ ≈ ⟦ x ⟧ℤ * ⟦ y ⟧ℤ
  *-homoℤ (+ m) (+ n) = pos-*-homo m n
  *-homoℤ -[1+ m ] (+ n) = begin
    ⟦ -[1+ m ] ℤ.* + n ⟧ℤ          ≡⟨ ≡.cong ⟦_⟧ℤ (≡.sym (ℤP.neg-distribˡ-* (+ suc m) (+ n))) ⟩
    ⟦ ℤ.- (+ suc m ℤ.* + n) ⟧ℤ     ≈⟨ -‿homoℤ (+ suc m ℤ.* + n) ⟩
    - ⟦ + suc m ℤ.* + n ⟧ℤ         ≈⟨ -‿cong (pos-*-homo (suc m) n) ⟩
    - (⟦ + suc m ⟧ℤ * ⟦ + n ⟧ℤ)    ≈⟨ -‿distribˡ-* _ _ ⟩
    ⟦ -[1+ m ] ⟧ℤ * ⟦ + n ⟧ℤ       ∎
  *-homoℤ (+ m) -[1+ n ] = begin
    ⟦ + m ℤ.* -[1+ n ] ⟧ℤ          ≡⟨ ≡.cong ⟦_⟧ℤ (≡.sym (ℤP.neg-distribʳ-* (+ m) (+ suc n))) ⟩
    ⟦ ℤ.- (+ m ℤ.* + suc n) ⟧ℤ     ≈⟨ -‿homoℤ (+ m ℤ.* + suc n) ⟩
    - ⟦ + m ℤ.* + suc n ⟧ℤ         ≈⟨ -‿cong (pos-*-homo m (suc n)) ⟩
    - (⟦ + m ⟧ℤ * ⟦ + suc n ⟧ℤ)    ≈⟨ -‿distribʳ-* _ _ ⟩
    ⟦ + m ⟧ℤ * ⟦ -[1+ n ] ⟧ℤ       ∎
  *-homoℤ -[1+ m ] -[1+ n ] = begin
    ⟦ -[1+ m ] ℤ.* -[1+ n ] ⟧ℤ     ≡⟨ ≡.cong ⟦_⟧ℤ (≡.sym (ℤP.pos-* (suc m) (suc n))) ⟩
    ⟦ + (suc m ℕ.* suc n) ⟧ℤ        ≈⟨ ×1-homo-* (suc m) (suc n) ⟩
    ⟦ + suc m ⟧ℤ * ⟦ + suc n ⟧ℤ    ≈⟨ sym ([-x][-y]≈xy _ _) ⟩
    ⟦ -[1+ m ] ⟧ℤ * ⟦ -[1+ n ] ⟧ℤ  ∎

  morphism : ℤ.+-*-rawRing ACR.-Raw-AlmostCommutative⟶ ACR.fromCommutativeRing R
  morphism = record
    { ⟦_⟧ = ⟦_⟧ℤ
    ; +-homo = +-homoℤ
    ; *-homo = *-homoℤ
    ; -‿homo = -‿homoℤ
    ; 0-homo = refl
    ; 1-homo = refl
    }

  private
    dec : ∀ a b -> Maybe (⟦ a ⟧ℤ ≈ ⟦ b ⟧ℤ)
    dec a b with a ℤP.≟ b
    ... | yes ≡.refl = just refl
    ... | no _ = nothing

  -- The solver. Use it like Algebra.Solver.Ring.Simple, e.g.
  --   solve 2 (λ x y -> x :* y := y :* x) refl a b
  open OldSolver ℤ.+-*-rawRing (ACR.fromCommutativeRing R) morphism dec public
