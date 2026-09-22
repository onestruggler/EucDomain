-- Ring endomorphisms of a ring A (for the instance operations), and
-- (module Laws) the fact that they commute with the semantics of the
-- solver expressions. This is used to prove that the adjoint
-- operations adj and adj2 of A [√2], A [i], A [ω] are (involutive)
-- ring homomorphisms.
--
-- The records only depend on the Ring instance, not on a proof of the
-- ring laws, so that using them for particular rings does not
-- instantiate the solver modules (which is expensive).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Hom where

open import Instances
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Vec.Base using (Vec ; map ; lookup)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

-- Ring endomorphisms (unital).
record IsRingEndo {A : Set} {{RA : Ring A}} (f : A -> A) : Set where
  field
    f-+ : ∀ x y -> f (x + y) ≡ f x + f y
    f-* : ∀ x y -> f (x * y) ≡ f x * f y
    f-1 : f 1# ≡ 1#

-- Involutive ring endomorphisms (i.e., involutive automorphisms).
record IsInvolutiveRingEndo {A : Set} {{RA : Ring A}} (f : A -> A) : Set where
  field
    isRingEndo : IsRingEndo f
    involutive : ∀ x -> f (f x) ≡ x
  open IsRingEndo isRingEndo public

-- The identity is an involutive automorphism.
id-isInvolutiveRingEndo : {A : Set} {{RA : Ring A}} -> IsInvolutiveRingEndo {A} (λ x -> x)
id-isInvolutiveRingEndo = record
  { isRingEndo = record { f-+ = λ _ _ -> refl ; f-* = λ _ _ -> refl ; f-1 = refl }
  ; involutive = λ _ -> refl }

-- Consequences, for a commutative ring A.
module Laws {A : Set} {{RA : Ring A}} (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
            {f : A -> A} (F : IsRingEndo f) where

  open import Quantum.Synthesis.Ring.Properties.Poly isCR
    using (commutativeRing ; Polynomial ; ⟦_⟧ ; ⟦_⟧ℤ)
  open import Algebra.Solver.Ring using (op ; con ; var ; _:^_ ; :-_ ; [+] ; [*])
  open import Algebra.Bundles using (CommutativeRing)
  open import Algebra.Properties.Ring (CommutativeRing.ring commutativeRing)
    using (x+x≈x⇒x≈0 ; +-inverseˡ-unique)
  private
    module A = IsCommutativeRing isCR

  open IsRingEndo F public

  f-0 : f 0# ≡ 0#
  f-0 = x+x≈x⇒x≈0 (f 0#) (trans (sym (f-+ 0# 0#)) (cong f (A.+-identityˡ 0#)))

  f-neg : ∀ x -> f (- x) ≡ - f x
  f-neg x = +-inverseˡ-unique (f (- x)) (f x)
    (trans (sym (f-+ (- x) x)) (trans (cong f (A.-‿inverseˡ x)) f-0))

  f-ℕ : ∀ n -> f ⟦ + n ⟧ℤ ≡ ⟦ + n ⟧ℤ
  f-ℕ zero = f-0
  f-ℕ (suc zero) = f-1
  f-ℕ (suc (suc n)) = trans (f-+ _ 1#) (cong₂ _+_ (f-ℕ (suc n)) f-1)

  f-ℤ : ∀ c -> f ⟦ c ⟧ℤ ≡ ⟦ c ⟧ℤ
  f-ℤ (+ n) = f-ℕ n
  f-ℤ -[1+ n ] = trans (f-neg _) (cong -_ (f-ℕ (suc n)))

  -- f commutes with the semantics of solver expressions.
  f-⟦⟧ : ∀ {n} (p : Polynomial n) (ρ : Vec A n) -> f (⟦ p ⟧ ρ) ≡ ⟦ p ⟧ (map f ρ)
  f-⟦⟧ (op [+] p q) ρ = trans (f-+ _ _) (cong₂ _+_ (f-⟦⟧ p ρ) (f-⟦⟧ q ρ))
  f-⟦⟧ (op [*] p q) ρ = trans (f-* _ _) (cong₂ _*_ (f-⟦⟧ p ρ) (f-⟦⟧ q ρ))
  f-⟦⟧ (con c) ρ = f-ℤ c
  f-⟦⟧ (var x) ρ = sym (lookup-map x f ρ)
  f-⟦⟧ (p :^ zero) ρ = f-1
  f-⟦⟧ (p :^ suc k) ρ = trans (f-* _ _) (cong₂ _*_ (f-⟦⟧ p ρ) (f-⟦⟧ (p :^ k) ρ))
  f-⟦⟧ (:- p) ρ = trans (f-neg _) (cong -_ (f-⟦⟧ p ρ))
