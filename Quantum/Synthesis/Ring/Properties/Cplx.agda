-- If A is a commutative ring, then so is A [i] (with the ring
-- operations of the instances in Quantum.Synthesis.Ring).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Cplx where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin.Base using (zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂ ; cong ; trans)

open import Instances
open import Quantum.Synthesis.Ring using (_[i] ; Cplx ; SemiRingCplx ; RingCplx ; AdjointCplx ; Adjoint2Cplx)
open import Quantum.Synthesis.Ring.Properties.Common using (CRLaws ; isCommutativeRing-from-laws)
import Quantum.Synthesis.Ring.Properties.Poly as Poly
import Quantum.Synthesis.Ring.Properties.Hom as Hom
open Hom using (IsRingEndo ; IsInvolutiveRingEndo)

open _[i] using (re ; im)

module _ {A : Set} {{RA : Ring A}} (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  open Poly isCR using (Polynomial ; var ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; SemiRingPoly ; RingPoly)

  private
    -- The semantics of an expression of (Polynomial n) [i].
    ⟦_⟧R : ∀ {n} -> Polynomial n [i] -> Vec A n -> A [i]
    ⟦ Cplx a b ⟧R ρ = Cplx (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)

    -- Proving an equation of A [i] componentwise with the solver.
    by : ∀ {n} (ρ : Vec A n) (e₁ e₂ : Polynomial n [i]) ->
         ⟦ re e₁ ⟧↓ ρ ≡ ⟦ re e₂ ⟧↓ ρ -> ⟦ im e₁ ⟧↓ ρ ≡ ⟦ im e₂ ⟧↓ ρ ->
         ⟦ e₁ ⟧R ρ ≡ ⟦ e₂ ⟧R ρ
    by ρ (Cplx a b) (Cplx c d) h₁ h₂ = cong₂ Cplx (prove ρ a c h₁) (prove ρ b d h₂)

    -- Three generic elements of (Polynomial 6) [i], and the
    -- corresponding environment.
    X Y Z : Polynomial 6 [i]
    X = Cplx (var zero) (var (suc zero))
    Y = Cplx (var (suc (suc zero))) (var (suc (suc (suc zero))))
    Z = Cplx (var (suc (suc (suc (suc zero))))) (var (suc (suc (suc (suc (suc zero))))))

    ρ : A [i] -> A [i] -> A [i] -> Vec A 6
    ρ (Cplx a b) (Cplx c d) (Cplx e f) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []

  +-assoc-Cplx : ∀ (x y z : A [i]) -> (x + y) + z ≡ x + (y + z)
  +-assoc-Cplx x y z = by (ρ x y z) ((X + Y) + Z) (X + (Y + Z)) refl refl

  +-comm-Cplx : ∀ (x y : A [i]) -> x + y ≡ y + x
  +-comm-Cplx x y = by (ρ x y y) (X + Y) (Y + X) refl refl

  +-identityˡ-Cplx : ∀ (x : A [i]) -> 0# + x ≡ x
  +-identityˡ-Cplx x = by (ρ x x x) (0# + X) X refl refl

  -‿inverseˡ-Cplx : ∀ (x : A [i]) -> (- x) + x ≡ 0#
  -‿inverseˡ-Cplx x = by (ρ x x x) ((- X) + X) 0# refl refl

  *-assoc-Cplx : ∀ (x y z : A [i]) -> (x * y) * z ≡ x * (y * z)
  *-assoc-Cplx x y z = by (ρ x y z) ((X * Y) * Z) (X * (Y * Z)) refl refl

  *-comm-Cplx : ∀ (x y : A [i]) -> x * y ≡ y * x
  *-comm-Cplx x y = by (ρ x y y) (X * Y) (Y * X) refl refl

  *-identityˡ-Cplx : ∀ (x : A [i]) -> 1# * x ≡ x
  *-identityˡ-Cplx x = by (ρ x x x) (1# * X) X refl refl

  distribʳ-Cplx : ∀ (x y z : A [i]) -> (y + z) * x ≡ y * x + z * x
  distribʳ-Cplx x y z = by (ρ x y z) ((Y + Z) * X) (Y * X + Z * X) refl refl

  isCommutativeRing-Cplx : IsCommutativeRing _≡_ _+_ _*_ -_ 0# (1# {A [i]})
  isCommutativeRing-Cplx = isCommutativeRing-from-laws _ _ _ _ _ record
    { +-assoc = +-assoc-Cplx
    ; +-comm = +-comm-Cplx
    ; +-identityˡ = +-identityˡ-Cplx
    ; -‿inverseˡ = -‿inverseˡ-Cplx
    ; *-assoc = *-assoc-Cplx
    ; *-comm = *-comm-Cplx
    ; *-identityˡ = *-identityˡ-Cplx
    ; distribʳ = distribʳ-Cplx
    }

  commutativeRing-Cplx : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Cplx = record { isCommutativeRing = isCommutativeRing-Cplx }

  -- --------------------------------------------------------------------
  -- * Automorphisms

  private
    open import Algebra.Properties.Ring (CommutativeRing.ring (Poly.commutativeRing isCR))
      using (-‿involutive)

    conjP : ∀ {n} -> Polynomial n [i] -> Polynomial n [i]
    conjP (Cplx a b) = Cplx a (- b)

  module _ {f : A -> A} (F : IsRingEndo f) where
    open Hom.Laws isCR F

    -- Applying f componentwise, and complex conjugation composed with f.
    map-Cplx conj-Cplx : A [i] -> A [i]
    map-Cplx (Cplx a b) = Cplx (f a) (f b)
    conj-Cplx (Cplx a b) = Cplx (f a) (- f b)

    map-Cplx-isRingEndo : IsRingEndo map-Cplx
    map-Cplx-isRingEndo = record
      { f-+ = λ x y -> cong₂ Cplx (f-⟦⟧ (re (X + Y)) (ρ x y y)) (f-⟦⟧ (im (X + Y)) (ρ x y y))
      ; f-* = λ x y -> cong₂ Cplx (f-⟦⟧ (re (X * Y)) (ρ x y y)) (f-⟦⟧ (im (X * Y)) (ρ x y y))
      ; f-1 = cong₂ Cplx f-1 f-0 }

    conj-Cplx-isRingEndo : IsRingEndo conj-Cplx
    conj-Cplx-isRingEndo = record
      { f-+ = λ x y -> trans
          (cong₂ Cplx (f-⟦⟧ (re (X + Y)) (ρ x y y)) (cong -_ (f-⟦⟧ (im (X + Y)) (ρ x y y))))
          (by (map f (ρ x y y)) (conjP (X + Y)) (conjP X + conjP Y) refl refl)
      ; f-* = λ x y -> trans
          (cong₂ Cplx (f-⟦⟧ (re (X * Y)) (ρ x y y)) (cong -_ (f-⟦⟧ (im (X * Y)) (ρ x y y))))
          (by (map f (ρ x y y)) (conjP (X * Y)) (conjP X * conjP Y) refl refl)
      ; f-1 = trans (cong₂ Cplx f-1 (cong -_ f-0)) (by (ρ 0# 0# 0#) (Cplx 1# (- 0#)) 1# refl refl) }

    module _ (inv : ∀ a -> f (f a) ≡ a) where
      map-Cplx-involutive : ∀ x -> map-Cplx (map-Cplx x) ≡ x
      map-Cplx-involutive x = cong₂ Cplx (inv _) (inv _)

      conj-Cplx-involutive : ∀ x -> conj-Cplx (conj-Cplx x) ≡ x
      conj-Cplx-involutive x =
        cong₂ Cplx (inv _) (trans (cong -_ (f-neg _)) (trans (-‿involutive _) (inv _)))

  -- If adj is an involutive automorphism of A, then adj (which is the
  -- complex conjugation composed with adj of A) is one of A [i];
  -- similarly for adj2.
  adj-Cplx : {{_ : Adjoint A}} -> IsInvolutiveRingEndo {A} adj -> IsInvolutiveRingEndo {A [i]} adj
  adj-Cplx F = record
    { isRingEndo = conj-Cplx-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = conj-Cplx-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }

  adj2-Cplx : {{_ : Adjoint2 A}} -> IsInvolutiveRingEndo {A} adj2 -> IsInvolutiveRingEndo {A [i]} adj2
  adj2-Cplx F = record
    { isRingEndo = map-Cplx-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = map-Cplx-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }
