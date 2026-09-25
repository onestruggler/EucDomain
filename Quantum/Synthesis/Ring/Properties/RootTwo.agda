-- If A is a commutative ring, then so is A [√2] (with the ring
-- operations of the instances in Quantum.Synthesis.Ring).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.RootTwo where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin.Base using (zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂ ; cong ; trans)

open import Instances
open import Quantum.Synthesis.Ring using (_[√2] ; RootTwo ; SemiRingRootTwo ; RingRootTwo ; AdjointRootTwo ; Adjoint2RootTwo)
open import Quantum.Synthesis.Ring.Properties.Common using (CRLaws ; isCommutativeRing-from-laws)
import Quantum.Synthesis.Ring.Properties.Poly as Poly
import Quantum.Synthesis.Ring.Properties.Hom as Hom
open Hom using (IsRingEndo ; IsInvolutiveRingEndo)

open _[√2] using (rt-a ; rt-b)

module _ {A : Set} {{RA : Ring A}} (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  open Poly isCR using (Polynomial ; var ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; SemiRingPoly ; RingPoly)

  private
    -- The semantics of an expression of (Polynomial n) [√2].
    ⟦_⟧R : ∀ {n} -> Polynomial n [√2] -> Vec A n -> A [√2]
    ⟦ RootTwo a b ⟧R ρ = RootTwo (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)

    -- Proving an equation of A [√2] componentwise with the solver.
    by : ∀ {n} (ρ : Vec A n) (e₁ e₂ : Polynomial n [√2]) ->
         ⟦ rt-a e₁ ⟧↓ ρ ≡ ⟦ rt-a e₂ ⟧↓ ρ -> ⟦ rt-b e₁ ⟧↓ ρ ≡ ⟦ rt-b e₂ ⟧↓ ρ ->
         ⟦ e₁ ⟧R ρ ≡ ⟦ e₂ ⟧R ρ
    by ρ (RootTwo a b) (RootTwo c d) h₁ h₂ = cong₂ RootTwo (prove ρ a c h₁) (prove ρ b d h₂)

    -- Three generic elements of (Polynomial 6) [√2], and the
    -- corresponding environment.
    X Y Z : Polynomial 6 [√2]
    X = RootTwo (var zero) (var (suc zero))
    Y = RootTwo (var (suc (suc zero))) (var (suc (suc (suc zero))))
    Z = RootTwo (var (suc (suc (suc (suc zero))))) (var (suc (suc (suc (suc (suc zero))))))

    ρ : A [√2] -> A [√2] -> A [√2] -> Vec A 6
    ρ (RootTwo a b) (RootTwo c d) (RootTwo e f) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []

  +-assoc-RootTwo : ∀ (x y z : A [√2]) -> (x + y) + z ≡ x + (y + z)
  +-assoc-RootTwo x y z = by (ρ x y z) ((X + Y) + Z) (X + (Y + Z)) refl refl

  +-comm-RootTwo : ∀ (x y : A [√2]) -> x + y ≡ y + x
  +-comm-RootTwo x y = by (ρ x y y) (X + Y) (Y + X) refl refl

  +-identityˡ-RootTwo : ∀ (x : A [√2]) -> 0# + x ≡ x
  +-identityˡ-RootTwo x = by (ρ x x x) (0# + X) X refl refl

  -‿inverseˡ-RootTwo : ∀ (x : A [√2]) -> (- x) + x ≡ 0#
  -‿inverseˡ-RootTwo x = by (ρ x x x) ((- X) + X) 0# refl refl

  *-assoc-RootTwo : ∀ (x y z : A [√2]) -> (x * y) * z ≡ x * (y * z)
  *-assoc-RootTwo x y z = by (ρ x y z) ((X * Y) * Z) (X * (Y * Z)) refl refl

  *-comm-RootTwo : ∀ (x y : A [√2]) -> x * y ≡ y * x
  *-comm-RootTwo x y = by (ρ x y y) (X * Y) (Y * X) refl refl

  *-identityˡ-RootTwo : ∀ (x : A [√2]) -> 1# * x ≡ x
  *-identityˡ-RootTwo x = by (ρ x x x) (1# * X) X refl refl

  distribʳ-RootTwo : ∀ (x y z : A [√2]) -> (y + z) * x ≡ y * x + z * x
  distribʳ-RootTwo x y z = by (ρ x y z) ((Y + Z) * X) (Y * X + Z * X) refl refl

  isCommutativeRing-RootTwo : IsCommutativeRing _≡_ _+_ _*_ -_ 0# (1# {A [√2]})
  isCommutativeRing-RootTwo = isCommutativeRing-from-laws _ _ _ _ _ record
    { +-assoc = +-assoc-RootTwo
    ; +-comm = +-comm-RootTwo
    ; +-identityˡ = +-identityˡ-RootTwo
    ; -‿inverseˡ = -‿inverseˡ-RootTwo
    ; *-assoc = *-assoc-RootTwo
    ; *-comm = *-comm-RootTwo
    ; *-identityˡ = *-identityˡ-RootTwo
    ; distribʳ = distribʳ-RootTwo
    }

  commutativeRing-RootTwo : CommutativeRing 0ℓ 0ℓ
  commutativeRing-RootTwo = record { isCommutativeRing = isCommutativeRing-RootTwo }

  -- --------------------------------------------------------------------
  -- * Automorphisms

  private
    open import Algebra.Properties.Ring (CommutativeRing.ring (Poly.commutativeRing isCR))
      using (-‿involutive)

    conjP : ∀ {n} -> Polynomial n [√2] -> Polynomial n [√2]
    conjP (RootTwo a b) = RootTwo a (- b)

  module _ {f : A -> A} (F : IsRingEndo f) where
    open Hom.Laws isCR F

    -- Applying f componentwise, and √2-conjugation composed with f.
    map-RootTwo conj-RootTwo : A [√2] -> A [√2]
    map-RootTwo (RootTwo a b) = RootTwo (f a) (f b)
    conj-RootTwo (RootTwo a b) = RootTwo (f a) (- f b)

    map-RootTwo-isRingEndo : IsRingEndo map-RootTwo
    map-RootTwo-isRingEndo = record
      { f-+ = λ x y -> cong₂ RootTwo (f-⟦⟧ (rt-a (X + Y)) (ρ x y y)) (f-⟦⟧ (rt-b (X + Y)) (ρ x y y))
      ; f-* = λ x y -> cong₂ RootTwo (f-⟦⟧ (rt-a (X * Y)) (ρ x y y)) (f-⟦⟧ (rt-b (X * Y)) (ρ x y y))
      ; f-1 = cong₂ RootTwo f-1 f-0 }

    conj-RootTwo-isRingEndo : IsRingEndo conj-RootTwo
    conj-RootTwo-isRingEndo = record
      { f-+ = λ x y -> trans
          (cong₂ RootTwo (f-⟦⟧ (rt-a (X + Y)) (ρ x y y)) (cong -_ (f-⟦⟧ (rt-b (X + Y)) (ρ x y y))))
          (by (map f (ρ x y y)) (conjP (X + Y)) (conjP X + conjP Y) refl refl)
      ; f-* = λ x y -> trans
          (cong₂ RootTwo (f-⟦⟧ (rt-a (X * Y)) (ρ x y y)) (cong -_ (f-⟦⟧ (rt-b (X * Y)) (ρ x y y))))
          (by (map f (ρ x y y)) (conjP (X * Y)) (conjP X * conjP Y) refl refl)
      ; f-1 = trans (cong₂ RootTwo f-1 (cong -_ f-0)) (by (ρ 0# 0# 0#) (RootTwo 1# (- 0#)) 1# refl refl) }

    module _ (inv : ∀ a -> f (f a) ≡ a) where
      map-RootTwo-involutive : ∀ x -> map-RootTwo (map-RootTwo x) ≡ x
      map-RootTwo-involutive x = cong₂ RootTwo (inv _) (inv _)

      conj-RootTwo-involutive : ∀ x -> conj-RootTwo (conj-RootTwo x) ≡ x
      conj-RootTwo-involutive x =
        cong₂ RootTwo (inv _) (trans (cong -_ (f-neg _)) (trans (-‿involutive _) (inv _)))

  -- If adj is an involutive automorphism of A, then adj is one of
  -- A [√2]; similarly for adj2 (which is the √2-conjugation composed
  -- with adj2 of A).
  adj-RootTwo : {{_ : Adjoint A}} -> IsInvolutiveRingEndo {A} adj -> IsInvolutiveRingEndo {A [√2]} adj
  adj-RootTwo F = record
    { isRingEndo = map-RootTwo-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = map-RootTwo-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }

  adj2-RootTwo : {{_ : Adjoint2 A}} -> IsInvolutiveRingEndo {A} adj2 -> IsInvolutiveRingEndo {A [√2]} adj2
  adj2-RootTwo F = record
    { isRingEndo = conj-RootTwo-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = conj-RootTwo-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }

  -- The constant-coefficient embedding into the extension.
  lift-RootTwo : A -> A [√2]
  lift-RootTwo a = RootTwo a 0#

  lift-RootTwo-isRingHom : Hom.IsRingHom lift-RootTwo
  lift-RootTwo-isRingHom = record
    { multiplicative = record
      { f-* = λ a b -> by (a ∷ b ∷ []) (RootTwo ((var zero) * (var (suc zero))) 0#) ((RootTwo (var zero) 0#) * (RootTwo (var (suc zero)) 0#)) refl refl
      ; f-1 = refl }
    ; f-+ = λ a b -> by (a ∷ b ∷ []) (RootTwo ((var zero) + (var (suc zero))) 0#) ((RootTwo (var zero) 0#) + (RootTwo (var (suc zero)) 0#)) refl refl
    ; f-0 = refl
    ; f-neg = λ a -> by (a ∷ []) (RootTwo (- (var zero)) 0#) (- (RootTwo (var zero) 0#)) refl refl }
