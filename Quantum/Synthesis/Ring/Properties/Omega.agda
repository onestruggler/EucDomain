-- If A is a commutative ring, then so is A [ω] (with the ring
-- operations of the instances in Quantum.Synthesis.Ring).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Omega where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin.Base using (zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; trans)

open import Instances
open import Quantum.Synthesis.Ring using (_[ω] ; Omega ; SemiRingOmega ; RingOmega ; AdjointOmega ; Adjoint2Omega)
open import Quantum.Synthesis.Ring.Properties.Common using (CRLaws ; isCommutativeRing-from-laws)
import Quantum.Synthesis.Ring.Properties.Poly as Poly
import Quantum.Synthesis.Ring.Properties.Hom as Hom
open Hom using (IsRingEndo ; IsInvolutiveRingEndo)

open _[ω] using (om-a ; om-b ; om-c ; om-d)

cong₄ : ∀ {B C : Set} (f : B -> B -> B -> B -> C) {x x' y y' z z' w w'} ->
        x ≡ x' -> y ≡ y' -> z ≡ z' -> w ≡ w' -> f x y z w ≡ f x' y' z' w'
cong₄ f refl refl refl refl = refl

module _ {A : Set} {{RA : Ring A}} (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  open Poly isCR using (Polynomial ; var ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; SemiRingPoly ; RingPoly)

  private
    -- The semantics of an expression of (Polynomial n) [ω].
    ⟦_⟧R : ∀ {n} -> Polynomial n [ω] -> Vec A n -> A [ω]
    ⟦ Omega a b c d ⟧R ρ = Omega (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ c ⟧ ρ) (⟦ d ⟧ ρ)

    -- Proving an equation of A [ω] componentwise with the solver.
    by : ∀ {n} (ρ : Vec A n) (e₁ e₂ : Polynomial n [ω]) ->
         ⟦ om-a e₁ ⟧↓ ρ ≡ ⟦ om-a e₂ ⟧↓ ρ -> ⟦ om-b e₁ ⟧↓ ρ ≡ ⟦ om-b e₂ ⟧↓ ρ ->
         ⟦ om-c e₁ ⟧↓ ρ ≡ ⟦ om-c e₂ ⟧↓ ρ -> ⟦ om-d e₁ ⟧↓ ρ ≡ ⟦ om-d e₂ ⟧↓ ρ ->
         ⟦ e₁ ⟧R ρ ≡ ⟦ e₂ ⟧R ρ
    by ρ (Omega a b c d) (Omega a' b' c' d') h₁ h₂ h₃ h₄ =
      cong₄ Omega (prove ρ a a' h₁) (prove ρ b b' h₂) (prove ρ c c' h₃) (prove ρ d d' h₄)

    -- Generic elements of (Polynomial n) [ω], and the corresponding
    -- environments. Each law below is proved with as many solver
    -- variables as it has generic elements (four per element), and no
    -- more: the solver's normal form Normal n is a sparse Horner form
    -- nested n deep, so its cost grows with the number of variables of
    -- its TYPE, not with the number of variables that actually occur.
    -- Using Polynomial 12 for a law about one or two elements (as an
    -- earlier version did) made this module three times slower.
    X₁ : Polynomial 4 [ω]
    X₁ = Omega (var zero) (var (suc zero)) (var (suc (suc zero))) (var (suc (suc (suc zero))))

    ρ₁ : A [ω] -> Vec A 4
    ρ₁ (Omega a b c d) = a ∷ b ∷ c ∷ d ∷ []

    X₂ Y₂ : Polynomial 8 [ω]
    X₂ = Omega (var zero) (var (suc zero)) (var (suc (suc zero))) (var (suc (suc (suc zero))))
    Y₂ = Omega (var (suc (suc (suc (suc zero))))) (var (suc (suc (suc (suc (suc zero))))))
               (var (suc (suc (suc (suc (suc (suc zero)))))))
               (var (suc (suc (suc (suc (suc (suc (suc zero))))))))

    ρ₂ : A [ω] -> A [ω] -> Vec A 8
    ρ₂ (Omega a b c d) (Omega e f g h) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []

    -- Three generic elements of (Polynomial 12) [ω], and the
    -- corresponding environment.
    X Y Z : Polynomial 12 [ω]
    X = Omega (var zero) (var (suc zero)) (var (suc (suc zero))) (var (suc (suc (suc zero))))
    Y = Omega (var (suc (suc (suc (suc zero))))) (var (suc (suc (suc (suc (suc zero))))))
              (var (suc (suc (suc (suc (suc (suc zero)))))))
              (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
    Z = Omega (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
              (var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
              (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
              (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

    ρ : A [ω] -> A [ω] -> A [ω] -> Vec A 12
    ρ (Omega a b c d) (Omega e f g h) (Omega i j k l) =
      a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ []

  +-assoc-Omega : ∀ (x y z : A [ω]) -> (x + y) + z ≡ x + (y + z)
  +-assoc-Omega x y z = by (ρ x y z) ((X + Y) + Z) (X + (Y + Z)) refl refl refl refl

  +-comm-Omega : ∀ (x y : A [ω]) -> x + y ≡ y + x
  +-comm-Omega x y = by (ρ₂ x y) (X₂ + Y₂) (Y₂ + X₂) refl refl refl refl

  +-identityˡ-Omega : ∀ (x : A [ω]) -> 0# + x ≡ x
  +-identityˡ-Omega x = by (ρ₁ x) (0# + X₁) X₁ refl refl refl refl

  -‿inverseˡ-Omega : ∀ (x : A [ω]) -> (- x) + x ≡ 0#
  -‿inverseˡ-Omega x = by (ρ₁ x) ((- X₁) + X₁) 0# refl refl refl refl

  *-assoc-Omega : ∀ (x y z : A [ω]) -> (x * y) * z ≡ x * (y * z)
  *-assoc-Omega x y z = by (ρ x y z) ((X * Y) * Z) (X * (Y * Z)) refl refl refl refl

  *-comm-Omega : ∀ (x y : A [ω]) -> x * y ≡ y * x
  *-comm-Omega x y = by (ρ₂ x y) (X₂ * Y₂) (Y₂ * X₂) refl refl refl refl

  *-identityˡ-Omega : ∀ (x : A [ω]) -> 1# * x ≡ x
  *-identityˡ-Omega x = by (ρ₁ x) (1# * X₁) X₁ refl refl refl refl

  distribʳ-Omega : ∀ (x y z : A [ω]) -> (y + z) * x ≡ y * x + z * x
  distribʳ-Omega x y z = by (ρ x y z) ((Y + Z) * X) (Y * X + Z * X) refl refl refl refl

  isCommutativeRing-Omega : IsCommutativeRing _≡_ _+_ _*_ -_ 0# (1# {A [ω]})
  isCommutativeRing-Omega = isCommutativeRing-from-laws _ _ _ _ _ record
    { +-assoc = +-assoc-Omega
    ; +-comm = +-comm-Omega
    ; +-identityˡ = +-identityˡ-Omega
    ; -‿inverseˡ = -‿inverseˡ-Omega
    ; *-assoc = *-assoc-Omega
    ; *-comm = *-comm-Omega
    ; *-identityˡ = *-identityˡ-Omega
    ; distribʳ = distribʳ-Omega
    }

  commutativeRing-Omega : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Omega = record { isCommutativeRing = isCommutativeRing-Omega }

  -- --------------------------------------------------------------------
  -- * Automorphisms

  private
    open import Algebra.Properties.Ring (CommutativeRing.ring (Poly.commutativeRing isCR))
      using (-‿involutive)

    adjP adj2P : ∀ {n} -> Polynomial n [ω] -> Polynomial n [ω]
    adjP (Omega a b c d) = Omega (- c) (- b) (- a) d
    adj2P (Omega a b c d) = Omega (- a) b (- c) d

  module _ {f : A -> A} (F : IsRingEndo f) where
    open Hom.Laws isCR F

    -- The complex conjugation, resp. the √2-conjugation, composed with
    -- f (applied componentwise).
    conj-Omega conj2-Omega : A [ω] -> A [ω]
    conj-Omega (Omega a b c d) = Omega (- f c) (- f b) (- f a) (f d)
    conj2-Omega (Omega a b c d) = Omega (- f a) (f b) (- f c) (f d)

    conj-Omega-isRingEndo : IsRingEndo conj-Omega
    conj-Omega-isRingEndo = record
      { f-+ = λ x y -> trans
          (cong₄ Omega (cong -_ (f-⟦⟧ (om-c (X₂ + Y₂)) (ρ₂ x y))) (cong -_ (f-⟦⟧ (om-b (X₂ + Y₂)) (ρ₂ x y)))
                       (cong -_ (f-⟦⟧ (om-a (X₂ + Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-d (X₂ + Y₂)) (ρ₂ x y)))
          (by (map f (ρ₂ x y)) (adjP (X₂ + Y₂)) (adjP X₂ + adjP Y₂) refl refl refl refl)
      ; f-* = λ x y -> trans
          (cong₄ Omega (cong -_ (f-⟦⟧ (om-c (X₂ * Y₂)) (ρ₂ x y))) (cong -_ (f-⟦⟧ (om-b (X₂ * Y₂)) (ρ₂ x y)))
                       (cong -_ (f-⟦⟧ (om-a (X₂ * Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-d (X₂ * Y₂)) (ρ₂ x y)))
          (by (map f (ρ₂ x y)) (adjP (X₂ * Y₂)) (adjP X₂ * adjP Y₂) refl refl refl refl)
      ; f-1 = trans (cong₄ Omega (cong -_ f-0) (cong -_ f-0) (cong -_ f-0) f-1)
                    (by [] (Omega (- 0#) (- 0#) (- 0#) 1#) 1# refl refl refl refl) }

    conj2-Omega-isRingEndo : IsRingEndo conj2-Omega
    conj2-Omega-isRingEndo = record
      { f-+ = λ x y -> trans
          (cong₄ Omega (cong -_ (f-⟦⟧ (om-a (X₂ + Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-b (X₂ + Y₂)) (ρ₂ x y))
                       (cong -_ (f-⟦⟧ (om-c (X₂ + Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-d (X₂ + Y₂)) (ρ₂ x y)))
          (by (map f (ρ₂ x y)) (adj2P (X₂ + Y₂)) (adj2P X₂ + adj2P Y₂) refl refl refl refl)
      ; f-* = λ x y -> trans
          (cong₄ Omega (cong -_ (f-⟦⟧ (om-a (X₂ * Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-b (X₂ * Y₂)) (ρ₂ x y))
                       (cong -_ (f-⟦⟧ (om-c (X₂ * Y₂)) (ρ₂ x y))) (f-⟦⟧ (om-d (X₂ * Y₂)) (ρ₂ x y)))
          (by (map f (ρ₂ x y)) (adj2P (X₂ * Y₂)) (adj2P X₂ * adj2P Y₂) refl refl refl refl)
      ; f-1 = trans (cong₄ Omega (cong -_ f-0) f-0 (cong -_ f-0) f-1)
                    (by [] (Omega (- 0#) 0# (- 0#) 1#) 1# refl refl refl refl) }

    module _ (inv : ∀ a -> f (f a) ≡ a) where
      private
        nn : ∀ a -> - f (- f a) ≡ a
        nn a = trans (cong -_ (f-neg _)) (trans (-‿involutive _) (inv a))

      conj-Omega-involutive : ∀ x -> conj-Omega (conj-Omega x) ≡ x
      conj-Omega-involutive x = cong₄ Omega (nn _) (nn _) (nn _) (inv _)

      conj2-Omega-involutive : ∀ x -> conj2-Omega (conj2-Omega x) ≡ x
      conj2-Omega-involutive x = cong₄ Omega (nn _) (inv _) (nn _) (inv _)

  -- If adj (resp. adj2) is an involutive automorphism of A, then adj
  -- (resp. adj2) is one of A [ω].
  adj-Omega : {{_ : Adjoint A}} -> IsInvolutiveRingEndo {A} adj -> IsInvolutiveRingEndo {A [ω]} adj
  adj-Omega F = record
    { isRingEndo = conj-Omega-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = conj-Omega-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }

  adj2-Omega : {{_ : Adjoint2 A}} -> IsInvolutiveRingEndo {A} adj2 -> IsInvolutiveRingEndo {A [ω]} adj2
  adj2-Omega F = record
    { isRingEndo = conj2-Omega-isRingEndo (IsInvolutiveRingEndo.isRingEndo F)
    ; involutive = conj2-Omega-involutive (IsInvolutiveRingEndo.isRingEndo F) (IsInvolutiveRingEndo.involutive F) }
