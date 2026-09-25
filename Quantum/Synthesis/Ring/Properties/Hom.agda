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
open import Algebra.Structures using (IsCommutativeRing ; IsCommutativeMonoid)
open import Algebra.Bundles using (RawRing ; RawMonoid)
import Algebra.Morphism.Structures as Standard
import Typeclasses.Properties as Power
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Vec.Base using (Vec ; map ; lookup)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

-- Maps between different carriers. These records use the instance operations
-- and do not require elaborating a ring solver or a bundled ring.
record IsMultiplicativeHom {A B : Set} {{SA : SemiRing A}} {{SB : SemiRing B}}
                          (f : A -> B) : Set where
  field
    f-* : ∀ x y -> f (x * y) ≡ f x * f y
    f-1 : f 1# ≡ 1#

record IsRingHom {A B : Set} {{RA : Ring A}} {{RB : Ring B}} (f : A -> B) : Set where
  field
    multiplicative : IsMultiplicativeHom f
    f-+ : ∀ x y -> f (x + y) ≡ f x + f y
    f-0 : f 0# ≡ 0#
    f-neg : ∀ x -> f (- x) ≡ - f x
  open IsMultiplicativeHom multiplicative public

  f-sub : ∀ x y -> f (x - y) ≡ f x - f y
  f-sub x y = trans (f-+ x (- y)) (cong (λ z -> f x + z) (f-neg y))

compose-multiplicative : {A B C : Set} {{SA : SemiRing A}} {{SB : SemiRing B}} {{SC : SemiRing C}}
  {f : A -> B} {g : B -> C} -> IsMultiplicativeHom g -> IsMultiplicativeHom f ->
  IsMultiplicativeHom (λ x -> g (f x))
compose-multiplicative {f = f} {g} G F = record
  { f-* = λ x y -> trans (cong g (IsMultiplicativeHom.f-* F x y)) (IsMultiplicativeHom.f-* G (f x) (f y))
  ; f-1 = trans (cong g (IsMultiplicativeHom.f-1 F)) (IsMultiplicativeHom.f-1 G) }

compose-ring : {A B C : Set} {{RA : Ring A}} {{RB : Ring B}} {{RC : Ring C}}
  {f : A -> B} {g : B -> C} -> IsRingHom g -> IsRingHom f -> IsRingHom (λ x -> g (f x))
compose-ring {f = f} {g} G F = record
  { multiplicative = compose-multiplicative (IsRingHom.multiplicative G) (IsRingHom.multiplicative F)
  ; f-+ = λ x y -> trans (cong g (IsRingHom.f-+ F x y)) (IsRingHom.f-+ G (f x) (f y))
  ; f-0 = trans (cong g (IsRingHom.f-0 F)) (IsRingHom.f-0 G)
  ; f-neg = λ x -> trans (cong g (IsRingHom.f-neg F x)) (IsRingHom.f-neg G (f x)) }

-- Interoperate with the standard library without duplicating ring laws.
instanceRawRing : (A : Set) {{RA : Ring A}} -> RawRing _ _
instanceRawRing A = record
  { Carrier = A ; _≈_ = _≡_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = -_ ; 0# = 0# ; 1# = 1# }

instanceRawMonoid : (A : Set) {{SA : SemiRing A}} -> RawMonoid _ _
instanceRawMonoid A = record { Carrier = A ; _≈_ = _≡_ ; _∙_ = _*_ ; ε = 1# }

toRingHomomorphism : {A B : Set} {{RA : Ring A}} {{RB : Ring B}} {f : A -> B} ->
  IsRingHom f -> Standard.IsRingHomomorphism (instanceRawRing A) (instanceRawRing B) f
toRingHomomorphism {f = f} F = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = cong f } ; homo = IsRingHom.f-+ F }
        ; ε-homo = IsRingHom.f-0 F }
      ; *-homo = IsRingHom.f-* F }
    ; 1#-homo = IsRingHom.f-1 F }
  ; -‿homo = IsRingHom.f-neg F }

toMonoidHomomorphism : {A B : Set} {{SA : SemiRing A}} {{SB : SemiRing B}} {f : A -> B} ->
  IsMultiplicativeHom f -> Standard.IsMonoidHomomorphism (instanceRawMonoid A) (instanceRawMonoid B) f
toMonoidHomomorphism {f = f} F = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = cong f } ; homo = IsMultiplicativeHom.f-* F }
  ; ε-homo = IsMultiplicativeHom.f-1 F }

module MultiplicativeLaws {A B : Set} {{SA : SemiRing A}} {{SB : SemiRing B}}
  (la : IsCommutativeMonoid (_≡_ {A = A}) _*_ 1#)
  (lb : IsCommutativeMonoid (_≡_ {A = B}) _*_ 1#)
  {f : A -> B} (F : IsMultiplicativeHom f) where
  open Power.MapPowers {A} {B} {{SA}} {{SB}} la lb f
    (IsMultiplicativeHom.f-1 F) (IsMultiplicativeHom.f-* F) public
    using () renaming (map-power to f-^)

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

  isRingHom : IsRingHom f
  isRingHom = record
    { multiplicative = record { f-* = f-* ; f-1 = f-1 }
    ; f-+ = f-+ ; f-0 = f-0 ; f-neg = f-neg }

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
