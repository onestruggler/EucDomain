{-# OPTIONS --safe --without-K #-}

-- γ-presentations of matrices: a numerator over ℤ[i] together with an
-- exponent k, standing for numerator / γ^k. Two presentations are
-- equivalent when they cross-multiply to the same numerator.
module GauInt.Matrix.Presentation where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_+_; _*_)
open import GauInt.Gamma using (powγ; powγ-add; powγ-cancel)
open import GauInt.Algebra.Swap using (swap; product-scale)
open import GauInt.Matrix
open import Data.Nat using (ℕ)
import Data.Nat.Properties as NP
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym; trans)

record ScaledMatrix (n : ℕ) : Set where
  constructor scaled
  field
    numerator : Mat n
    exponent : ℕ
open ScaledMatrix public

Equivalent : ∀ {n} → ScaledMatrix n → ScaledMatrix n → Set
Equivalent A B = scale (powγ (exponent B)) (numerator A) ≈ scale (powγ (exponent A)) (numerator B)

equivalent-refl : ∀ {n} (A : ScaledMatrix n) → Equivalent A A
equivalent-refl A = ≈-refl

equivalent-sym : ∀ {n} {A B : ScaledMatrix n} → Equivalent A B → Equivalent B A
equivalent-sym = ≈-sym

equivalent-trans : ∀ {n} {A B C : ScaledMatrix n} → Equivalent A B → Equivalent B C → Equivalent A C
equivalent-trans {A = A} {B} {C} h k i j = powγ-cancel (exponent B)
  (trans (swap (powγ (exponent B)) (powγ (exponent C)) (numerator A i j))
    (trans (cong (powγ (exponent C) *_) (h i j))
      (trans (swap (powγ (exponent C)) (powγ (exponent A)) (numerator B i j))
        (trans (cong (powγ (exponent A) *_) (k i j))
          (swap (powγ (exponent A)) (powγ (exponent B)) (numerator C i j))))))

equivalent? : ∀ {n} (A B : ScaledMatrix n) → Dec (Equivalent A B)
equivalent? A B = matrixEq (scale (powγ (exponent B)) (numerator A)) (scale (powγ (exponent A)) (numerator B))

scaledMul : ∀ {n} → ScaledMatrix n → ScaledMatrix n → ScaledMatrix n
scaledMul A B = scaled (mul (numerator A) (numerator B)) (exponent A + exponent B)

equivalent-mul : ∀ {n} {A A′ B B′ : ScaledMatrix n} →
  Equivalent A A′ → Equivalent B B′ → Equivalent (scaledMul A B) (scaledMul A′ B′)
equivalent-mul {n} {A = A} {A′} {B} {B′} h k i j =
  trans (sym (sum-mulˡ {n} (powγ (exponent A′ + exponent B′)) (λ t → numerator A i t * numerator B t j)))
  (trans (sum-cong {n} term) (sum-mulˡ {n} (powγ (exponent A + exponent B)) (λ t → numerator A′ i t * numerator B′ t j)))
  where
  term : ∀ t → powγ (exponent A′ + exponent B′) * (numerator A i t * numerator B t j)
    ≡ powγ (exponent A + exponent B) * (numerator A′ i t * numerator B′ t j)
  term t = trans (cong (_* (numerator A i t * numerator B t j)) (powγ-add (exponent A′) (exponent B′)))
    (trans (product-scale (powγ (exponent A′)) (powγ (exponent B′)) (numerator A i t) (numerator B t j))
      (trans (cong₂ _*_ (h i t) (k t j))
        (trans (sym (product-scale (powγ (exponent A)) (powγ (exponent B)) (numerator A′ i t) (numerator B′ t j)))
          (cong (_* (numerator A′ i t * numerator B′ t j)) (sym (powγ-add (exponent A) (exponent B)))))))

scaled-assoc : ∀ {n} (A B C : ScaledMatrix n) →
  Equivalent (scaledMul (scaledMul A B) C) (scaledMul A (scaledMul B C))
scaled-assoc A B C i j = trans
  (cong (powγ (exponent A + (exponent B + exponent C)) *_) (mul-assoc (numerator A) (numerator B) (numerator C) i j))
  (cong (λ k → powγ k * mul (numerator A) (mul (numerator B) (numerator C)) i j)
    (sym (NP.+-assoc (exponent A) (exponent B) (exponent C))))

idS : ∀ {n} → ScaledMatrix n
idS = scaled identity 0

identity-product : ∀ {n} (A : ScaledMatrix n) → Equivalent (scaledMul (scaled identity 0) A) A
identity-product A = scale-cong (powγ (exponent A)) (identity-mul (numerator A))

right-identity : ∀ {n} (A : ScaledMatrix n) → Equivalent (scaledMul A idS) A
right-identity A i j = trans (cong (powγ (exponent A) *_) (mul-identity (numerator A) i j))
  (cong (λ k → powγ k * numerator A i j) (sym (NP.+-identityʳ (exponent A))))

middle-assoc : ∀ {n} (A B C D : ScaledMatrix n) →
  Equivalent (scaledMul (scaledMul A B) (scaledMul C D)) (scaledMul A (scaledMul (scaledMul B C) D))
middle-assoc A B C D = equivalent-trans {A = scaledMul (scaledMul A B) (scaledMul C D)}
  {B = scaledMul A (scaledMul B (scaledMul C D))} {C = scaledMul A (scaledMul (scaledMul B C) D)}
  (scaled-assoc A B (scaledMul C D))
  (equivalent-mul {A = A} {A′ = A} {B = scaledMul B (scaledMul C D)} {B′ = scaledMul (scaledMul B C) D}
    (equivalent-refl A) (equivalent-sym {A = scaledMul (scaledMul B C) D} {B = scaledMul B (scaledMul C D)} (scaled-assoc B C D)))

cancel-middle : ∀ {n} (A B C D : ScaledMatrix n) → Equivalent (scaledMul B C) idS →
  Equivalent (scaledMul (scaledMul A B) (scaledMul C D)) (scaledMul A D)
cancel-middle A B C D hi = equivalent-trans {A = scaledMul (scaledMul A B) (scaledMul C D)}
  {B = scaledMul A (scaledMul (scaledMul B C) D)} {C = scaledMul A D} (middle-assoc A B C D)
  (equivalent-mul {A = A} {A′ = A} {B = scaledMul (scaledMul B C) D} {B′ = D} (equivalent-refl A)
    (equivalent-trans {A = scaledMul (scaledMul B C) D} {B = scaledMul idS D} {C = D}
      (equivalent-mul {A = scaledMul B C} {A′ = idS} {B = D} {B′ = D} hi (equivalent-refl D)) (identity-product D)))
