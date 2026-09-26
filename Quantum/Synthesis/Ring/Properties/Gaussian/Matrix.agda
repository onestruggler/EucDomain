{-# OPTIONS --safe --without-K #-}

-- Dimension-independent counterpart of Lean's Mat4/Mat6 operations.
-- Matrix equality is pointwise, avoiding a function-extensionality axiom.
module Quantum.Synthesis.Ring.Properties.Gaussian.Matrix where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Algebra
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
import Data.Vec.Functional as Vector
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec)
open import Finite.Check using (decAll)
open import Algebra.Bundles using (module CommutativeRing)
open CommutativeRing gaussianRing using () renaming (zeroˡ to *-zeroˡ; zeroʳ to *-zeroʳ)

Mat : ℕ → Set
Mat n = Fin n → Fin n → ZComplex

infix 4 _≈_
_≈_ : ∀ {n} → Mat n → Mat n → Set
A ≈ B = ∀ i j → A i j ≡ B i j

≈-refl : ∀ {n} {M : Mat n} → M ≈ M
≈-refl i j = refl

≈-sym : ∀ {n} {A B : Mat n} → A ≈ B → B ≈ A
≈-sym h i j = sym (h i j)

≈-trans : ∀ {n} {A B C : Mat n} → A ≈ B → B ≈ C → A ≈ C
≈-trans h k i j = trans (h i j) (k i j)

matrixEq : ∀ {n} (A B : Mat n) → Dec (A ≈ B)
matrixEq {n} A B = decAll n _ (λ i → decAll n _ (λ j → A i j TC.≟ B i j))

sum : ∀ {n} → (Fin n → ZComplex) → ZComplex
sum = Vector.foldr _+_ 0#

sum-cong : ∀ {n} {f g : Fin n → ZComplex} → (∀ i → f i ≡ g i) → sum f ≡ sum g
sum-cong {zero} h = refl
sum-cong {suc n} h = cong₂ _+_ (h zero) (sum-cong (λ i → h (suc i)))

sum-zero : ∀ n → sum {n} (λ _ → 0#) ≡ 0#
sum-zero zero = refl
sum-zero (suc n) = trans (cong (0# TC.+_) (sum-zero n)) (+-identityˡ 0#)

shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
shuffle = GaussianSolver.solve 4 (λ a b c d →
  (a GaussianSolver.:+ b) GaussianSolver.:+ (c GaussianSolver.:+ d)
  GaussianSolver.:= (a GaussianSolver.:+ c) GaussianSolver.:+ (b GaussianSolver.:+ d)) refl

sum-add : ∀ {n} (f g : Fin n → ZComplex) → sum (λ i → f i + g i) ≡ sum f + sum g
sum-add {zero} f g = sym (+-identityˡ 0#)
sum-add {suc n} f g = trans
  (cong ((f zero + g zero) TC.+_) (sum-add (λ i → f (suc i)) (λ i → g (suc i))))
  (shuffle (f zero) (g zero) (sum (λ i → f (suc i))) (sum (λ i → g (suc i))))

sum-sub : ∀ {n} (f g : Fin n → ZComplex) → sum (λ i → f i - g i) ≡ sum f - sum g
sum-sub {zero} f g = refl
sum-sub {suc n} f g = trans (cong ((f zero - g zero) TC.+_) (sum-sub (λ i → f (suc i)) (λ i → g (suc i))))
  (solve 4 (λ a b c d → (a :- b) :+ (c :- d) := (a :+ c) :- (b :+ d)) refl
    (f zero) (g zero) (sum (λ i → f (suc i))) (sum (λ i → g (suc i))))
  where open GaussianSolver

sum-mulˡ : ∀ {n} z (f : Fin n → ZComplex) → sum (λ i → z * f i) ≡ z * sum f
sum-mulˡ {zero} z f = sym (*-zeroʳ z)
sum-mulˡ {suc n} z f = trans
  (cong (z * f zero TC.+_) (sum-mulˡ z (λ i → f (suc i))))
  (sym (*-distribˡ z (f zero) (sum (λ i → f (suc i)))))

sum-mulʳ : ∀ {n} z (f : Fin n → ZComplex) → sum (λ i → f i * z) ≡ sum f * z
sum-mulʳ z f = trans (sum-cong (λ i → *-comm (f i) z))
  (trans (sum-mulˡ z f) (*-comm z (sum f)))

sum-swap : ∀ {m n} (f : Fin m → Fin n → ZComplex) →
  sum (λ i → sum (f i)) ≡ sum (λ j → sum (λ i → f i j))
sum-swap {zero} {n} f = sym (sum-zero n)
sum-swap {suc m} {n} f = trans
  (cong (sum (f zero) TC.+_) (sum-swap (λ i j → f (suc i) j)))
  (sym (sum-add (f zero) (λ j → sum (λ i → f (suc i) j))))

delta : ∀ {n} → Fin n → Fin n → ZComplex
delta zero zero = 1#
delta zero (suc j) = 0#
delta (suc i) zero = 0#
delta (suc i) (suc j) = delta i j

identity : ∀ {n} → Mat n
identity = delta

mul : ∀ {n} → Mat n → Mat n → Mat n
mul A B i j = sum (λ k → A i k * B k j)

scale : ∀ {n} → ZComplex → Mat n → Mat n
scale z M i j = z * M i j

adjoint : ∀ {n} → Mat n → Mat n
adjoint M i j = TC.adj (M j i)

transpose : ∀ {n} → Mat n → Mat n
transpose M i j = M j i

gram : ∀ {n} → Mat n → Mat n
gram M = mul M (adjoint M)

mul-cong : ∀ {n} {A B C D : Mat n} → A ≈ B → C ≈ D → mul A C ≈ mul B D
mul-cong h k i j = sum-cong (λ x → cong₂ _*_ (h i x) (k x j))

scale-cong : ∀ {n} z {A B : Mat n} → A ≈ B → scale z A ≈ scale z B
scale-cong z h i j = cong (z *_) (h i j)

scale-scale : ∀ {n} z w (M : Mat n) → scale z (scale w M) ≈ scale (z * w) M
scale-scale z w M i j = sym (*-assoc z w (M i j))

mul-scaleˡ : ∀ {n} z (A B : Mat n) → mul (scale z A) B ≈ scale z (mul A B)
mul-scaleˡ z A B i j = trans (sum-cong (λ k → *-assoc z (A i k) (B k j)))
  (sum-mulˡ z (λ k → A i k * B k j))

mul-scaleʳ : ∀ {n} z (A B : Mat n) → mul A (scale z B) ≈ scale z (mul A B)
mul-scaleʳ z A B i j = trans
  (sum-cong (λ k → trans (sym (*-assoc (A i k) z (B k j)))
    (trans (cong (_* B k j) (*-comm (A i k) z)) (*-assoc z (A i k) (B k j)))))
  (sum-mulˡ z (λ k → A i k * B k j))

mul-scaled : ∀ {n} z w (M N : Mat n) → mul (scale z M) (scale w N) ≈ scale (z * w) (mul M N)
mul-scaled z w M N = ≈-trans (mul-scaleˡ z M (scale w N))
  (≈-trans (scale-cong z (mul-scaleʳ w M N)) (scale-scale z w (mul M N)))

mul-assoc : ∀ {n} (A B C : Mat n) → mul (mul A B) C ≈ mul A (mul B C)
mul-assoc A B C i j = trans
  (sum-cong (λ k → sym (sum-mulʳ (C k j) (λ l → A i l * B l k))))
  (trans (sum-swap (λ k l → (A i l * B l k) * C k j))
    (sum-cong (λ l → trans (sum-cong (λ k → *-assoc (A i l) (B l k) (C k j)))
      (sum-mulˡ (A i l) (λ k → B l k * C k j)))))

-- Associativity is proved once for matrices of any finite dimension.
mul-middle : ∀ {n} (A B C D : Mat n) →
  mul (mul A B) (mul C D) ≈ mul A (mul (mul B C) D)
mul-middle A B C D = ≈-trans (mul-assoc A B (mul C D))
  (mul-cong {A = A} {B = A} ≈-refl (≈-sym (mul-assoc B C D)))

sandwich-product : ∀ {n} (A B C D E F : Mat n) →
  mul (mul A B) (mul (mul C D) (mul E F)) ≈
  mul (mul (mul (mul (mul A B) C) D) E) F
sandwich-product A B C D E F = ≈-trans
  (≈-sym (mul-assoc (mul A B) (mul C D) (mul E F)))
  (≈-trans (mul-cong {C = mul E F} {D = mul E F} (≈-sym (mul-assoc (mul A B) C D)) ≈-refl)
    (≈-sym (mul-assoc (mul (mul (mul A B) C) D) E F)))

delta-sym : ∀ {n} (i j : Fin n) → delta i j ≡ delta j i
delta-sym zero zero = refl
delta-sym zero (suc j) = refl
delta-sym (suc i) zero = refl
delta-sym (suc i) (suc j) = delta-sym i j

delta-self : ∀ {n} (i : Fin n) → delta i i ≡ 1#
delta-self zero = refl
delta-self (suc i) = delta-self i

delta-other : ∀ {n} (i j : Fin n) → i ≢ j → delta i j ≡ 0#
delta-other zero zero h with h refl
... | ()
delta-other zero (suc j) h = refl
delta-other (suc i) zero h = refl
delta-other (suc i) (suc j) h = delta-other i j (λ eq → h (cong suc eq))

sum-delta : ∀ {n} (i : Fin n) (f : Fin n → ZComplex) → sum (λ k → delta i k * f k) ≡ f i
sum-delta {suc n} zero f = trans (cong₂ _+_ (*-identityˡ (f zero))
  (trans (sum-cong (λ k → *-zeroˡ (f (suc k)))) (sum-zero n))) (+-identityʳ (f zero))
sum-delta (suc i) f = trans (cong₂ _+_ (*-zeroˡ (f zero))
  (sum-delta i (λ k → f (suc k)))) (+-identityˡ (f (suc i)))

identity-mul : ∀ {n} (M : Mat n) → mul identity M ≈ M
identity-mul M i j = sum-delta i (λ k → M k j)

mul-identity : ∀ {n} (M : Mat n) → mul M identity ≈ M
mul-identity M i j = trans
  (sum-cong (λ k → trans (*-comm (M i k) (delta k j)) (cong (_* M i k) (delta-sym k j))))
  (sum-delta j (M i))
