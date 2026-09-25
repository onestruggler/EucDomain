{-# OPTIONS --safe --without-K #-}

-- Pointwise finite-sum laws for the executable residue weight.
module Natural.Sum where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Fin using (Fin; zero; suc; _≟_)
import Data.Fin.Permutation as P
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.PropositionalEquality using (subst)

sumNat : ∀ {n} → (Fin n → ℕ) → ℕ
sumNat {0} f = 0
sumNat {Data.Nat.suc n} f = f zero + sumNat (λ i → f (suc i))

sum-cong : ∀ {n} {f g : Fin n → ℕ} → (∀ i → f i ≡ g i) → sumNat f ≡ sumNat g
sum-cong {zero} h = refl
sum-cong {suc n} h = cong₂ _+_ (h zero) (sum-cong (λ i → h (suc i)))

sum-zero : ∀ n → sumNat {n} (λ _ → 0) ≡ 0
sum-zero zero = refl
sum-zero (suc n) = sum-zero n

sum-component : ∀ {n} (f : Fin n → ℕ) i → f i ≤ sumNat f
sum-component f zero = NP.m≤m+n (f zero) _
sum-component f (suc i) = NP.≤-trans (sum-component (λ k → f (suc k)) i)
  (NP.m≤n+m (sumNat (λ k → f (suc k))) (f zero))

sum-le : ∀ {n} (f g : Fin n → ℕ) → (∀ i → f i ≤ g i) → sumNat f ≤ sumNat g
sum-le {zero} f g h = NP.≤-refl
sum-le {suc n} f g h = NP.+-mono-≤ (h zero) (sum-le (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

equal-head : ∀ a b c d → a ≤ c → b ≤ d → a + b ≡ c + d → a ≡ c
equal-head a b c d hac hbd he = NP.≤-antisym hac
  (NP.+-cancelʳ-≤ d c a (subst (λ x → x ≤ a + d) he (NP.+-monoʳ-≤ a hbd)))

sum-equal-bounds : ∀ {n} (f g : Fin n → ℕ) → (∀ i → f i ≤ g i) → sumNat f ≡ sumNat g → ∀ i → f i ≡ g i
sum-equal-bounds {suc n} f g h he zero = equal-head (f zero) (sumNat (λ i → f (suc i)))
  (g zero) (sumNat (λ i → g (suc i))) (h zero) (sum-le (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i))) he
sum-equal-bounds {suc n} f g h he (suc i) = sum-equal-bounds (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i))
  (NP.+-cancelˡ-≡ (g zero) (sumNat (λ i → f (suc i))) (sumNat (λ i → g (suc i)))
    (trans (cong (_+ sumNat (λ i → f (suc i))) (sym head)) he)) i
  where
  head = equal-head (f zero) (sumNat (λ i → f (suc i))) (g zero) (sumNat (λ i → g (suc i)))
    (h zero) (sum-le (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i))) he

sum-add : ∀ {n} (f g : Fin n → ℕ) → sumNat (λ i → f i + g i) ≡ sumNat f + sumNat g
sum-add {zero} f g = refl
sum-add {suc n} f g = trans (cong ((f zero + g zero) +_) (sum-add (λ i → f (suc i)) (λ i → g (suc i))))
  (solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
    (f zero) (g zero) (sumNat (λ i → f (suc i))) (sumNat (λ i → g (suc i))))

sum-swap : ∀ {m n} (f : Fin m → Fin n → ℕ) →
  sumNat (λ i → sumNat (f i)) ≡ sumNat (λ j → sumNat (λ i → f i j))
sum-swap {zero} {n} f = sym (sum-zero n)
sum-swap {suc m} f = trans (cong (sumNat (f zero) +_) (sum-swap (λ i j → f (suc i) j)))
  (sym (sum-add (f zero) (λ j → sumNat (λ i → f (suc i) j))))

delta : ∀ {n} → Fin n → Fin n → ℕ
delta zero zero = 1
delta zero (suc j) = 0
delta (suc i) zero = 0
delta (suc i) (suc j) = delta i j

delta-self : ∀ {n} (i : Fin n) → delta i i ≡ 1
delta-self zero = refl
delta-self (suc i) = delta-self i

delta-other : ∀ {n} (i j : Fin n) → i ≢ j → delta i j ≡ 0
delta-other zero zero h with h refl
... | ()
delta-other zero (suc j) h = refl
delta-other (suc i) zero h = refl
delta-other (suc i) (suc j) h = delta-other i j (λ eq → h (cong suc eq))

delta-sym : ∀ {n} (i j : Fin n) → delta i j ≡ delta j i
delta-sym zero zero = refl
delta-sym zero (suc j) = refl
delta-sym (suc i) zero = refl
delta-sym (suc i) (suc j) = delta-sym i j

sum-delta : ∀ {n} (i : Fin n) (f : Fin n → ℕ) → sumNat (λ k → delta i k * f k) ≡ f i
sum-delta {suc n} zero f = trans (cong₂ _+_ (NP.*-identityˡ (f zero)) (sum-zero n)) (NP.+-identityʳ (f zero))
sum-delta (suc i) f = sum-delta i (λ k → f (suc k))

delta-permutation : ∀ {n} (p : P.Permutation′ n) i j → delta (p P.⟨$⟩ʳ i) j ≡ delta (p P.⟨$⟩ˡ j) i
delta-permutation p i j with (p P.⟨$⟩ʳ i) ≟ j
... | yes eq = trans (cong (λ k → delta k j) eq) (trans (delta-self j)
  (sym (trans (cong (λ k → delta k i) (trans (cong (p P.⟨$⟩ˡ_) (sym eq)) (P.inverseˡ p))) (delta-self i))))
... | no neq = trans (delta-other (p P.⟨$⟩ʳ i) j neq)
  (sym (delta-other (p P.⟨$⟩ˡ j) i (λ eq → neq (trans (cong (p P.⟨$⟩ʳ_) (sym eq)) (P.inverseʳ p)))))

sum-reindex : ∀ {n} (p : P.Permutation′ n) (f : Fin n → ℕ) → sumNat (λ i → f (p P.⟨$⟩ʳ i)) ≡ sumNat f
sum-reindex p f = trans (sum-cong (λ i → sym (sum-delta (p P.⟨$⟩ʳ i) f)))
  (trans (sum-swap (λ i j → delta (p P.⟨$⟩ʳ i) j * f j))
    (sum-cong (λ j → trans (sum-cong (λ i → cong (_* f j) (delta-permutation p i j)))
      (sum-delta (p P.⟨$⟩ˡ j) (λ _ → f j)))))
