{-# OPTIONS --safe --without-K #-}

-- Algebraic laws for the operational fast-power method.
module Typeclasses.Properties where

open import Typeclasses using (SemiRing; _*_; 1#; _^_; power-odd; power-acc; power-fuel)
open import Algebra.Structures using (IsCommutativeMonoid)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n; ⌊_/2⌋)
import Data.Nat.Properties as NP
open import Data.Bool.Base using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

private
  even-split : ∀ n → power-odd n ≡ false → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
  even-split zero h = refl
  even-split (suc zero) ()
  even-split (suc (suc n)) h rewrite NP.+-suc ⌊ n /2⌋ ⌊ n /2⌋ =
    cong (λ k → suc (suc k)) (even-split n h)

  odd-split : ∀ n → power-odd n ≡ true → suc (⌊ n /2⌋ + ⌊ n /2⌋) ≡ n
  odd-split zero ()
  odd-split (suc zero) h = refl
  odd-split (suc (suc n)) h rewrite NP.+-suc ⌊ n /2⌋ ⌊ n /2⌋ =
    cong (λ k → suc (suc k)) (odd-split n h)

  halve-bound : ∀ f n → suc (suc n) ≤ suc (suc f) → ⌊ suc (suc n) /2⌋ ≤ suc f
  halve-bound f n h = NP.≤-pred (NP.≤-trans (NP.⌊n/2⌋<n (suc n)) h)

module Powers {A : Set} {{sr : SemiRing A}}
  (laws : IsCommutativeMonoid (_≡_ {A = A}) _*_ 1#) where

  open IsCommutativeMonoid laws using (assoc; comm; identityˡ; identityʳ)

  power : A → ℕ → A
  power x zero = 1#
  power x (suc n) = x * power x n

  power-add : ∀ x m n → power x (m + n) ≡ power x m * power x n
  power-add x zero n = sym (identityˡ (power x n))
  power-add x (suc m) n = trans (cong (x *_) (power-add x m n))
    (sym (assoc x (power x m) (power x n)))

  private
    square : ∀ x n → power (x * x) n ≡ power x (n + n)
    square x zero = refl
    square x (suc n) rewrite NP.+-suc n n =
      trans (cong ((x * x) *_) (square x n)) (assoc x x (power x (n + n)))

    acc-odd : ∀ x n z → power (x * x) n * (x * z) ≡ power x (suc (n + n)) * z
    acc-odd x n z = trans (cong (_* (x * z)) (square x n))
      (trans (sym (assoc (power x (n + n)) x z))
        (cong (_* z) (comm (power x (n + n)) x)))

    acc-sound : ∀ f x n z → 1 ≤ n → n ≤ suc f →
      power-acc _*_ f x n z ≡ power x n * z
    acc-sound zero x zero z () h
    acc-sound zero x (suc zero) z pos h = cong (_* z) (sym (identityʳ x))
    acc-sound zero x (suc (suc n)) z pos (s≤s ())
    acc-sound (suc f) x zero z () h
    acc-sound (suc f) x (suc zero) z pos h = cong (_* z) (sym (identityʳ x))
    acc-sound (suc f) x (suc (suc n)) z pos h with power-odd n in e
    ... | false = trans (acc-sound f (x * x) (suc ⌊ n /2⌋) z (s≤s z≤n) (halve-bound f n h))
      (trans (cong (_* z) (square x (suc ⌊ n /2⌋)))
        (cong (λ k → power x k * z) (even-split (suc (suc n)) e)))
    ... | true = trans (acc-sound f (x * x) (suc ⌊ n /2⌋) (x * z) (s≤s z≤n) (halve-bound f n h))
      (trans (acc-odd x (suc ⌊ n /2⌋) z)
        (cong (λ k → power x k * z) (odd-split (suc (suc n)) e)))

    fuel-sound : ∀ f x n → 1 ≤ n → n ≤ suc f → power-fuel _*_ f x n ≡ power x n
    fuel-sound zero x zero () h
    fuel-sound zero x (suc zero) pos h = sym (identityʳ x)
    fuel-sound zero x (suc (suc n)) pos (s≤s ())
    fuel-sound (suc f) x zero () h
    fuel-sound (suc f) x (suc zero) pos h = sym (identityʳ x)
    fuel-sound (suc f) x (suc (suc n)) pos h with power-odd n in e
    ... | false = trans (fuel-sound f (x * x) (suc ⌊ n /2⌋) (s≤s z≤n) (halve-bound f n h))
      (trans (square x (suc ⌊ n /2⌋)) (cong (power x) (even-split (suc (suc n)) e)))
    ... | true = trans (acc-sound f (x * x) (suc ⌊ n /2⌋) x (s≤s z≤n) (halve-bound f n h))
      (trans (cong (_* x) (square x (suc ⌊ n /2⌋)))
        (trans (comm (power x (suc ⌊ n /2⌋ + suc ⌊ n /2⌋)) x)
          (cong (power x) (odd-split (suc (suc n)) e))))

  ^-correct : ∀ x n → x ^ n ≡ power x n
  ^-correct x zero = refl
  ^-correct x n@(suc _) = fuel-sound n x n (s≤s z≤n) (NP.n≤1+n n)

  ^-suc : ∀ x n → x ^ suc n ≡ x * (x ^ n)
  ^-suc x n = trans (^-correct x (suc n)) (cong (x *_) (sym (^-correct x n)))

  ^-double : ∀ x n → x ^ (n + n) ≡ (x * x) ^ n
  ^-double x n = trans (^-correct x (n + n))
    (trans (sym (square x n)) (sym (^-correct (x * x) n)))

  exchange : ∀ a b c → a * (b * c) ≡ b * (a * c)
  exchange a b c = trans (sym (assoc a b c))
    (trans (cong (_* c) (comm a b)) (assoc b a c))

  ^-add : ∀ x m n → x ^ (m + n) ≡ (x ^ m) * (x ^ n)
  ^-add x m n = trans (^-correct x (m + n))
    (trans (power-add x m n)
      (trans (cong (_* power x n) (sym (^-correct x m)))
        (cong ((x ^ m) *_) (sym (^-correct x n)))))

  action-compose : ∀ x m n z → (x ^ m) * ((x ^ n) * z) ≡ (x ^ (m + n)) * z
  action-compose x m n z = trans (sym (assoc (x ^ m) (x ^ n) z))
    (cong (_* z) (sym (^-add x m n)))

  ^-one : ∀ n → 1# ^ n ≡ 1#
  ^-one zero = refl
  ^-one (suc n) = trans (^-suc 1# n) (trans (identityˡ (1# ^ n)) (^-one n))

  product-swap : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
  product-swap a b c d = trans (assoc a b (c * d))
    (trans (cong (a *_) (sym (assoc b c d)))
      (trans (cong (λ t → a * (t * d)) (comm b c))
        (trans (cong (a *_) (assoc c b d)) (sym (assoc a c (b * d))))))

  ^-mul : ∀ x y n → (x * y) ^ n ≡ (x ^ n) * (y ^ n)
  ^-mul x y zero = sym (identityˡ 1#)
  ^-mul x y (suc n) = trans (^-suc (x * y) n)
    (trans (cong ((x * y) *_) (^-mul x y n))
      (trans (product-swap x y (x ^ n) (y ^ n))
        (cong₂ _*_ (sym (^-suc x n)) (sym (^-suc y n)))))

  inverse-powers : ∀ x y → x * y ≡ 1# → ∀ n → (x ^ n) * (y ^ n) ≡ 1#
  inverse-powers x y inverse n = trans (sym (^-mul x y n))
    (trans (cong (λ a → a ^ n) inverse) (^-one n))

  cancel-powers : ∀ x y → x * y ≡ 1# → ∀ n {a b} →
    (y ^ n) * a ≡ (y ^ n) * b → a ≡ b
  cancel-powers x y inverse n {a} {b} h = trans (sym (identityˡ a))
    (trans (cong (_* a) (sym (inverse-powers x y inverse n)))
      (trans (assoc (x ^ n) (y ^ n) a)
        (trans (cong ((x ^ n) *_) h)
          (trans (sym (assoc (x ^ n) (y ^ n) b))
            (trans (cong (_* b) (inverse-powers x y inverse n)) (identityˡ b))))))

module MapPowers {A B : Set} {{sa : SemiRing A}} {{sb : SemiRing B}}
  (la : IsCommutativeMonoid (_≡_ {A = A}) _*_ 1#)
  (lb : IsCommutativeMonoid (_≡_ {A = B}) _*_ 1#)
  (f : A → B) (one : f 1# ≡ 1#) (mul : ∀ x y → f (x * y) ≡ f x * f y) where

  private
    module PA = Powers la
    module PB = Powers lb

  map-power : ∀ x n → f (x ^ n) ≡ f x ^ n
  map-power x zero = one
  map-power x (suc n) = trans (cong f (PA.^-suc x n))
    (trans (mul x (x ^ n))
      (trans (cong (f x *_) (map-power x n)) (sym (PB.^-suc (f x) n))))
