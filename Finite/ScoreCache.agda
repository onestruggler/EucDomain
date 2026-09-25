{-# OPTIONS --safe --without-K #-}
-- Structural evaluation and identity proofs for bounded residue scores.
module Finite.ScoreCache where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

forceNat : ∀ {A : Set} → ℕ → (ℕ → A) → A
forceNat zero f = f zero
forceNat (suc n) f = forceNat n (λ m → f (suc m))

forceNat-id : ∀ {A : Set} n (f : ℕ → A) → forceNat n f ≡ f n
forceNat-id zero f = refl
forceNat-id (suc n) f = forceNat-id n (λ m → f (suc m))

forceInteger : ∀ {A : Set} → ℤ → (ℤ → A) → A
forceInteger (+ n) f = forceNat n (λ m → f (+ m))
forceInteger -[1+ n ] f = forceNat n (λ m → f -[1+ m ])

forceInteger-id : ∀ {A : Set} z (f : ℤ → A) → forceInteger z f ≡ f z
forceInteger-id (+ n) f = forceNat-id n (λ m → f (+ m))
forceInteger-id -[1+ n ] f = forceNat-id n (λ m → f -[1+ m ])

forceScore : ∀ {A : Set} → Maybe ℤ → (Maybe ℤ → A) → A
forceScore nothing f = f nothing
forceScore (just z) f = forceInteger z (λ w → f (just w))

forceScore-id : ∀ {A : Set} z (f : Maybe ℤ → A) → forceScore z f ≡ f z
forceScore-id nothing f = refl
forceScore-id (just z) f = forceInteger-id z (λ w → f (just w))

forceScores : ∀ {n} {A : Set} → Vec (Maybe ℤ) n → (Vec (Maybe ℤ) n → A) → A
forceScores [] f = f []
forceScores (x ∷ xs) f = forceScore x (λ y → forceScores xs (λ ys → f (y ∷ ys)))

forceScores-id : ∀ {n} {A : Set} (xs : Vec (Maybe ℤ) n) f → forceScores {A = A} xs f ≡ f xs
forceScores-id [] f = refl
forceScores-id (x ∷ xs) f = trans (forceScore-id x (λ y → forceScores xs (λ ys → f (y ∷ ys))))
  (forceScores-id xs (λ ys → f (x ∷ ys)))

forceBoth : ∀ {n} {A : Set} → Vec (Maybe ℤ) n → Vec (Maybe ℤ) n →
  (Vec (Maybe ℤ) n → Vec (Maybe ℤ) n → A) → A
forceBoth xs ys f = forceScores xs (λ x → forceScores ys (f x))

forceBoth-id : ∀ {n} {A : Set} (xs ys : Vec (Maybe ℤ) n) f → forceBoth {A = A} xs ys f ≡ f xs ys
forceBoth-id xs ys f = trans (forceScores-id xs (λ x → forceScores ys (f x))) (forceScores-id ys (f xs))
