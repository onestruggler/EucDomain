{-# OPTIONS --safe --without-K #-}
-- Residue-code arithmetic by pattern matching (no table lookups, no `#_`
-- literals), proved equal to GauInt.Gamma.Residue.Tables entry by entry.
module GauInt.Gamma.Residue.Cases where

open import GauInt.Gamma.Residue using (Code)
import GauInt.Gamma.Residue.Tables as T
open import Finite.Check using (checkFin; decAll)
open import Data.Nat using (ℕ)
import Data.Nat as N
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F)
open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as BP
open import Data.Unit using (tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

add mul : Code → Code → Code
add 0F 0F = 0F
add 0F 1F = 1F
add 0F 2F = 2F
add 0F 3F = 3F
add 0F 4F = 4F
add 0F 5F = 5F
add 0F 6F = 6F
add 0F 7F = 7F
add 1F 0F = 1F
add 1F 1F = 4F
add 1F 2F = 3F
add 1F 3F = 6F
add 1F 4F = 5F
add 1F 5F = 0F
add 1F 6F = 7F
add 1F 7F = 2F
add 2F 0F = 2F
add 2F 1F = 3F
add 2F 2F = 0F
add 2F 3F = 1F
add 2F 4F = 6F
add 2F 5F = 7F
add 2F 6F = 4F
add 2F 7F = 5F
add 3F 0F = 3F
add 3F 1F = 6F
add 3F 2F = 1F
add 3F 3F = 4F
add 3F 4F = 7F
add 3F 5F = 2F
add 3F 6F = 5F
add 3F 7F = 0F
add 4F 0F = 4F
add 4F 1F = 5F
add 4F 2F = 6F
add 4F 3F = 7F
add 4F 4F = 0F
add 4F 5F = 1F
add 4F 6F = 2F
add 4F 7F = 3F
add 5F 0F = 5F
add 5F 1F = 0F
add 5F 2F = 7F
add 5F 3F = 2F
add 5F 4F = 1F
add 5F 5F = 4F
add 5F 6F = 3F
add 5F 7F = 6F
add 6F 0F = 6F
add 6F 1F = 7F
add 6F 2F = 4F
add 6F 3F = 5F
add 6F 4F = 2F
add 6F 5F = 3F
add 6F 6F = 0F
add 6F 7F = 1F
add 7F 0F = 7F
add 7F 1F = 2F
add 7F 2F = 5F
add 7F 3F = 0F
add 7F 4F = 3F
add 7F 5F = 6F
add 7F 6F = 1F
add 7F 7F = 4F
mul 0F 0F = 0F
mul 0F 1F = 0F
mul 0F 2F = 0F
mul 0F 3F = 0F
mul 0F 4F = 0F
mul 0F 5F = 0F
mul 0F 6F = 0F
mul 0F 7F = 0F
mul 1F 0F = 0F
mul 1F 1F = 1F
mul 1F 2F = 2F
mul 1F 3F = 3F
mul 1F 4F = 4F
mul 1F 5F = 5F
mul 1F 6F = 6F
mul 1F 7F = 7F
mul 2F 0F = 0F
mul 2F 1F = 2F
mul 2F 2F = 4F
mul 2F 3F = 6F
mul 2F 4F = 0F
mul 2F 5F = 2F
mul 2F 6F = 4F
mul 2F 7F = 6F
mul 3F 0F = 0F
mul 3F 1F = 3F
mul 3F 2F = 6F
mul 3F 3F = 5F
mul 3F 4F = 4F
mul 3F 5F = 7F
mul 3F 6F = 2F
mul 3F 7F = 1F
mul 4F 0F = 0F
mul 4F 1F = 4F
mul 4F 2F = 0F
mul 4F 3F = 4F
mul 4F 4F = 0F
mul 4F 5F = 4F
mul 4F 6F = 0F
mul 4F 7F = 4F
mul 5F 0F = 0F
mul 5F 1F = 5F
mul 5F 2F = 2F
mul 5F 3F = 7F
mul 5F 4F = 4F
mul 5F 5F = 1F
mul 5F 6F = 6F
mul 5F 7F = 3F
mul 6F 0F = 0F
mul 6F 1F = 6F
mul 6F 2F = 4F
mul 6F 3F = 2F
mul 6F 4F = 0F
mul 6F 5F = 6F
mul 6F 6F = 4F
mul 6F 7F = 2F
mul 7F 0F = 0F
mul 7F 1F = 7F
mul 7F 2F = 6F
mul 7F 3F = 1F
mul 7F 4F = 4F
mul 7F 5F = 3F
mul 7F 6F = 2F
mul 7F 7F = 5F

star : Code → Code
star 0F = 0F
star 1F = 1F
star 2F = 6F
star 3F = 7F
star 4F = 4F
star 5F = 5F
star 6F = 2F
star 7F = 3F

bit : Fin 3 → Code → ℕ
bit 0F 0F = 0
bit 0F 1F = 1
bit 0F 2F = 0
bit 0F 3F = 1
bit 0F 4F = 0
bit 0F 5F = 1
bit 0F 6F = 0
bit 0F 7F = 1
bit 1F 0F = 0
bit 1F 1F = 1
bit 1F 2F = 1
bit 1F 3F = 0
bit 1F 4F = 0
bit 1F 5F = 1
bit 1F 6F = 1
bit 1F 7F = 0
bit 2F 0F = 0
bit 2F 1F = 0
bit 2F 2F = 1
bit 2F 3F = 1
bit 2F 4F = 1
bit 2F 5F = 1
bit 2F 6F = 0
bit 2F 7F = 0

isZero : Code → Bool
isZero zero = true
isZero (suc _) = false

eqF : ∀ {n} → Fin n → Fin n → Bool
eqF zero zero = true
eqF zero (suc _) = false
eqF (suc _) zero = false
eqF (suc x) (suc y) = eqF x y

eqF-≟ : ∀ {n} (x y : Fin n) → does (x ≟ y) ≡ eqF x y
eqF-≟ zero zero = refl
eqF-≟ zero (suc y) = refl
eqF-≟ (suc x) zero = refl
eqF-≟ (suc x) (suc y) = eqF-≟ x y

eqF-zero : ∀ (x : Code) → eqF x 0F ≡ isZero x
eqF-zero zero = refl
eqF-zero (suc x) = refl

abstract
  add-T : ∀ a b → add a b ≡ T.add a b
  add-T = checkFin 8 _ (λ a → decAll 8 _ (λ b → add a b ≟ T.add a b)) tt
  mul-T : ∀ a b → mul a b ≡ T.multiply a b
  mul-T = checkFin 8 _ (λ a → decAll 8 _ (λ b → mul a b ≟ T.multiply a b)) tt
  star-T : ∀ a → star a ≡ T.star a
  star-T = checkFin 8 _ (λ a → star a ≟ T.star a) tt
  bit-T : ∀ d c → bit d c ≡ T.bit d c
  bit-T = checkFin 3 _ (λ d → decAll 8 _ (λ c → bit d c N.≟ T.bit d c)) tt
  add-zeroʳ : ∀ a → add a 0F ≡ a
  add-zeroʳ = checkFin 8 _ (λ a → add a 0F ≟ a) tt
  add-assoc : ∀ a b c → add (add a b) c ≡ add a (add b c)
  add-assoc = checkFin 8 _ (λ a → decAll 8 _ (λ b → decAll 8 _ (λ c → add (add a b) c ≟ add a (add b c)))) tt
  star-add : ∀ a b → star (add a b) ≡ add (star a) (star b)
  star-add = checkFin 8 _ (λ a → decAll 8 _ (λ b → star (add a b) ≟ add (star a) (star b))) tt
  star-mul : ∀ a b → star (mul a b) ≡ mul (star a) (star b)
  star-mul = checkFin 8 _ (λ a → decAll 8 _ (λ b → star (mul a b) ≟ mul (star a) (star b))) tt
  star-star : ∀ a → star (star a) ≡ a
  star-star = checkFin 8 _ (λ a → star (star a) ≟ a) tt
  isZero-star : ∀ a → isZero (star a) ≡ isZero a
  isZero-star = checkFin 8 _ (λ a → isZero (star a) BP.≟ isZero a) tt
