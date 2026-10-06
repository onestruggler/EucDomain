{-# OPTIONS --safe --without-K #-}

-- Square Boolean matrices: weights, row overlaps and their parity constraints.
module Finite.BinaryMatrix where

open import Natural.Sum using (sumNat; sum-cong)
open import Finite.Check using (decAll)
open import Data.Nat using (ℕ; _*_; _%_; _≟_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F)
open import Data.Bool using (Bool; false; true; _∧_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (_×?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

Binary : ℕ → Set
Binary n = Fin n → Fin n → Bool

bitNat : Bool → ℕ
bitNat false = 0
bitNat true = 1

bit-square : ∀ b → bitNat b * bitNat b ≡ bitNat b
bit-square false = refl
bit-square true = refl

bit-and : ∀ a b → bitNat (a ∧ b) ≡ bitNat a * bitNat b
bit-and false false = refl
bit-and false true = refl
bit-and true false = refl
bit-and true true = refl

tuple : ∀ {A : Set} → A → A → A → A → Fin 4 → A
tuple a b c d 0F = a
tuple a b c d 1F = b
tuple a b c d 2F = c
tuple a b c d 3F = d

tuple-eta : ∀ {A : Set} (f : Fin 4 → A) i → tuple (f 0F) (f 1F) (f 2F) (f 3F) i ≡ f i
tuple-eta f 0F = refl
tuple-eta f 1F = refl
tuple-eta f 2F = refl
tuple-eta f 3F = refl

rowWeight : ∀ {n} → (Fin n → Bool) → ℕ
rowWeight f = sumNat (λ i → bitNat (f i))

weight : ∀ {n} → Binary n → ℕ
weight R = sumNat (λ i → rowWeight (R i))

overlapCount : ∀ {n} → Binary n → Fin n → Fin n → ℕ
overlapCount R i j = sumNat (λ k → bitNat (R i k) * bitNat (R j k))

transpose : ∀ {n} → Binary n → Binary n
transpose R i j = R j i

Overlaps : ∀ {n} → Binary n → Set
Overlaps R = ∀ i j → overlapCount R i j % 2 ≡ 0

Constraints : ∀ {n} → Binary n → Set
Constraints R = Overlaps R × Overlaps (transpose R)

overlaps? : ∀ {n} (R : Binary n) → Dec (Overlaps R)
overlaps? {n} R = decAll n _ (λ i → decAll n _ (λ j → (overlapCount R i j % 2) ≟ 0))

constraints? : ∀ {n} (R : Binary n) → Dec (Constraints R)
constraints? R = overlaps? R ×? overlaps? (transpose R)

weight-cong : ∀ {n} {R S : Binary n} → (∀ i j → R i j ≡ S i j) → weight R ≡ weight S
weight-cong h = sum-cong (λ i → sum-cong (λ j → cong bitNat (h i j)))

overlap-cong : ∀ {n} {R S : Binary n} → (∀ i j → R i j ≡ S i j) → ∀ i j → overlapCount R i j ≡ overlapCount S i j
overlap-cong h i j = sum-cong (λ k → cong₂ _*_ (cong bitNat (h i k)) (cong bitNat (h j k)))

constraints-cong : ∀ {n} {R S : Binary n} → (∀ i j → R i j ≡ S i j) → Constraints R → Constraints S
constraints-cong h (hr , hc) =
  (λ i j → trans (cong (_% 2) (sym (overlap-cong h i j))) (hr i j)) ,
  (λ i j → trans (cong (_% 2) (sym (overlap-cong (λ i j → h j i) i j))) (hc i j))

self-overlap : ∀ {n} (R : Binary n) i → overlapCount R i i ≡ rowWeight (R i)
self-overlap R i = sum-cong (λ j → bit-square (R i j))
