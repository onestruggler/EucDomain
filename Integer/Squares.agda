{-# OPTIONS --safe --without-K #-}
module Integer.Squares where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat as N
import Data.Nat.Properties as NP
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; +≤+)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

square-nonnegative : ∀ x → (+ 0) Z.≤ x Z.* x
square-nonnegative (+ zero) = +≤+ z≤n
square-nonnegative (+ suc n) = +≤+ z≤n
square-nonnegative -[1+ n ] = +≤+ z≤n

nat-square-large : ∀ n → 2 N.≤ (suc (suc n)) N.* (suc (suc n))
nat-square-large n = NP.≤-trans (s≤s (s≤s z≤n)) (NP.m≤m+n (suc (suc n)) (suc n N.* suc (suc n)))

small-square : ∀ x → x Z.* x Z.≤ (+ 1) → (x ≡ + 0) ⊎ (x ≡ + 1) ⊎ (x ≡ -[1+ 0 ])
small-square (+ zero) h = inj₁ refl
small-square (+ suc zero) h = inj₂ (inj₁ refl)
small-square (+ suc (suc n)) (+≤+ h) = ⊥-elim (bad (NP.≤-trans (nat-square-large n) h))
  where bad : 2 N.≤ 1 → ⊥; bad (s≤s ())
small-square -[1+ zero ] h = inj₂ (inj₂ refl)
small-square -[1+ suc n ] (+≤+ h) = ⊥-elim (bad (NP.≤-trans (nat-square-large n) h))
  where bad : 2 N.≤ 1 → ⊥; bad (s≤s ())

