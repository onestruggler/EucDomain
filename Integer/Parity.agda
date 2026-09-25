{-# OPTIONS --safe --without-K #-}

module Integer.Parity where

open import Integer.Congruence
open import Data.Integer using (ℤ; +_; _%ℕ_; _/ℕ_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
import Data.Integer.DivMod as ZD
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

parity : ℤ → ℕ
parity x = x %ℕ 2

parityBit : ℤ → Bool
parityBit x = Relation.Nullary.does (parity x Data.Nat.≟ 1)

parity-cases : ∀ x → parity x ≡ 0 ⊎ parity x ≡ 1
parity-cases x = bounded (parity x) (ZD.n%ℕd<d x 2)
  where
  bounded : ∀ n → n < 2 → n ≡ 0 ⊎ n ≡ 1
  bounded zero h = inj₁ refl
  bounded (suc zero) h = inj₂ refl
  bounded (suc (suc n)) (s≤s (s≤s ()))

parity-bound : ∀ x → parity x ≤ 1
parity-bound x with parity-cases x
... | inj₁ eq = subst (_≤ 1) (sym eq) z≤n
... | inj₂ eq = subst (_≤ 1) (sym eq) (s≤s z≤n)

parity-decomposition : ∀ x → x ≡ + (parity x) Z.+ (+ 2) Z.* (x /ℕ 2)
parity-decomposition x = trans (ZD.a≡a%ℕn+[a/ℕn]*n x 2)
  (cong (λ t → + (parity x) Z.+ t) (ZP.*-comm (x /ℕ 2) (+ 2)))

parity-congruence : ∀ x → Cong (+ 2) x (+ (parity x))
parity-congruence x = x /ℕ 2 , parity-decomposition x

square-congruence : ∀ x → Cong (+ 4) (x Z.* x) (+ (parity x))
square-congruence x with parity-cases x
... | inj₁ hp = q Z.* q , trans (cong₂ Z._*_ hx hx)
  (trans (solve 1 (λ q → (con (+ 0) :+ con (+ 2) :* q) :* (con (+ 0) :+ con (+ 2) :* q)
    := con (+ 0) :+ con (+ 4) :* (q :* q)) refl q)
    (cong (λ p → + p Z.+ (+ 4) Z.* (q Z.* q)) (sym hp)))
  where
  q = x /ℕ 2
  hx = trans (parity-decomposition x) (cong (λ p → + p Z.+ (+ 2) Z.* q) hp)
... | inj₂ hp = q Z.* q Z.+ q , trans (cong₂ Z._*_ hx hx)
  (trans (solve 1 (λ q → (con (+ 1) :+ con (+ 2) :* q) :* (con (+ 1) :+ con (+ 2) :* q)
    := con (+ 1) :+ con (+ 4) :* (q :* q :+ q)) refl q)
    (cong (λ p → + p Z.+ (+ 4) Z.* (q Z.* q Z.+ q)) (sym hp)))
  where
  q = x /ℕ 2
  hx = trans (parity-decomposition x) (cong (λ p → + p Z.+ (+ 2) Z.* q) hp)


-- Congruence and Boolean parity operations.
open import Integer.Congruence
open import Integer.Residues using (multiple2-natural)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (_%_; _≟_)
open import Data.Bool using (_xor_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

one-not-even : Cong (+ 2) (+ 1) (+ 0) → ⊥
one-not-even h = bad (multiple2-natural 1 h)
  where bad : 1 % 2 ≡ 0 → ⊥; bad ()

parity-congruent : ∀ x y → Cong (+ 2) x y → parity x ≡ parity y
parity-congruent x y h = finish pCong
  where
  pCong : Cong (+ 2) (+ (parity x)) (+ (parity y))
  pCong = cong-trans (+ 2) (+ (parity x)) x (+ (parity y))
    (cong-sym (+ 2) x (+ (parity x)) (parity-congruence x))
    (cong-trans (+ 2) x y (+ (parity y)) h (parity-congruence y))
  finish : Cong (+ 2) (+ (parity x)) (+ (parity y)) → parity x ≡ parity y
  finish h with parity-cases x | parity-cases y
  ... | inj₁ hx | inj₁ hy = trans hx (sym hy)
  ... | inj₂ hx | inj₂ hy = trans hx (sym hy)
  ... | inj₁ hx | inj₂ hy = ⊥-elim (one-not-even (cong-sym (+ 2) (+ 0) (+ 1)
    (subst (λ n → Cong (+ 2) (+ 0) (+ n)) hy (subst (λ n → Cong (+ 2) (+ n) (+ (parity y))) hx h))))
  ... | inj₂ hx | inj₁ hy = ⊥-elim (one-not-even
    (subst (λ n → Cong (+ 2) (+ 1) (+ n)) hy (subst (λ n → Cong (+ 2) (+ n) (+ (parity y))) hx h)))

parityBit-congruent : ∀ x y → Cong (+ 2) x y → parityBit x ≡ parityBit y
parityBit-congruent x y h = cong (λ n → does (n ≟ 1)) (parity-congruent x y h)

parityBit-sum : ∀ x y → parityBit (x Z.+ y) ≡ parityBit x xor parityBit y
parityBit-sum x y = trans (parityBit-congruent (x Z.+ y) (+ (parity x) Z.+ + (parity y))
  (cong-add (+ 2) x (+ (parity x)) y (+ (parity y)) (parity-congruence x) (parity-congruence y))) small
  where
  small : parityBit (+ (parity x) Z.+ + (parity y)) ≡ parityBit x xor parityBit y
  small with parity-cases x | parity-cases y
  ... | inj₁ hx | inj₁ hy rewrite hx | hy = refl
  ... | inj₁ hx | inj₂ hy rewrite hx | hy = refl
  ... | inj₂ hx | inj₁ hy rewrite hx | hy = refl
  ... | inj₂ hx | inj₂ hy rewrite hx | hy = refl

parityBit-neg : ∀ x → parityBit (Z.- x) ≡ parityBit x
parityBit-neg x = parityBit-congruent (Z.- x) x
  (Z.- x , solve 1 (λ x → :- x := x :+ con (+ 2) :* (:- x)) refl x)

parityBit-difference : ∀ x y → parityBit (x Z.- y) ≡ parityBit x xor parityBit y
parityBit-difference x y = trans (parityBit-sum x (Z.- y)) (cong (parityBit x xor_) (parityBit-neg y))
