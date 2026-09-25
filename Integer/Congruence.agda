{-# OPTIONS --safe --without-K #-}

-- Congruences with explicit integer witnesses. This avoids trusting a
-- modular arithmetic evaluator when transporting unbounded Gram equations.
module Integer.Congruence where

open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Integer.Sum using (intSum)

Cong : ℤ → ℤ → ℤ → Set
Cong d x y = Σ[ q ∈ ℤ ] x ≡ y Z.+ d Z.* q

cong-refl : ∀ d x → Cong d x x
cong-refl d x = + 0 , sym (trans (cong (λ z → x Z.+ z) (ZP.*-zeroʳ d)) (ZP.+-identityʳ x))

cong-sym : ∀ d x y → Cong d x y → Cong d y x
cong-sym d x y (q , h) = Z.- q , trans
  (solve 3 (λ d y q → y := (y :+ d :* q) :+ d :* (:- q)) refl d y q)
  (cong (λ z → z Z.+ d Z.* (Z.- q)) (sym h))

cong-trans : ∀ d x y z → Cong d x y → Cong d y z → Cong d x z
cong-trans d x y z (p , hp) (q , hq) = q Z.+ p , trans hp
  (trans (cong (λ t → t Z.+ d Z.* p) hq)
    (solve 4 (λ d z p q → (z :+ d :* q) :+ d :* p := z :+ d :* (q :+ p)) refl d z p q))

cong-add : ∀ d x x′ y y′ → Cong d x x′ → Cong d y y′ → Cong d (x Z.+ y) (x′ Z.+ y′)
cong-add d x x′ y y′ (p , hp) (q , hq) = p Z.+ q , trans (cong₂ Z._+_ hp hq)
  (solve 5 (λ d x y p q → (x :+ d :* p) :+ (y :+ d :* q) := (x :+ y) :+ d :* (p :+ q)) refl d x′ y′ p q)

cong-mul : ∀ d x x′ y y′ → Cong d x x′ → Cong d y y′ → Cong d (x Z.* y) (x′ Z.* y′)
cong-mul d x x′ y y′ (p , hp) (q , hq) = x′ Z.* q Z.+ y′ Z.* p Z.+ d Z.* p Z.* q ,
  trans (cong₂ Z._*_ hp hq)
    (solve 5 (λ d x y p q → (x :+ d :* p) :* (y :+ d :* q) :=
      x :* y :+ d :* (x :* q :+ y :* p :+ d :* p :* q)) refl d x′ y′ p q)

cong-sum : ∀ {n} d (f g : Fin n → ℤ) → (∀ i → Cong d (f i) (g i)) → Cong d (intSum f) (intSum g)
cong-sum {zero} d f g h = cong-refl d (+ 0)
cong-sum {suc n} d f g h = cong-add d (f zero) (g zero) (intSum (λ i → f (suc i))) (intSum (λ i → g (suc i)))
  (h zero) (cong-sum d (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))
