{-# OPTIONS --safe --without-K #-}
module Integer.Sum where

open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

-- Keep finite integer sums independent of matrices, spin and circuit semantics.
intSum : ∀ {n} → (Fin n → ℤ) → ℤ
intSum {zero} f = + 0
intSum {suc n} f = f zero Z.+ intSum (λ i → f (suc i))

sum-add : ∀ {n} (f g : Fin n → ℤ) → intSum (λ i → f i Z.+ g i) ≡ intSum f Z.+ intSum g
sum-add {zero} f g = refl
sum-add {suc n} f g = trans (cong (λ x → (f zero Z.+ g zero) Z.+ x) (sum-add (λ i → f (suc i)) (λ i → g (suc i))))
  (solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
    (f zero) (g zero) (intSum (λ i → f (suc i))) (intSum (λ i → g (suc i))))

sum-sub : ∀ {n} (f g : Fin n → ℤ) → intSum (λ i → f i Z.- g i) ≡ intSum f Z.- intSum g
sum-sub {zero} f g = refl
sum-sub {suc n} f g = trans (cong (λ x → (f zero Z.- g zero) Z.+ x) (sum-sub (λ i → f (suc i)) (λ i → g (suc i))))
  (solve 4 (λ a b c d → (a :- b) :+ (c :- d) := (a :+ c) :- (b :+ d)) refl
    (f zero) (g zero) (intSum (λ i → f (suc i))) (intSum (λ i → g (suc i))))

sum-scale : ∀ {n} a (f : Fin n → ℤ) → intSum (λ i → a Z.* f i) ≡ a Z.* intSum f
sum-scale {zero} a f = Relation.Binary.PropositionalEquality.sym (ZP.*-zeroʳ a)
sum-scale {suc n} a f = trans (cong (λ x → a Z.* f zero Z.+ x) (sum-scale a (λ i → f (suc i))))
  (Relation.Binary.PropositionalEquality.sym (ZP.*-distribˡ-+ a (f zero) (intSum (λ i → f (suc i)))))
