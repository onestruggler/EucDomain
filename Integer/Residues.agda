{-# OPTIONS --safe --without-K #-}

-- Small residue conclusions obtained from explicit congruence witnesses.
module Integer.Residues where

open import Integer.Congruence
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
import Data.Nat as N
import Data.Nat.DivMod as ND
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

multiple2-natural : ∀ w → Cong (+ 2) (+ w) (+ 0) → w ND.% 2 ≡ 0
multiple2-natural w (+ q , h) = trans (cong (λ x → x ND.% 2) (ZP.+-injective h′)) (ND.m*n%n≡0 q 2)
  where
  h′ : + w ≡ + (q N.* 2)
  h′ = trans h (trans (ZP.+-identityˡ ((+ 2) Z.* (+ q)))
    (trans (ZP.*-comm (+ 2) (+ q)) (sym (ZP.pos-* q 2))))
multiple2-natural w (-[1+ q ] , ())

multiple4-natural : ∀ w → Cong (+ 4) (+ w) (+ 0) → w ND.% 4 ≡ 0
multiple4-natural w (+ q , h) = trans (cong (λ x → x ND.% 4) (ZP.+-injective h′)) (ND.m*n%n≡0 q 4)
  where
  h′ : + w ≡ + (q N.* 4)
  h′ = trans h (trans (ZP.+-identityˡ ((+ 4) Z.* (+ q)))
    (trans (ZP.*-comm (+ 4) (+ q)) (sym (ZP.pos-* q 4))))
multiple4-natural w (-[1+ q ] , ())

four-to-two : ∀ x y → Cong (+ 4) x y → Cong (+ 2) x y
four-to-two x y (q , h) = (+ 2) Z.* q , trans h
  (solve 2 (λ y q → y :+ con (+ 4) :* q := y :+ con (+ 2) :* (con (+ 2) :* q)) refl y q)

weight-high : ∀ w → w ≤ 6 → Cong (+ 4) (+ w) (+ 0) → w ≡ 0 ⊎ w ≡ 4
weight-high w hw hc = classify w hw (multiple4-natural w hc)
  where
  classify : ∀ w → w ≤ 6 → w ND.% 4 ≡ 0 → w ≡ 0 ⊎ w ≡ 4
  classify 0 h eq = inj₁ refl
  classify 1 h ()
  classify 2 h ()
  classify 3 h ()
  classify 4 h eq = inj₂ refl
  classify 5 h ()
  classify 6 h ()
  classify (suc (suc (suc (suc (suc (suc (suc n))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))) eq

weight-one : ∀ w → w ≤ 2 → Cong (+ 4) (+ w) (+ 2) → w ≡ 2
weight-one 0 hw hc = ⊥-elim (impossible (multiple4-natural 2 (cong-sym (+ 4) (+ 0) (+ 2) hc)))
  where impossible : 2 ND.% 4 ≡ 0 → Data.Empty.⊥
        impossible ()
weight-one 1 hw hc = ⊥-elim (impossible (multiple2-natural 1 (cong-trans (+ 2) (+ 1) (+ 2) (+ 0)
  (four-to-two (+ 1) (+ 2) hc) (+ 1 , refl))))
  where impossible : 1 ND.% 2 ≡ 0 → Data.Empty.⊥
        impossible ()
weight-one 2 hw hc = refl
weight-one (suc (suc (suc n))) (s≤s (s≤s ())) hc
