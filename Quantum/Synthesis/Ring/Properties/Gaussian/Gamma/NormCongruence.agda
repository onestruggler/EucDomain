{-# OPTIONS --safe --without-K #-}

-- Two gamma digits determine the Gaussian norm modulo four.
module Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.NormCongruence where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma using (γ; powγ)
import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.Congruence as G
open import Integer.Congruence using (Cong)
import Integer.Congruence as IC
open import Integer.Sum using (intSum)
open import Data.Fin using (Fin)
open import Data.Integer using (+_)
import Data.Integer as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

norm-perturbation₂ : ∀ b q → Cong (+ 4) (TC.norm (b + q * powγ 2)) (TC.norm b)
norm-perturbation₂ (Cplx x y) (Cplx u v) =
  (Z.- (x Z.* v) Z.+ y Z.* u Z.+ u Z.* u Z.+ v Z.* v) ,
  solve 4 (λ x y u v →
    (x :+ (u :* con (+ 0) :- v :* con (+ 2))) :* (x :+ (u :* con (+ 0) :- v :* con (+ 2))) :+
    (y :+ (u :* con (+ 2) :+ v :* con (+ 0))) :* (y :+ (u :* con (+ 2) :+ v :* con (+ 0))) :=
    (x :* x :+ y :* y) :+ con (+ 4) :* ((:- (x :* v)) :+ y :* u :+ u :* u :+ v :* v)) refl x y u v

norm-congruent₂ : ∀ a b → G.Cong 2 a b → Cong (+ 4) (TC.norm a) (TC.norm b)
norm-congruent₂ a b (q , h) = subst (λ z → Cong (+ 4) (TC.norm z) (TC.norm b)) (sym h) (norm-perturbation₂ b q)

norm-sum-congruent₂ : ∀ {n} (f g : Fin n → ZComplex) → (∀ i → G.Cong 2 (f i) (g i)) →
  Cong (+ 4) (intSum (λ i → TC.norm (f i))) (intSum (λ i → TC.norm (g i)))
norm-sum-congruent₂ f g h = IC.cong-sum (+ 4) (λ i → TC.norm (f i)) (λ i → TC.norm (g i))
  (λ i → norm-congruent₂ (f i) (g i) (h i))

norm-perturbation : ∀ b q → Cong (+ 4) (TC.norm (b + q * powγ 3)) (TC.norm b)
norm-perturbation (Cplx x y) (Cplx u v) =
  ((Z.- x Z.+ y) Z.* u Z.- (x Z.+ y) Z.* v Z.+ (+ 2) Z.* (u Z.* u Z.+ v Z.* v)) ,
  solve 4 (λ x y u v →
    (x :+ (u :* con (Z.- (+ 2)) :- v :* con (+ 2))) :* (x :+ (u :* con (Z.- (+ 2)) :- v :* con (+ 2))) :+
    (y :+ (u :* con (+ 2) :+ v :* con (Z.- (+ 2)))) :* (y :+ (u :* con (+ 2) :+ v :* con (Z.- (+ 2)))) :=
    (x :* x :+ y :* y) :+ con (+ 4) :* (((:- x) :+ y) :* u :- (x :+ y) :* v :+ con (+ 2) :* (u :* u :+ v :* v))) refl x y u v

norm-congruent : ∀ a b → G.Cong 3 a b → Cong (+ 4) (TC.norm a) (TC.norm b)
norm-congruent a b (q , h) = subst (λ z → Cong (+ 4) (TC.norm z) (TC.norm b)) (sym h) (norm-perturbation b q)
