{-# OPTIONS --safe --without-K #-}

-- Port of the ring and conjugation facts in Lean/Kopt/Algebra.lean.
module GauInt.Algebra where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; isEquivalence)
open import Algebra.Bundles using (CommutativeRing)
import Tactic.RingSolver.NonReflective as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR
open import Relation.Nullary.Decidable.Core using (dec⇒maybe)

-- The shared generic complex-ring proof specializes to Gaussian integers.
import Quantum.Synthesis.Ring.Properties.Cplx as Cplx
import Quantum.Synthesis.Ring.Properties.Hom as Hom

gaussianRing : CommutativeRing _ _
gaussianRing = Cplx.commutativeRing-Cplx ZP.+-*-isCommutativeRing

open CommutativeRing gaussianRing public using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ;
   *-comm; *-assoc; *-identityˡ; *-identityʳ)
  renaming (distribˡ to *-distribˡ; distribʳ to *-distribʳ;
    -‿inverseˡ to +-inverseˡ; -‿inverseʳ to +-inverseʳ)

-- Sparse polynomial normalization keeps the large exterior identity tractable.
module GaussianSolver where
  open Solver (ACR.fromCommutativeRing gaussianRing (λ x → dec⇒maybe (0# TC.≟ x))) public
    renaming (Κ to con; _⊕_ to _:+_; _⊗_ to _:*_; ⊝_ to :-_)
  infixl 6 _:-_
  _:-_ : ∀ {n} → Expr ZComplex n → Expr ZComplex n → Expr ZComplex n
  a :- b = a :+ (:- b)
  infix 4 _:=_
  _:=_ : ∀ {n} → Expr ZComplex n → Expr ZComplex n → Expr ZComplex n × Expr ZComplex n
  _:=_ = _,_

open +-*-Solver

conj-add : ∀ (x y : ZComplex) → TC.adj (x + y) ≡ TC.adj x + TC.adj y
conj-add (Cplx a b) (Cplx c d) = cong (Cplx (a Z.+ c))
  (solve 2 (λ b d → :- (b :+ d) := (:- b) :+ (:- d)) refl b d)

conj-mul : ∀ (x y : ZComplex) → TC.adj (x * y) ≡ TC.adj x * TC.adj y
conj-mul (Cplx a b) (Cplx c d) = cong₂ Cplx
  (solve 4 (λ a b c d → a :* c :- b :* d := a :* c :- (:- b) :* (:- d)) refl a b c d)
  (solve 4 (λ a b c d → :- (a :* d :+ b :* c) := a :* (:- d) :+ (:- b) :* c) refl a b c d)

conj-involutive : ∀ (x : ZComplex) → TC.adj (TC.adj x) ≡ x
conj-involutive (Cplx a b) = cong (Cplx a) (ZP.neg-involutive b)

normSq-mul : ∀ (x y : ZComplex) → TC.norm (x * y) ≡ TC.norm x Z.* TC.norm y
normSq-mul (Cplx a b) (Cplx c d) = solve 4 (λ a b c d →
  (a :* c :- b :* d) :* (a :* c :- b :* d) :+
  (a :* d :+ b :* c) :* (a :* d :+ b :* c) :=
    (a :* a :+ b :* b) :* (c :* c :+ d :* d)) refl a b c d

-- Scalar embeddings and units are independent of matrix and spin semantics.
lift : ℤ → ZComplex
lift x = Cplx x (+ 0)

lift-add : ∀ x y → lift (x Z.+ y) ≡ lift x + lift y
lift-add x y = refl

lift-mul : ∀ x y → lift (x Z.* y) ≡ lift x * lift y
lift-mul x y = cong₂ Cplx (sym (ZP.+-identityʳ (x Z.* y)))
  (sym (cong₂ Z._+_ (ZP.*-zeroʳ x) (ZP.*-zeroˡ y)))

-- Scalar conjugation is a unital ring automorphism. (Matrix adjoints, in
-- contrast, reverse the order of multiplication.) Reuse the shared proof.
adj-isInvolutiveRingEndo : Hom.IsInvolutiveRingEndo {ZComplex} TC.adj
adj-isInvolutiveRingEndo = Cplx.adj-Cplx ZP.+-*-isCommutativeRing Hom.id-isInvolutiveRingEndo

adj-isRingHom : Hom.IsRingHom {ZComplex} {ZComplex} TC.adj
adj-isRingHom = Hom.Laws.isRingHom (CommutativeRing.isCommutativeRing gaussianRing)
  (Hom.IsInvolutiveRingEndo.isRingEndo adj-isInvolutiveRingEndo)

lift-isRingHom : Hom.IsRingHom lift
lift-isRingHom = Cplx.lift-Cplx-isRingHom ZP.+-*-isCommutativeRing

open Hom.IsRingHom lift-isRingHom public using () renaming
  (f-0 to lift-zero; f-1 to lift-one; f-neg to lift-neg; f-sub to lift-sub)
open Hom.IsRingHom adj-isRingHom public using () renaming
  (f-0 to conj-zero; f-1 to conj-one; f-neg to conj-neg; f-sub to conj-sub)

norm-isMultiplicativeHom : Hom.IsMultiplicativeHom {ZComplex} {ℤ} TC.norm
norm-isMultiplicativeHom = record { f-* = normSq-mul ; f-1 = refl }

-- Powers use the operational, repeated-squaring ^ from EucDomain.
module LiftLaws = Hom.MultiplicativeLaws {A = ℤ} {B = ZComplex}
  ZP.*-1-isCommutativeMonoid (CommutativeRing.*-isCommutativeMonoid gaussianRing)
  (Hom.IsRingHom.multiplicative lift-isRingHom)
open LiftLaws public using () renaming (f-^ to lift-power)

module NormLaws = Hom.MultiplicativeLaws {A = ZComplex} {B = ℤ}
  (CommutativeRing.*-isCommutativeMonoid gaussianRing) ZP.*-1-isCommutativeMonoid
  norm-isMultiplicativeHom
open NormLaws public using () renaming (f-^ to norm-power)

module AdjointLaws = Hom.MultiplicativeLaws {A = ZComplex} {B = ZComplex}
  (CommutativeRing.*-isCommutativeMonoid gaussianRing) (CommutativeRing.*-isCommutativeMonoid gaussianRing)
  (Hom.IsRingHom.multiplicative adj-isRingHom)
open AdjointLaws public using () renaming (f-^ to conj-power)

-- Standard-library interfaces, including injectivity of the lifting.
open import Algebra.Morphism.Structures using (IsRingMonomorphism)

lift-isRingMonomorphism : IsRingMonomorphism (Hom.instanceRawRing ℤ) (Hom.instanceRawRing ZComplex) lift
lift-isRingMonomorphism = record
  { isRingHomomorphism = Hom.toRingHomomorphism lift-isRingHom
  ; injective = cong re }

Unit : ZComplex → Set
Unit u = u * TC.adj u ≡ 1#

unit-product : ∀ u v → Unit u → Unit v → Unit (u * v)
unit-product u v hu hv = trans (cong ((u * v) *_) (conj-mul u v))
  (trans (GaussianSolver.solve 4 (λ a b c d → (a GaussianSolver.:* b) GaussianSolver.:* (c GaussianSolver.:* d)
    GaussianSolver.:= (a GaussianSolver.:* c) GaussianSolver.:* (b GaussianSolver.:* d)) refl u v (TC.adj u) (TC.adj v))
    (cong₂ _*_ hu hv))

unit-unscale : ∀ u x → Unit u → TC.adj u * (u * x) ≡ x
unit-unscale u x hu = trans (sym (*-assoc (TC.adj u) u x))
  (trans (cong (_* x) (trans (*-comm (TC.adj u) u) hu)) (*-identityˡ x))

unit-conjugate : ∀ u → Unit u → Unit (TC.adj u)
unit-conjugate u h = trans (cong (TC.adj u *_) (conj-involutive u)) (trans (*-comm (TC.adj u) u) h)

unscale-zero : ∀ u x → Unit u → u * x ≡ 0# → x ≡ 0#
unscale-zero u x hu hz = trans (sym (unit-unscale u x hu))
  (trans (cong (TC.adj u *_) hz) (CommutativeRing.zeroʳ gaussianRing (TC.adj u)))
