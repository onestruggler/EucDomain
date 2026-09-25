-- The least denominator exponent (Definition II.1) of Bian & Feng:
-- correctness and minimality of the implementation lde of Kopt.Base,
-- Lemma II.7 (γᵏt is odd when k = lde t > 0) and Lemma II.8
-- (subadditivity of lde).

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.Lde where

open import Algebra.Structures using (IsCommutativeRing)
import Algebra.Bundles as Bundles
import Algebra.Properties.Ring
open import Level using (0ℓ)
open import Data.Bool.Base using (Bool ; true ; false ; not ; T ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim ; ⊥-elim-irr)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as IntP
import Data.Integer.DivMod as IDM
import Data.Integer.Solver as IntSolver
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
open import Kopt.Properties.Gamma
open import Kopt.Properties.DyadicTools

private
  module ℤS = IntSolver.+-*-Solver
  module ZS = ZSolver commutativeRing-ZComplex
  module DR = IsCommutativeRing isCommutativeRing-DComplex
  module 𝔻R = IsCommutativeRing isCommutativeRing-𝔻
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex

-- ----------------------------------------------------------------------
-- * Rearrangements in a commutative ring
--
-- The ring solver is not used for 𝔻[i]: normalising a 𝔻[i] term that
-- contains a variable is extremely expensive (the dyadic fractions
-- are a record type with a smart constructor, so every product is
-- unfolded into stuck applications of "dyadic"). The following
-- rearrangements are enough, and each is a handful of applications of
-- associativity and commutativity.

module CRLemmas {A : Set} {{_ : Ring A}}
                (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  private
    module R = IsCommutativeRing isCR
    ringB : Bundles.Ring 0ℓ 0ℓ
    ringB = record { isRing = R.isRing }

  open Algebra.Properties.Ring ringB public using (-‿involutive ; -‿distribˡ-* ; -‿+-comm)

  -- (x+y)+(z+w) = (x+z)+(y+w)
  +-interchange : ∀ (x y z w : A) -> (x + y) + (z + w) ≡ (x + z) + (y + w)
  +-interchange x y z w = trans (R.+-assoc x y (z + w))
    (trans (cong (λ u -> x + u) (+-swapˡ y z w)) (sym (R.+-assoc x z (y + w))))
    where
      +-swapˡ : ∀ (p q r : A) -> p + (q + r) ≡ q + (p + r)
      +-swapˡ p q r = trans (sym (R.+-assoc p q r))
                            (trans (cong (λ u -> u + r) (R.+-comm p q)) (R.+-assoc q p r))

  -- (x-y)z = xz - yz
  minus-distribʳ : ∀ (x y z : A) -> (x - y) * z ≡ x * z - y * z
  minus-distribʳ x y z = trans (R.distribʳ z x (- y))
    (cong (λ u -> x * z + u) (sym (-‿distribˡ-* y z)))

  -- x(yz) = y(xz)
  swapˡ : ∀ (x y z : A) -> x * (y * z) ≡ y * (x * z)
  swapˡ x y z = trans (sym (R.*-assoc x y z))
                      (trans (cong (λ w -> w * z) (R.*-comm x y)) (R.*-assoc y x z))

  -- (xy)z = (xz)y
  swapʳ : ∀ (x y z : A) -> (x * y) * z ≡ (x * z) * y
  swapʳ x y z = trans (R.*-assoc x y z)
                      (trans (cong (λ w -> x * w) (R.*-comm y z)) (sym (R.*-assoc x z y)))

  -- x(yz) = (xz)y
  assoc-swap : ∀ (x y z : A) -> x * (y * z) ≡ (x * z) * y
  assoc-swap x y z = trans (swapˡ x y z) (R.*-comm y (x * z))

  -- (xy)(zw) = (xz)(yw)
  interchange : ∀ (x y z w : A) -> (x * y) * (z * w) ≡ (x * z) * (y * w)
  interchange x y z w = trans (R.*-assoc x y (z * w))
    (trans (cong (λ u -> x * u) (swapˡ y z w)) (sym (R.*-assoc x z (y * w))))

  -- (xy)(zw) = (xw)(yz)
  interchange2 : ∀ (x y z w : A) -> (x * y) * (z * w) ≡ (x * w) * (y * z)
  interchange2 x y z w = trans (cong (λ u -> (x * y) * u) (R.*-comm z w)) (interchange x y w z)

module DL = CRLemmas {DComplex} isCommutativeRing-DComplex

private

  true≢false : true ≡ false -> ⊥
  true≢false ()

  re-eq : ∀ {A : Set} {x y u v : A} -> Cplx x y ≡ Cplx u v -> x ≡ u
  re-eq refl = refl

  im-eq : ∀ {A : Set} {x y u v : A} -> Cplx x y ≡ Cplx u v -> y ≡ v
  im-eq refl = refl

  recompute-T : ∀ b -> .(T b) -> T b
  recompute-T true _ = tt
  recompute-T false p = ⊥-elim-irr p

  T-not⇒false : ∀ {x} -> T (not x) -> x ≡ false
  T-not⇒false {false} _ = refl

  pos⇒suc : ∀ z -> 0 Nat.< z -> ∃ λ r -> z ≡ suc r
  pos⇒suc (suc r) _ = r , refl

-- ----------------------------------------------------------------------
-- * Powers

↑-+ : {A : Set} {{_ : Ring A}} ->
      IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1# ->
      ∀ (x : A) m n -> x ↑ (m Nat.+ n) ≡ (x ↑ m) * (x ↑ n)
↑-+ isCR x zero n = sym (IsCommutativeRing.*-identityˡ isCR (x ↑ n))
↑-+ isCR x (suc m) n = trans (cong (λ z -> x * z) (↑-+ isCR x m n))
                             (sym (IsCommutativeRing.*-assoc isCR x (x ↑ m) (x ↑ n)))

-- ----------------------------------------------------------------------
-- * Multiplying a dyadic fraction by a power of two

private
  2𝔻 : Dyadic
  2𝔻 = fromℕ 2

  even⇒%2≡0 : ∀ a -> evenℤ a ≡ true -> a Int.%ℕ 2 ≡ 0
  even⇒%2≡0 (+ n) eq = NatP.≡ᵇ⇒≡ (n Nat.% 2) 0 (subst T (sym eq) tt)
  even⇒%2≡0 -[1+ n ] eq with suc n Nat.% 2 | NatP.≡ᵇ⇒≡ (suc n Nat.% 2) 0 (subst T (sym eq) tt)
  ... | zero | _ = refl
  ... | suc _ | ()

  shiftR-even : ∀ a -> evenℤ a ≡ true -> shiftR a 1 * (+ 2) ≡ a
  shiftR-even a eq = sym (begin
    a                                       ≡⟨ IDM.a≡a%n+[a/n]*n a (+ 2) ⟩
    + (a Int.%ℕ 2) + shiftR a 1 * (+ 2)     ≡⟨ cong (λ r -> + r + shiftR a 1 * (+ 2)) (even⇒%2≡0 a eq) ⟩
    + 0 + shiftR a 1 * (+ 2)                ≡⟨ IntP.+-identityˡ _ ⟩
    shiftR a 1 * (+ 2)                      ∎)
    where open ≡-Reasoning

  even-*2 : ∀ a -> evenℤ (a * (+ 2)) ≡ true
  even-*2 a = trans (cong evenℤ (IntP.*-comm a (+ 2))) (even-2* a)

  shiftR-*2 : ∀ a -> shiftR (a * (+ 2)) 1 ≡ a
  shiftR-*2 a = IntP.*-cancelʳ-≡ (shiftR (a * (+ 2)) 1) a (+ 2) (shiftR-even (a * (+ 2)) (even-*2 a))

-- (a/2ⁿ⁺¹)·2 = a/2ⁿ.
dyadic-half : ∀ a n (c : T (Canonical a (suc n))) (c' : T (Canonical a n)) ->
              Dyadic' a (suc n) c * 2𝔻 ≡ Dyadic' a n c'
dyadic-half a n c c' = begin
  Dyadic' a (suc n) c * 2𝔻        ≡⟨ cong (λ j -> dyadic (a * (+ 2)) j) (NatP.+-identityʳ (suc n)) ⟩
  dyadic (a * (+ 2)) (suc n)      ≡⟨ dyadic-even-step (a * (+ 2)) n (subst T (sym (even-*2 a)) tt) ⟩
  dyadic (shiftR (a * (+ 2)) 1) n ≡⟨ cong (λ z -> dyadic z n) (shiftR-*2 a) ⟩
  dyadic a n                      ≡⟨ dyadic-canon a n c' ⟩
  Dyadic' a n c'                  ∎
  where open ≡-Reasoning

-- (a/2ᵏ)·2ᵏ = a.
dyadic-shift0 : ∀ a k (c : T (Canonical a k)) -> Dyadic' a k c * (2𝔻 ↑ k) ≡ from-whole a
dyadic-shift0 a zero c = begin
  Dyadic' a 0 c * 1#              ≡⟨ cong (λ z -> dyadic z 0) (IntP.*-identityʳ a) ⟩
  dyadic a 0                      ≡⟨ dyadic-canon a 0 (canon-0 a) ⟩
  Dyadic' a 0 (canon-0 a)         ≡⟨ sym (fromℤ-Dyadic a) ⟩
  from-whole a                    ∎
  where open ≡-Reasoning
dyadic-shift0 a (suc k) c = begin
  Dyadic' a (suc k) c * (2𝔻 * (2𝔻 ↑ k))   ≡⟨ sym (𝔻R.*-assoc (Dyadic' a (suc k) c) 2𝔻 (2𝔻 ↑ k)) ⟩
  (Dyadic' a (suc k) c * 2𝔻) * (2𝔻 ↑ k)   ≡⟨ cong (λ z -> z * (2𝔻 ↑ k)) (dyadic-half a k c c') ⟩
  Dyadic' a k c' * (2𝔻 ↑ k)               ≡⟨ dyadic-shift0 a k c' ⟩
  from-whole a                            ∎
  where
    open ≡-Reasoning
    c' : T (Canonical a k)
    c' = canon-odd a k (canonical-odd a k c)

private
  2𝔻↑ : ∀ d -> (2𝔻 ↑ d) ≡ from-whole (+ (2 Nat.^ d))
  2𝔻↑ zero = refl
  2𝔻↑ (suc d) = begin
    2𝔻 * (2𝔻 ↑ d)                                 ≡⟨ cong (λ z -> 2𝔻 * z) (2𝔻↑ d) ⟩
    from-whole (+ 2) * from-whole (+ (2 Nat.^ d))  ≡⟨ sym (fromℤ-* (+ 2) (+ (2 Nat.^ d))) ⟩
    from-whole ((+ 2) * (+ (2 Nat.^ d)))           ≡⟨ cong (λ z -> Dyadic ∋ from-whole z)
                                                        (sym (IntP.pos-* 2 (2 Nat.^ d))) ⟩
    from-whole (+ (2 Nat.^ suc d))                 ∎
    where open ≡-Reasoning

-- (a/2ᵏ)·2ᵏ⁺ᵈ = a·2ᵈ.
dyadic-scale : ∀ a k d (c : T (Canonical a k)) ->
               Dyadic' a k c * (2𝔻 ↑ (k Nat.+ d)) ≡ from-whole (a * (+ (2 Nat.^ d)))
dyadic-scale a k d c = begin
  Dyadic' a k c * (2𝔻 ↑ (k Nat.+ d))           ≡⟨ cong (λ z -> Dyadic' a k c * z)
                                                    (↑-+ isCommutativeRing-𝔻 2𝔻 k d) ⟩
  Dyadic' a k c * ((2𝔻 ↑ k) * (2𝔻 ↑ d))        ≡⟨ sym (𝔻R.*-assoc (Dyadic' a k c) (2𝔻 ↑ k) (2𝔻 ↑ d)) ⟩
  (Dyadic' a k c * (2𝔻 ↑ k)) * (2𝔻 ↑ d)        ≡⟨ cong (λ z -> z * (2𝔻 ↑ d)) (dyadic-shift0 a k c) ⟩
  from-whole a * (2𝔻 ↑ d)                      ≡⟨ cong (λ z -> from-whole a * z) (2𝔻↑ d) ⟩
  from-whole a * from-whole (+ (2 Nat.^ d))    ≡⟨ sym (fromℤ-* a (+ (2 Nat.^ d))) ⟩
  from-whole (a * (+ (2 Nat.^ d)))             ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * Powers of two and of γ in 𝔻[i]

private
  2ℂ : DComplex
  2ℂ = fromℕ 2

  Cplx-real-* : ∀ (x y p : Dyadic) -> Cplx x y * Cplx p 0# ≡ Cplx (x * p) (y * p)
  Cplx-real-* x y p = cong₂ Cplx
    (trans (cong (λ z -> x * p - z) (𝔻R.zeroʳ y)) (𝔻R.+-identityʳ (x * p)))
    (trans (cong (λ z -> z + y * p) (𝔻R.zeroʳ x)) (𝔻R.+-identityˡ (y * p)))

  2ℂ↑ : ∀ m -> (2ℂ ↑ m) ≡ Cplx (2𝔻 ↑ m) 0#
  2ℂ↑ zero = refl
  2ℂ↑ (suc m) = begin
    2ℂ * (2ℂ ↑ m)                         ≡⟨ cong (λ z -> 2ℂ * z) (2ℂ↑ m) ⟩
    Cplx 2𝔻 0# * Cplx (2𝔻 ↑ m) 0#         ≡⟨ Cplx-real-* 2𝔻 0# (2𝔻 ↑ m) ⟩
    Cplx (2𝔻 * (2𝔻 ↑ m)) (0# * (2𝔻 ↑ m))  ≡⟨ cong (λ z -> Cplx (2𝔻 * (2𝔻 ↑ m)) z) (𝔻R.zeroˡ (2𝔻 ↑ m)) ⟩
    Cplx (2𝔻 ↑ suc m) 0#                  ∎
    where open ≡-Reasoning

  2ℤℂ : ZComplex
  2ℤℂ = fromℕ 2

  γ-sq-ℤ : (γ {ZComplex}) * γ ≡ i * 2ℤℂ
  γ-sq-ℤ = refl

  -- γ^(2m) = iᵐ2ᵐ in ℤ[i], since γ² = 2i.
  γ↑even-ℤ : ∀ m -> ((γ {ZComplex}) ↑ (m Nat.+ m)) ≡ (i ↑ m) * (2ℤℂ ↑ m)
  γ↑even-ℤ zero = refl
  γ↑even-ℤ (suc m) = begin
    γ ↑ (suc m Nat.+ suc m)               ≡⟨ cong (λ n -> (γ {ZComplex}) ↑ suc n) (NatP.+-suc m m) ⟩
    γ * (γ * (γ ↑ (m Nat.+ m)))           ≡⟨ cong (λ z -> γ * (γ * z)) (γ↑even-ℤ m) ⟩
    γ * (γ * ((i ↑ m) * (2ℤℂ ↑ m)))       ≡⟨ sym (ZR.*-assoc γ γ ((i ↑ m) * (2ℤℂ ↑ m))) ⟩
    (γ * γ) * ((i ↑ m) * (2ℤℂ ↑ m))       ≡⟨ cong (λ z -> z * ((i ↑ m) * (2ℤℂ ↑ m))) γ-sq-ℤ ⟩
    (i * 2ℤℂ) * ((i ↑ m) * (2ℤℂ ↑ m))     ≡⟨ solve 4 (λ p q r s -> (p :* q) :* (r :* s) := (p :* r) :* (q :* s))
                                               refl i 2ℤℂ (i ↑ m) (2ℤℂ ↑ m) ⟩
    (i * (i ↑ m)) * (2ℤℂ * (2ℤℂ ↑ m))     ∎
    where
      open ≡-Reasoning
      open ZS

  -- The same in 𝔻[i], by transporting along from-whole.
  γ↑even : ∀ m -> ((γ {DComplex}) ↑ (m Nat.+ m)) ≡ (i ↑ m) * (2ℂ ↑ m)
  γ↑even m = begin
    (γ {DComplex}) ↑ (m Nat.+ m)                     ≡⟨ sym (from-whole-γ↑ (m Nat.+ m)) ⟩
    from-whole ((γ {ZComplex}) ↑ (m Nat.+ m))        ≡⟨ cong (λ z -> DComplex ∋ from-whole z) (γ↑even-ℤ m) ⟩
    from-whole ((i ↑ m) * (2ℤℂ ↑ m))                 ≡⟨ from-whole-* (i ↑ m) (2ℤℂ ↑ m) ⟩
    from-whole (i ↑ m) * from-whole (2ℤℂ ↑ m)        ≡⟨ cong₂ (λ p q -> p * q) (from-whole-↑ i m) (from-whole-↑ 2ℤℂ m) ⟩
    (i ↑ m) * (2ℂ ↑ m)                               ∎
    where open ≡-Reasoning

  invγ : DComplex
  invγ = 1/γ

  invγ-γ : invγ * γ ≡ 1#
  invγ-γ = refl

  γ-invγ : (γ {DComplex}) * invγ ≡ 1#
  γ-invγ = refl

-- ----------------------------------------------------------------------
-- * Denominators, over variables
--
-- These are the first of the lemmas that Kopt.Properties.LdeVars
-- explains and continues: 𝔻[i] equations stated over VARIABLES g (for
-- γ), u (for 1/γ), p (for γ↑l) and q (for γ↑(l+1)), with every
-- equation that a reasoning chain would otherwise obtain by
-- *conversion* turned into a hypothesis matched against refl. The
-- conversion checker must never be asked to decide that two different
-- expressions denote the same concrete element of 𝔻[i] (Dyadic and
-- _[i]_ are records with eta, so such a decision unfolds the whole
-- dyadic arithmetic); at the use sites below, the conclusion of the
-- instantiated lemma is syntactically the goal, so no conversion
-- happens there either. They live in this module, rather than in
-- Kopt.Properties.LdeVars, because this module needs them too and is
-- below it in the import order.

-- x↑(n+1) = x·x↑n. For a variable base this is refl, so instantiating
-- it at γ is instantiation and not conversion.
↑-suc : ∀ (g : DComplex) (n : ℕ) -> g ↑ suc n ≡ g * (g ↑ n)
↑-suc g n = refl

-- (g·z)/g = z and z·(g/g) = z, for a right or left inverse of g.
unit-elimʳ : ∀ (g u z : DComplex) -> g * u ≡ 1# -> (g * z) * u ≡ z
unit-elimʳ g u z e =
  trans (DL.swapʳ g z u) (trans (cong (λ w -> w * z) e) (DR.*-identityˡ z))

unit-elimˡ : ∀ (g u z : DComplex) -> u * g ≡ 1# -> z * (u * g) ≡ z
unit-elimˡ g u z e = trans (cong (λ w -> z * w) e) (DR.*-identityʳ z)

-- One more factor of g in the denominator: t·q is gz·z when t·p is z.
whole-suc : ∀ (t g p q : DComplex) (gz z : ZComplex) ->
            (DComplex ∋ from-whole gz) ≡ g -> q ≡ g * p ->
            t * p ≡ from-whole z -> t * q ≡ from-whole (gz * z)
whole-suc t g p q gz z hgz refl h = begin
  t * (g * p)                   ≡⟨ DL.assoc-swap t g p ⟩
  (t * p) * g                   ≡⟨ cong (λ w -> w * g) h ⟩
  from-whole z * g              ≡⟨ cong (λ w -> from-whole z * w) (sym hgz) ⟩
  from-whole z * from-whole gz  ≡⟨ sym (from-whole-* z gz) ⟩
  from-whole (z * gz)           ≡⟨ cong (λ w -> DComplex ∋ from-whole w) (ZR.*-comm z gz) ⟩
  from-whole (gz * z)           ∎
  where open ≡-Reasoning

-- One fewer: if t·q is the *even* Gaussian integer gz·y, then t·p is
-- already y. (The chain multiplies by u on the right throughout. The
-- more obvious form, which rewrites 1# into u·g on the left, has a
-- concrete 1# -- an element of 𝔻[i] -- next to the variables in every
-- step, and that alone costs 295 s of type checking instead of 6 s.)
whole-pred : ∀ (t u g p q : DComplex) (gz y : ZComplex) ->
             (DComplex ∋ from-whole gz) ≡ g -> g * u ≡ 1# -> q ≡ g * p ->
             t * q ≡ from-whole (gz * y) -> t * p ≡ from-whole y
whole-pred t u g p q gz y hgz gu refl h = begin
  t * p                               ≡⟨ sym (unit-elimʳ g u (t * p) gu) ⟩
  (g * (t * p)) * u                   ≡⟨ cong (λ z -> z * u) (DL.swapˡ g t p) ⟩
  (t * (g * p)) * u                   ≡⟨ cong (λ z -> z * u) h ⟩
  from-whole (gz * y) * u             ≡⟨ cong (λ z -> z * u) (from-whole-* gz y) ⟩
  (from-whole gz * from-whole y) * u  ≡⟨ cong (λ z -> (z * from-whole y) * u) hgz ⟩
  (g * from-whole y) * u              ≡⟨ unit-elimʳ g u (from-whole y) gu ⟩
  from-whole y                        ∎
  where open ≡-Reasoning

-- γ can be cancelled in 𝔻[i] (it is invertible there).
γ-cancelˡ : ∀ (x y : DComplex) -> γ * x ≡ γ * y -> x ≡ y
γ-cancelˡ x y e = begin
  x                 ≡⟨ sym (DR.*-identityˡ x) ⟩
  1# * x            ≡⟨ cong (λ z -> z * x) (sym invγ-γ) ⟩
  (invγ * γ) * x    ≡⟨ DR.*-assoc invγ γ x ⟩
  invγ * (γ * x)    ≡⟨ cong (λ z -> invγ * z) e ⟩
  invγ * (γ * y)    ≡⟨ sym (DR.*-assoc invγ γ y) ⟩
  (invγ * γ) * y    ≡⟨ cong (λ z -> z * y) invγ-γ ⟩
  1# * y            ≡⟨ DR.*-identityˡ y ⟩
  y                 ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * Multiplication by a power of i does not change the parity

private
  parity-i* : ∀ (x : ZComplex) -> parityℤ[i] (i * x) ≡ parityℤ[i] x
  parity-i* (Cplx a b) = cong (λ z -> if z then Even else Odd)
    (even-cong-2 (((+ 0) * a - (+ 1) * b) + ((+ 0) * b + (+ 1) * a)) (a + b) (Int.- b) lemma)
    where
      open ℤS
      lemma : ((+ 0) * a - (+ 1) * b) + ((+ 0) * b + (+ 1) * a) ≡ (a + b) + (+ 2) * (Int.- b)
      lemma = solve 2 (λ x y -> (con (+ 0) :* x :- con (+ 1) :* y) :+ (con (+ 0) :* y :+ con (+ 1) :* x)
                          := (x :+ y) :+ con (+ 2) :* (:- y)) refl a b

  parity-i↑ : ∀ m (x : ZComplex) -> parityℤ[i] ((i ↑ m) * x) ≡ parityℤ[i] x
  parity-i↑ zero x = cong parityℤ[i] (ZR.*-identityˡ x)
  parity-i↑ (suc m) x = begin
    parityℤ[i] ((i * (i ↑ m)) * x)   ≡⟨ cong parityℤ[i] (ZR.*-assoc i (i ↑ m) x) ⟩
    parityℤ[i] (i * ((i ↑ m) * x))   ≡⟨ parity-i* ((i ↑ m) * x) ⟩
    parityℤ[i] ((i ↑ m) * x)         ≡⟨ parity-i↑ m x ⟩
    parityℤ[i] x                     ∎
    where open ≡-Reasoning

  -- (-i)ᵐiᵐ = 1.
  i-inv : ∀ m -> ((- i) ↑ m) * ((i {ZComplex}) ↑ m) ≡ 1#
  i-inv zero = refl
  i-inv (suc m) = begin
    ((- i) * ((- i) ↑ m)) * (i * (i ↑ m))      ≡⟨ solve 4 (λ u v p q -> (u :* p) :* (v :* q) := (v :* u) :* (p :* q))
                                                    refl (- i) i ((- i) ↑ m) ((i {ZComplex}) ↑ m) ⟩
    ((i {ZComplex}) * (- i)) * (((- i) ↑ m) * (i ↑ m))
                                               ≡⟨ cong (λ z -> ((i {ZComplex}) * (- i)) * z) (i-inv m) ⟩
    ((i {ZComplex}) * (- i)) * 1#              ≡⟨ ZR.*-identityʳ ((i {ZComplex}) * (- i)) ⟩
    1#                                         ∎
    where
      open ≡-Reasoning
      open ZS

  -- The components of 2z are even.
  even-of-2* : ∀ (A' B' : ℤ) (v : ZComplex) -> Cplx A' B' ≡ fromℕ 2 * v ->
               (evenℤ A' ≡ true) × (evenℤ B' ≡ true)
  even-of-2* A' B' (Cplx p q) e =
    trans (cong evenℤ (trans (re-eq e) lemA)) (even-2* p) ,
    trans (cong evenℤ (trans (im-eq e) lemB)) (even-2* q)
    where
      open ℤS
      lemA : (+ 2) * p - (+ 0) * q ≡ (+ 2) * p
      lemA = solve 2 (λ x y -> con (+ 2) :* x :- con (+ 0) :* y := con (+ 2) :* x) refl p q
      lemB : (+ 2) * q + (+ 0) * p ≡ (+ 2) * q
      lemB = solve 2 (λ x y -> con (+ 2) :* x :+ con (+ 0) :* y := con (+ 2) :* x) refl q p

-- ----------------------------------------------------------------------
-- * Denominator exponents (Definition II.1)

-- k is a denominator exponent of t if γᵏt is a Gaussian integer.
-- (A record rather than a Σ-type, so that k and t can be inferred
-- from a proof: unifying a product in 𝔻[i] with a meta is hopeless.)
record DenomExpγ (k : ℕ) (t : DComplex) : Set where
  constructor denom-exp
  field
    whole : ZComplex
    whole-eq : t * (γ ↑ k) ≡ from-whole whole
open DenomExpγ public

-- Denominator exponents are closed upwards.
DenomExpγ-suc : ∀ (k : ℕ) (t : DComplex) -> DenomExpγ k t -> DenomExpγ (suc k) t
DenomExpγ-suc k t (denom-exp z h) =
  denom-exp (γ * z) (whole-suc t γ (γ ↑ k) (γ ↑ suc k) γ z from-whole-γ (↑-suc γ k) h)

DenomExpγ-≤′ : ∀ {j k : ℕ} {t : DComplex} -> j Nat.≤′ k -> DenomExpγ j t -> DenomExpγ k t
DenomExpγ-≤′ Nat.≤′-refl h = h
DenomExpγ-≤′ {j} {suc k} {t} (Nat.≤′-step p) h = DenomExpγ-suc k t (DenomExpγ-≤′ p h)

DenomExpγ-≤ : ∀ {j k : ℕ} {t : DComplex} -> j Nat.≤ k -> DenomExpγ j t -> DenomExpγ k t
DenomExpγ-≤ p h = DenomExpγ-≤′ (NatP.≤⇒≤′ p) h

-- ----------------------------------------------------------------------
-- * The analysis of t = a/2ᵏ + (b/2ˡ)i

module _ (a : ℤ) (k : ℕ) (b : ℤ) (l : ℕ) (c : T (Canonical a k)) (d : T (Canonical b l)) where

  private
    t : DComplex
    t = Cplx (Dyadic' a k c) (Dyadic' b l d)

    m : ℕ
    m = max k l

    A B : ℤ
    A = a * (+ (2 Nat.^ (m Nat.∸ k)))
    B = b * (+ (2 Nat.^ (m Nat.∸ l)))

    Z W : ZComplex
    Z = Cplx A B
    W = (i ↑ m) * Z

  -- m = max k l is one of k and l.
  max-cases : (max k l ≡ l × k Nat.≤ l) ⊎ (max k l ≡ k × l Nat.≤ k)
  max-cases with k Nat.≤ᵇ l in le
  ... | true = inj₁ (refl , NatP.≤ᵇ⇒≤ k l (subst T (sym le) tt))
  ... | false = inj₂ (refl , NatP.≰⇒≥ (λ h -> subst T le (NatP.≤⇒≤ᵇ h)))

  k≤m : k Nat.≤ m
  k≤m with max-cases
  ... | inj₁ (e , p) = subst (λ n -> k Nat.≤ n) (sym e) p
  ... | inj₂ (e , p) = subst (λ n -> k Nat.≤ n) (sym e) NatP.≤-refl

  l≤m : l Nat.≤ m
  l≤m with max-cases
  ... | inj₁ (e , p) = subst (λ n -> l Nat.≤ n) (sym e) NatP.≤-refl
  ... | inj₂ (e , p) = subst (λ n -> l Nat.≤ n) (sym e) p

  -- t·2ᵐ is the Gaussian integer Z = A + Bi.
  t-2 : t * (2ℂ ↑ m) ≡ from-whole Z
  t-2 = begin
    t * (2ℂ ↑ m)                             ≡⟨ cong (λ z -> t * z) (2ℂ↑ m) ⟩
    Cplx x y * Cplx (2𝔻 ↑ m) 0#              ≡⟨ Cplx-real-* x y (2𝔻 ↑ m) ⟩
    Cplx (x * (2𝔻 ↑ m)) (y * (2𝔻 ↑ m))       ≡⟨ cong₂ Cplx lemA lemB ⟩
    Cplx (from-whole A) (from-whole B)       ∎
    where
      open ≡-Reasoning
      x : Dyadic
      x = Dyadic' a k c
      y : Dyadic
      y = Dyadic' b l d
      lemA : x * (2𝔻 ↑ m) ≡ from-whole A
      lemA = subst (λ j -> x * (2𝔻 ↑ j) ≡ from-whole A) (NatP.m+[n∸m]≡n k≤m)
                   (dyadic-scale a k (m Nat.∸ k) c)
      lemB : y * (2𝔻 ↑ m) ≡ from-whole B
      lemB = subst (λ j -> y * (2𝔻 ↑ j) ≡ from-whole B) (NatP.m+[n∸m]≡n l≤m)
                   (dyadic-scale b l (m Nat.∸ l) d)

  -- t·γ²ᵐ is the Gaussian integer W = iᵐZ.
  t-γ : t * (γ ↑ (m Nat.+ m)) ≡ from-whole W
  t-γ = begin
    t * (γ ↑ (m Nat.+ m))               ≡⟨ cong (λ z -> t * z) (γ↑even m) ⟩
    t * ((i ↑ m) * (2ℂ ↑ m))            ≡⟨ DL.swapˡ t (i ↑ m) (2ℂ ↑ m) ⟩
    (i ↑ m) * (t * (2ℂ ↑ m))            ≡⟨ cong (λ z -> (i ↑ m) * z) t-2 ⟩
    (i ↑ m) * from-whole Z              ≡⟨ cong (λ z -> z * from-whole Z) (sym (from-whole-↑ i m)) ⟩
    from-whole (i ↑ m) * from-whole Z   ≡⟨ sym (from-whole-* (i ↑ m) Z) ⟩
    from-whole ((i ↑ m) * Z)            ∎
    where
      open ≡-Reasoning

  -- W and Z have the same parity.
  W-parity : parityℤ[i] W ≡ parityℤ[i] Z
  W-parity = parity-i↑ m Z

  -- Z = (-i)ᵐW.
  Z-of-W : Z ≡ ((- i) ↑ m) * W
  Z-of-W = begin
    Z                                  ≡⟨ sym (ZR.*-identityˡ Z) ⟩
    1# * Z                             ≡⟨ cong (λ z -> z * Z) (sym (i-inv m)) ⟩
    (((- i) ↑ m) * (i ↑ m)) * Z        ≡⟨ ZR.*-assoc ((- i) ↑ m) (i ↑ m) Z ⟩
    ((- i) ↑ m) * ((i ↑ m) * Z)        ∎
    where open ≡-Reasoning

  -- Any denominator exponent j ≤ 2m yields a divisor of W.
  denom-div : ∀ j -> j Nat.≤ (m Nat.+ m) -> DenomExpγ j t ->
              ∃ λ U -> W ≡ U * (γ ↑ ((m Nat.+ m) Nat.∸ j))
  denom-div j j≤ (denom-exp U h) = U , from-whole-injective (begin
    from-whole W                                     ≡⟨ sym t-γ ⟩
    t * (γ ↑ (m Nat.+ m))                            ≡⟨ cong (λ n -> t * (γ ↑ n)) (sym (NatP.m+[n∸m]≡n j≤)) ⟩
    t * (γ ↑ (j Nat.+ ((m Nat.+ m) Nat.∸ j)))        ≡⟨ cong (λ z -> t * z)
                                                          (↑-+ isCommutativeRing-DComplex γ j ((m Nat.+ m) Nat.∸ j)) ⟩
    t * ((γ ↑ j) * (γ ↑ ((m Nat.+ m) Nat.∸ j)))      ≡⟨ sym (DR.*-assoc t (γ ↑ j) (γ ↑ ((m Nat.+ m) Nat.∸ j))) ⟩
    (t * (γ ↑ j)) * (γ ↑ ((m Nat.+ m) Nat.∸ j))      ≡⟨ cong (λ z -> z * (γ ↑ ((m Nat.+ m) Nat.∸ j))) h ⟩
    from-whole U * (γ ↑ ((m Nat.+ m) Nat.∸ j))       ≡⟨ cong (λ z -> from-whole U * z)
                                                          (sym (from-whole-γ↑ ((m Nat.+ m) Nat.∸ j))) ⟩
    from-whole U * from-whole (γ ↑ ((m Nat.+ m) Nat.∸ j))
                                                     ≡⟨ sym (from-whole-* U (γ ↑ ((m Nat.+ m) Nat.∸ j))) ⟩
    from-whole (U * (γ ↑ ((m Nat.+ m) Nat.∸ j)))     ∎)
    where open ≡-Reasoning

  -- If m > 0 then A or B is odd.
  AB-odd : ∀ m' -> max k l ≡ suc m' -> (evenℤ A ≡ false) ⊎ (evenℤ B ≡ false)
  AB-odd m' em with max-cases
  ... | inj₁ (e , p) = inj₂ (trans (cong evenℤ Beq) (T-not⇒false b-odd))
    where
      l≡ : l ≡ suc m'
      l≡ = trans (sym e) em
      b-odd : T (not (evenℤ b))
      b-odd = canonical-odd b m' (subst (λ n -> T (Canonical b n)) l≡ d)
      Beq : B ≡ b
      Beq = trans (cong (λ n -> b * (+ (2 Nat.^ n))) (trans (cong (λ z -> z Nat.∸ l) e) (NatP.n∸n≡0 l)))
                  (IntP.*-identityʳ b)
  ... | inj₂ (e , p) = inj₁ (trans (cong evenℤ Aeq) (T-not⇒false a-odd))
    where
      k≡ : k ≡ suc m'
      k≡ = trans (sym e) em
      a-odd : T (not (evenℤ a))
      a-odd = canonical-odd a m' (subst (λ n -> T (Canonical a n)) k≡ c)
      Aeq : A ≡ a
      Aeq = trans (cong (λ n -> a * (+ (2 Nat.^ n))) (trans (cong (λ z -> z Nat.∸ k) e) (NatP.n∸n≡0 k)))
                  (IntP.*-identityʳ a)

  -- The value of lde, in terms of A and B.
  private
    shiftL-AB : ∀ m' -> max k l ≡ suc m' ->
                evenℤ (shiftL a (suc m' Nat.∸ k) + shiftL b (suc m' Nat.∸ l)) ≡ evenℤ (A + B)
    shiftL-AB m' em = cong evenℤ (cong₂ Int._+_
      (trans (shiftL≡ a (suc m' Nat.∸ k)) (cong (λ n -> a * (+ (2 Nat.^ (n Nat.∸ k)))) (sym em)))
      (trans (shiftL≡ b (suc m' Nat.∸ l)) (cong (λ n -> b * (+ (2 Nat.^ (n Nat.∸ l)))) (sym em))))

  -- Case m = 0: t is already integral.
  case-0 : max k l ≡ 0 -> DenomExpγ 0 t × (∀ j -> DenomExpγ j t -> 0 Nat.≤ j)
  case-0 e = denom-exp Z (subst (λ n -> t * (2ℂ ↑ n) ≡ from-whole Z) e t-2) , (λ j _ -> z≤n)

  -- Case m = m'+1 with A + B odd: lde t = 2m.
  case-odd : ∀ m' -> max k l ≡ suc m' -> evenℤ (A + B) ≡ false ->
             DenomExpγ (2 Nat.* suc m') t × (∀ j -> DenomExpγ j t -> (2 Nat.* suc m') Nat.≤ j)
  case-odd m' em ep = denom-exp W integral , minimal
    where
      open ≡-Reasoning
      mm : 2 Nat.* suc m' ≡ m Nat.+ m
      mm = trans (cong (λ n -> suc m' Nat.+ n) (NatP.+-identityʳ (suc m')))
                 (cong₂ Nat._+_ (sym em) (sym em))
      integral : t * (γ ↑ (2 Nat.* suc m')) ≡ from-whole W
      integral = subst (λ n -> t * (γ ↑ n) ≡ from-whole W) (sym mm) t-γ
      contra : ∀ j -> DenomExpγ j t -> j Nat.< (2 Nat.* suc m') -> ⊥
      contra j hj j< = true≢false (trans (sym W-even-Z) ep)
        where
          j<mm : j Nat.< (m Nat.+ m)
          j<mm = subst (λ n -> j Nat.< n) mm j<
          divW : ∃ λ U -> W ≡ U * (γ ↑ ((m Nat.+ m) Nat.∸ j))
          divW = denom-div j (NatP.<⇒≤ j<mm) hj
          r-eq : ∃ λ r -> (m Nat.+ m) Nat.∸ j ≡ suc r
          r-eq = pos⇒suc ((m Nat.+ m) Nat.∸ j) (NatP.m<n⇒0<n∸m j<mm)
          W-even : parityℤ[i] W ≡ Even
          W-even = divides⇒even W (proj₁ divW * (γ ↑ proj₁ r-eq)) (begin
            W                                                ≡⟨ proj₂ divW ⟩
            proj₁ divW * (γ ↑ ((m Nat.+ m) Nat.∸ j))         ≡⟨ cong (λ n -> proj₁ divW * (γ ↑ n)) (proj₂ r-eq) ⟩
            proj₁ divW * (γ * (γ ↑ proj₁ r-eq))              ≡⟨ solve 3 (λ u g p -> u :* (g :* p) := g :* (u :* p))
                                                                  refl (proj₁ divW) γ (γ ↑ proj₁ r-eq) ⟩
            γ * (proj₁ divW * (γ ↑ proj₁ r-eq))              ∎)
            where open ZS
          W-even-Z : evenℤ (A + B) ≡ true
          W-even-Z = even-sum A B (trans (sym W-parity) W-even)
      minimal : ∀ j -> DenomExpγ j t -> (2 Nat.* suc m') Nat.≤ j
      minimal j hj = NatP.≮⇒≥ (λ p -> contra j hj p)

  -- Case m = m'+1 with A + B even: lde t = 2m - 1.
  -- (W/γ is passed as a variable V, so that the proof below never
  -- unfolds it.)
  case-even-aux : ∀ m' -> max k l ≡ suc m' -> evenℤ (A + B) ≡ true ->
              ∀ (V : ZComplex) -> γ * V ≡ W ->
              DenomExpγ (2 Nat.* suc m' Nat.∸ 1) t × (∀ j -> DenomExpγ j t -> (2 Nat.* suc m' Nat.∸ 1) Nat.≤ j)
  case-even-aux m' em ep V γV = denom-exp V integral , minimal
    where
      open ≡-Reasoning
      M : ℕ
      M = suc m'
      mM : m ≡ M
      mM = em
      mm : m Nat.+ m ≡ suc (m Nat.+ m')
      mm = trans (cong (λ n -> m Nat.+ n) mM) (NatP.+-suc m m')
      halved : 2 Nat.* suc m' Nat.∸ 1 ≡ m Nat.+ m'
      halved = trans (cong (λ n -> (suc m' Nat.+ n) Nat.∸ 1) (NatP.+-identityʳ (suc m')))
                     (trans (NatP.+-suc m' m') (cong (λ n -> n Nat.+ m') (sym mM)))
      integral : t * (γ ↑ (2 Nat.* suc m' Nat.∸ 1)) ≡ from-whole V
      integral = subst (λ n -> t * (γ ↑ n) ≡ from-whole V) (sym halved) step
        where
          step : t * (γ ↑ (m Nat.+ m')) ≡ from-whole V
          step = whole-pred t invγ γ (γ ↑ (m Nat.+ m')) (γ ↑ (m Nat.+ m)) γ V
                            from-whole-γ γ-invγ
                            (trans (cong (λ n -> (γ {DComplex}) ↑ n) mm) (↑-suc γ (m Nat.+ m')))
                            (trans t-γ (cong (λ z -> DComplex ∋ from-whole z) (sym γV)))

      both-even : ∀ j -> DenomExpγ j t -> j Nat.< (m Nat.+ m') -> (evenℤ A ≡ true) × (evenℤ B ≡ true)
      both-even j hj j< = even-of-2* A B (((- i) ↑ m) * (i * (proj₁ divW * (γ ↑ r)))) Zeq
        where
          j≤ : j Nat.≤ (m Nat.+ m')
          j≤ = NatP.<⇒≤ j<
          j<mm : j Nat.< (m Nat.+ m)
          j<mm = subst (λ n -> j Nat.< n) (sym mm) (NatP.<-trans j< (NatP.n<1+n (m Nat.+ m')))
          divW : ∃ λ U -> W ≡ U * (γ ↑ ((m Nat.+ m) Nat.∸ j))
          divW = denom-div j (NatP.<⇒≤ j<mm) hj
          r : ℕ
          r = proj₁ (pos⇒suc ((m Nat.+ m') Nat.∸ j) (NatP.m<n⇒0<n∸m j<))
          r-eq : (m Nat.+ m) Nat.∸ j ≡ suc (suc r)
          r-eq = trans (trans (cong (λ n -> n Nat.∸ j) mm) (NatP.+-∸-assoc 1 j≤))
                       (cong suc (proj₂ (pos⇒suc ((m Nat.+ m') Nat.∸ j) (NatP.m<n⇒0<n∸m j<))))
          Weq : W ≡ fromℕ 2 * (i * (proj₁ divW * (γ ↑ r)))
          Weq = begin
            W                                                    ≡⟨ proj₂ divW ⟩
            proj₁ divW * (γ ↑ ((m Nat.+ m) Nat.∸ j))             ≡⟨ cong (λ n -> proj₁ divW * (γ ↑ n)) r-eq ⟩
            proj₁ divW * (γ * (γ * (γ ↑ r)))                     ≡⟨ solve 3 (λ u g p -> u :* (g :* (g :* p))
                                                                      := (g :* g) :* (u :* p))
                                                                      refl (proj₁ divW) γ (γ ↑ r) ⟩
            (γ * γ) * (proj₁ divW * (γ ↑ r))                     ≡⟨ cong (λ z -> z * (proj₁ divW * (γ ↑ r))) γ-squared ⟩
            (fromℕ 2 * i) * (proj₁ divW * (γ ↑ r))               ≡⟨ solve 3 (λ two ii p -> (two :* ii) :* p := two :* (ii :* p))
                                                                      refl (fromℕ 2) i (proj₁ divW * (γ ↑ r)) ⟩
            fromℕ 2 * (i * (proj₁ divW * (γ ↑ r)))               ∎
            where open ZS
          Zeq : Cplx A B ≡ fromℕ 2 * (((- i) ↑ m) * (i * (proj₁ divW * (γ ↑ r))))
          Zeq = begin
            Cplx A B                                             ≡⟨ Z-of-W ⟩
            ((- i) ↑ m) * W                                      ≡⟨ cong (λ z -> ((- i) ↑ m) * z) Weq ⟩
            ((- i) ↑ m) * (fromℕ 2 * (i * (proj₁ divW * (γ ↑ r))))
                                                                 ≡⟨ solve 3 (λ u two v -> u :* (two :* v) := two :* (u :* v))
                                                                      refl ((- i) ↑ m) (fromℕ 2) (i * (proj₁ divW * (γ ↑ r))) ⟩
            fromℕ 2 * (((- i) ↑ m) * (i * (proj₁ divW * (γ ↑ r))))  ∎
            where open ZS
      contra : ∀ j -> DenomExpγ j t -> j Nat.< (m Nat.+ m') -> ⊥
      contra j hj j< with AB-odd m' em
      ... | inj₁ hA = true≢false (trans (sym (proj₁ (both-even j hj j<))) hA)
      ... | inj₂ hB = true≢false (trans (sym (proj₂ (both-even j hj j<))) hB)
      minimal : ∀ j -> DenomExpγ j t -> (2 Nat.* suc m' Nat.∸ 1) Nat.≤ j
      minimal j hj = subst (λ n -> n Nat.≤ j) (sym halved)
                       (NatP.≮⇒≥ (λ p -> contra j hj p))

  case-even : ∀ m' -> max k l ≡ suc m' -> evenℤ (A + B) ≡ true ->
              DenomExpγ (2 Nat.* suc m' Nat.∸ 1) t × (∀ j -> DenomExpγ j t -> (2 Nat.* suc m' Nat.∸ 1) Nat.≤ j)
  case-even m' em ep = case-even-aux m' em ep (W /γ)
    (γ-div-even W (trans W-parity (from-even A B ep)))

  -- The value computed by lde, in the three cases. (These are proved
  -- by rewriting the maximum inside the implementation; no other
  -- reduction of a 𝔻[i] term is needed.)
  lde-0 : max k l ≡ 0 -> lde t ≡ 0
  lde-0 e rewrite e = refl

  lde-suc : ∀ m' -> max k l ≡ suc m' ->
            lde t ≡ (if evenℤ (shiftL a (suc m' Nat.∸ k) + shiftL b (suc m' Nat.∸ l))
                     then 2 Nat.* suc m' Nat.∸ 1 else 2 Nat.* suc m')
  lde-suc m' e rewrite e = refl

  lde-even : ∀ m' -> max k l ≡ suc m' -> evenℤ (A + B) ≡ true -> lde t ≡ 2 Nat.* suc m' Nat.∸ 1
  lde-even m' e ep = trans (lde-suc m' e)
    (cong (λ z -> if z then 2 Nat.* suc m' Nat.∸ 1 else 2 Nat.* suc m') (trans (shiftL-AB m' e) ep))

  lde-odd : ∀ m' -> max k l ≡ suc m' -> evenℤ (A + B) ≡ false -> lde t ≡ 2 Nat.* suc m'
  lde-odd m' e ep = trans (lde-suc m' e)
    (cong (λ z -> if z then 2 Nat.* suc m' Nat.∸ 1 else 2 Nat.* suc m') (trans (shiftL-AB m' e) ep))

  -- Correctness and minimality of lde (Definition II.1).
  -- (The case distinction is made by auxiliary functions rather than
  -- by "with", so that the goal, which contains a product in 𝔻[i], is
  -- never normalised.)
  spec : DenomExpγ (lde t) t × (∀ j -> DenomExpγ j t -> lde t Nat.≤ j)
  spec = go (max k l) refl
    where
      P : ℕ -> Set
      P n = DenomExpγ n t × (∀ j -> DenomExpγ j t -> n Nat.≤ j)
      go2 : ∀ m' -> max k l ≡ suc m' -> (bb : Bool) -> evenℤ (A + B) ≡ bb -> P (lde t)
      go2 m' e true ep = subst P (sym (lde-even m' e ep)) (case-even m' e ep)
      go2 m' e false ep = subst P (sym (lde-odd m' e ep)) (case-odd m' e ep)
      go : ∀ n -> max k l ≡ n -> P (lde t)
      go zero e = subst P (sym (lde-0 e)) (case-0 e)
      go (suc m') e = go2 m' e (evenℤ (A + B)) refl

-- ----------------------------------------------------------------------
-- * Correctness of lde

-- (These proofs are large; do not unfold them.)




-- lde t is a denominator exponent of t: γ^(lde t)·t is integral.
lde-denom-exp : ∀ (t : DComplex) -> DenomExpγ (lde t) t
lde-denom-exp (Cplx (Dyadic' a k c) (Dyadic' b l d)) =
  proj₁ (spec a k b l (recompute-T (Canonical a k) c) (recompute-T (Canonical b l) d))

-- lde t is the least denominator exponent.
lde-least : ∀ (t : DComplex) j -> DenomExpγ j t -> lde t Nat.≤ j
lde-least (Cplx (Dyadic' a k c) (Dyadic' b l d)) =
  proj₂ (spec a k b l (recompute-T (Canonical a k) c) (recompute-T (Canonical b l) d))
