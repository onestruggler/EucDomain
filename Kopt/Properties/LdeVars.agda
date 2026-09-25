-- The 𝔻[i] arithmetic behind the denominator-exponent lemmas, stated
-- over VARIABLES.
--
-- Why this module exists (type-checking performance). Dyadic and
-- _[i]_ are records with eta, so a product in 𝔻[i] never stays stuck:
-- it reduces to a Cplx of dyadic expressions, and every conversion
-- between two *different* expressions of type 𝔻[i] unfolds the whole
-- dyadic arithmetic of both sides. With the concrete constants γ,
-- 1/γ and γ↑l in the terms, the reasoning chains of
-- Kopt.Properties.LdeLemmas and Kopt.Properties.KResidue took
-- minutes each; the same chains with those constants replaced by
-- variables take a fraction of a second.
--
-- So the chains live here, with
--
--   g   for γ,        u   for 1/γ,       gz  for γ in ℤ[i],
--   p   for γ↑l,      q   for γ↑(l+1),
--
-- and with every equation that the original chains obtained *by
-- conversion* turned into an explicit hypothesis, matched against
-- refl (q ≡ g * p for γ↑(l+1) = γ·γ↑l, from-whole gz ≡ g for
-- from-whole γ = γ, u * g ≡ 1# for the inverse). Each lemma is then
-- used at the concrete constants by pure *instantiation*: the
-- conclusion of the instantiated lemma is syntactically the goal, so
-- no 𝔻[i] conversion happens at the use site either. The hypotheses
-- q ≡ g * p are discharged by ↑-suc of Kopt.Properties.Lde, which is
-- refl for a variable base and therefore costs nothing when
-- instantiated.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.LdeVars where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
open import Kopt.Properties.Gamma
open import Kopt.Properties.DyadicTools
open import Kopt.Properties.Lde

private
  module DR = IsCommutativeRing isCommutativeRing-DComplex

-- ↑-suc, unit-elimʳ, unit-elimˡ, whole-suc and whole-pred are in
-- Kopt.Properties.Lde, which needs them itself and is below this
-- module in the import order.

-- ----------------------------------------------------------------------
-- * Sums, products and unit multiples of integral multiples of p

-- p is a common denominator: if xp and yp are integral, so is (x+y)p.
whole-+ : ∀ (x y p : DComplex) (X Y : ZComplex) ->
          x * p ≡ from-whole X -> y * p ≡ from-whole Y ->
          (x + y) * p ≡ from-whole (X + Y)
whole-+ x y p X Y hx hy = begin
  (x + y) * p                   ≡⟨ DR.distribʳ p x y ⟩
  (x * p) + (y * p)             ≡⟨ cong₂ (λ a b -> a + b) hx hy ⟩
  from-whole X + from-whole Y   ≡⟨ sym (from-whole-+ X Y) ⟩
  from-whole (X + Y)            ∎
  where open ≡-Reasoning

-- The denominators multiply: (xy)(pj·pk) is integral when x·pj and
-- y·pk are.
whole-* : ∀ (x y pj pk q : DComplex) (X Y : ZComplex) -> q ≡ pj * pk ->
          x * pj ≡ from-whole X -> y * pk ≡ from-whole Y ->
          (x * y) * q ≡ from-whole (X * Y)
whole-* x y pj pk q X Y refl hx hy = begin
  (x * y) * (pj * pk)           ≡⟨ DL.interchange x y pj pk ⟩
  (x * pj) * (y * pk)           ≡⟨ cong₂ (λ a b -> a * b) hx hy ⟩
  from-whole X * from-whole Y   ≡⟨ sym (from-whole-* X Y) ⟩
  from-whole (X * Y)            ∎
  where open ≡-Reasoning

-- Multiplying by a Gaussian integer keeps the denominator.
whole-scale : ∀ (x p : DComplex) (u X : ZComplex) -> x * p ≡ from-whole X ->
              (from-whole u * x) * p ≡ from-whole (u * X)
whole-scale x p u X h = begin
  (from-whole u * x) * p          ≡⟨ DR.*-assoc (from-whole u) x p ⟩
  from-whole u * (x * p)          ≡⟨ cong (λ z -> from-whole u * z) h ⟩
  from-whole u * from-whole X     ≡⟨ sym (from-whole-* u X) ⟩
  from-whole (u * X)              ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * Passing between p = g↑l and q = g↑(l+1)

-- Dividing by g costs one more factor of g in the denominator.
whole-div : ∀ (x u g p q : DComplex) (X : ZComplex) -> u * g ≡ 1# -> q ≡ g * p ->
            x * p ≡ from-whole X -> (x * u) * q ≡ from-whole X
whole-div x u g p q X ug refl h = begin
  (x * u) * (g * p)   ≡⟨ DL.interchange2 x u g p ⟩
  (x * p) * (u * g)   ≡⟨ unit-elimˡ g u (x * p) ug ⟩
  x * p               ≡⟨ h ⟩
  from-whole X        ∎
  where open ≡-Reasoning

-- W is gz·Z, from w·q = W, w·p = Z and q = g·p (the step of Lemma
-- II.8 for odd arguments; qn is another expression for q).
whole-factor : ∀ (w g p q qn : DComplex) (gz W Z : ZComplex) ->
               (DComplex ∋ from-whole gz) ≡ g -> qn ≡ q -> q ≡ g * p ->
               w * qn ≡ from-whole W -> w * p ≡ from-whole Z ->
               (DComplex ∋ from-whole W) ≡ from-whole (Z * gz)
whole-factor w g p q qn gz W Z hgz refl refl hW hZ = begin
  from-whole W                  ≡⟨ sym hW ⟩
  w * (g * p)                   ≡⟨ DL.assoc-swap w g p ⟩
  (w * p) * g                   ≡⟨ cong (λ z -> z * g) hZ ⟩
  from-whole Z * g              ≡⟨ cong (λ z -> from-whole Z * z) (sym hgz) ⟩
  from-whole Z * from-whole gz  ≡⟨ sym (from-whole-* Z gz) ⟩
  from-whole (Z * gz)           ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * The K action: (x±y)/g
--
-- These four are the chains of Kopt.Properties.KResidue.

-- If X+Y = gz·V, then ((x+y)/g)·p is V.
whole-div-+ : ∀ (x y u g p : DComplex) (gz X Y V : ZComplex) ->
              (DComplex ∋ from-whole gz) ≡ g -> g * u ≡ 1# ->
              x * p ≡ from-whole X -> y * p ≡ from-whole Y -> X + Y ≡ gz * V ->
              ((x + y) * u) * p ≡ from-whole V
whole-div-+ x y u g p gz X Y V hgz gu hx hy e = begin
  ((x + y) * u) * p                  ≡⟨ trans (DL.swapʳ (x + y) u p)
                                          (cong (λ z -> z * u) (DR.distribʳ p x y)) ⟩
  ((x * p) + (y * p)) * u            ≡⟨ cong (λ z -> z * u) (cong₂ (λ a b -> a + b) hx hy) ⟩
  (from-whole X + from-whole Y) * u  ≡⟨ cong (λ z -> z * u) (sym (from-whole-+ X Y)) ⟩
  from-whole (X + Y) * u             ≡⟨ cong (λ z -> from-whole z * u) e ⟩
  from-whole (gz * V) * u            ≡⟨ cong (λ z -> z * u) (from-whole-* gz V) ⟩
  (from-whole gz * from-whole V) * u ≡⟨ cong (λ z -> (z * from-whole V) * u) hgz ⟩
  (g * from-whole V) * u             ≡⟨ unit-elimʳ g u (from-whole V) gu ⟩
  from-whole V                       ∎
  where open ≡-Reasoning

-- If X-Y = gz·V, then ((x-y)/g)·p is V.
whole-div-minus : ∀ (x y u g p : DComplex) (gz X Y V : ZComplex) ->
                  (DComplex ∋ from-whole gz) ≡ g -> g * u ≡ 1# ->
                  x * p ≡ from-whole X -> y * p ≡ from-whole Y -> X - Y ≡ gz * V ->
                  ((x - y) * u) * p ≡ from-whole V
whole-div-minus x y u g p gz X Y V hgz gu hx hy e = begin
  ((x - y) * u) * p                  ≡⟨ trans (DL.swapʳ (x - y) u p)
                                          (cong (λ z -> z * u) (DL.minus-distribʳ x y p)) ⟩
  ((x * p) - (y * p)) * u            ≡⟨ cong (λ z -> z * u) (cong₂ (λ a b -> a - b) hx hy) ⟩
  (from-whole X - from-whole Y) * u  ≡⟨ cong (λ z -> z * u) (sym (from-whole-minus X Y)) ⟩
  from-whole (X - Y) * u             ≡⟨ cong (λ z -> from-whole z * u) e ⟩
  from-whole (gz * V) * u            ≡⟨ cong (λ z -> z * u) (from-whole-* gz V) ⟩
  (from-whole gz * from-whole V) * u ≡⟨ cong (λ z -> (z * from-whole V) * u) hgz ⟩
  (g * from-whole V) * u             ≡⟨ unit-elimʳ g u (from-whole V) gu ⟩
  from-whole V                       ∎
  where open ≡-Reasoning

-- At one level higher, no divisibility is needed: ((x+y)/g)·q = X+Y.
whole-up-+ : ∀ (x y u g p q : DComplex) (X Y : ZComplex) -> u * g ≡ 1# -> q ≡ g * p ->
             x * p ≡ from-whole X -> y * p ≡ from-whole Y ->
             ((x + y) * u) * q ≡ from-whole (X + Y)
whole-up-+ x y u g p q X Y ug refl hx hy = begin
  ((x + y) * u) * (g * p)        ≡⟨ trans (DL.interchange2 (x + y) u g p)
                                      (cong (λ z -> z * (u * g)) (DR.distribʳ p x y)) ⟩
  ((x * p) + (y * p)) * (u * g)  ≡⟨ unit-elimˡ g u ((x * p) + (y * p)) ug ⟩
  (x * p) + (y * p)              ≡⟨ cong₂ (λ a b -> a + b) hx hy ⟩
  from-whole X + from-whole Y    ≡⟨ sym (from-whole-+ X Y) ⟩
  from-whole (X + Y)             ∎
  where open ≡-Reasoning

whole-up-minus : ∀ (x y u g p q : DComplex) (X Y : ZComplex) -> u * g ≡ 1# -> q ≡ g * p ->
                 x * p ≡ from-whole X -> y * p ≡ from-whole Y ->
                 ((x - y) * u) * q ≡ from-whole (X - Y)
whole-up-minus x y u g p q X Y ug refl hx hy = begin
  ((x - y) * u) * (g * p)        ≡⟨ trans (DL.interchange2 (x - y) u g p)
                                      (cong (λ z -> z * (u * g)) (DL.minus-distribʳ x y p)) ⟩
  ((x * p) - (y * p)) * (u * g)  ≡⟨ unit-elimˡ g u ((x * p) - (y * p)) ug ⟩
  (x * p) - (y * p)              ≡⟨ cong₂ (λ a b -> a - b) hx hy ⟩
  from-whole X - from-whole Y    ≡⟨ sym (from-whole-minus X Y) ⟩
  from-whole (X - Y)             ∎
  where open ≡-Reasoning
