{-# OPTIONS --safe --without-K #-}

-- Correctness of the operational 1+i denominator on dyadic Gaussian scalars.
module Quantum.Synthesis.Ring.Properties.GammaDenominator where

import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Ring.Properties.Dyadic as DP
import Quantum.Synthesis.Ring.Properties.DyadicComplex as D
import GauInt.Gamma as G
import GauInt.Gamma.Division as GD
import GauInt.Parity as GP
open import Instances as TC using (_+_; _*_; _^_; 1#)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; _∸_)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (ℤ; +_)
open import Data.Bool.Base using (true; false; T; if_then_else_)
open import Data.Unit.Base using (tt)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

private
  Aligned : R.Dyadic → R.Dyadic → ℤ × ℤ × ℕ → Set
  Aligned x y (a , b , k) = R.dyadic a k ≡ x × R.dyadic b k ≡ y

align-correct : ∀ x y → Aligned x y (R.align-dyadic x y)
align-correct x@(R.Dyadic' a n _) y@(R.Dyadic' b m _) with n ≤ᵇ m in eq
... | true = trans (DP.dyadic-upscale a n m (NP.≤ᵇ⇒≤ n m (subst T (sym eq) tt))) (DP.dyadic-canonical x) ,
  DP.dyadic-canonical y
... | false = DP.dyadic-canonical x ,
  trans (DP.dyadic-upscale b m n (NP.≰⇒≥ (λ h → subst T eq (NP.≤⇒≤ᵇ h)))) (DP.dyadic-canonical y)

private
  common-value : ∀ (z : R.DComplex) a b k →
    R.dyadic a k ≡ R._[i].re z → R.dyadic b k ≡ R._[i].im z →
    z ≡ D.embed (R.Cplx a b) * ((TC.½ {R.DComplex}) ^ k)
  common-value (R.Cplx x y) a b k hx hy =
    trans (cong₂ R.Cplx (trans (sym hx) (D.dyadic-value a k)) (trans (sym hy) (D.dyadic-value b k)))
      (sym (D.scale-half a b k))

  clears-common : ∀ (z : R.DComplex) (w : R.ZComplex) k →
    z ≡ D.embed w * ((TC.½ {R.DComplex}) ^ k) →
    (D.gamma ^ (k + k)) * z ≡ D.embed ((TC.i {R.ZComplex} ^ k) * w)
  clears-common z w k h =
    trans {j = g * (a * t)} (cong (g *_) {x = z} {y = a * t} h)
      (trans {j = a * (g * t)} (D.Powers.exchange g a t)
        (trans {j = a * u} (cong (a *_) {x = g * t} {y = u} (D.gamma-half-power k))
          (trans {j = u * a} (D.*-comm a u)
            (trans {j = v * a} (cong (_* a) {x = u} {y = v} (sym (D.EmbedPowers.map-power TC.i k)))
              (sym (D.embed-* (TC.i ^ k) w))))))
    where
    g = D.gamma ^ (k + k)
    a = D.embed w
    t = (TC.½ {R.DComplex}) ^ k
    u = (TC.i {R.DComplex}) ^ k
    v = D.embed ((TC.i {R.ZComplex}) ^ k)

  even-divisible : ∀ w → R.evenℤ (R._[i].re w + R._[i].im w) ≡ true → G.Evenγ w
  even-divisible w h = GP.zero-parity-even w
    (NP.≡ᵇ⇒≡ _ 0 (subst T (sym h) tt))

  cancel-cleared : (z : R.DComplex) (w q : R.ZComplex) (k : ℕ) →
    (D.gamma ^ suc k) * z ≡ D.embed w → G.γ * q ≡ w →
    (D.gamma ^ k) * z ≡ D.embed q
  cancel-cleared z w q k h divides = D.Powers.cancel-step D.inverseGamma D.gamma D.inverse-gamma
    k z (D.embed q) (trans {j = D.embed w} h factored)
    where
    factored : D.embed w ≡ D.gamma * D.embed q
    factored = trans {i = D.embed w} {j = D.embed (G.γ * q)} {k = D.gamma * D.embed q}
      (cong D.embed {x = w} {y = G.γ * q} (sym divides))
      (trans {i = D.embed (G.γ * q)} {j = D.embed G.γ * D.embed q} {k = D.gamma * D.embed q}
        (D.embed-* G.γ q) (cong (_* D.embed q) {x = D.embed G.γ} {y = D.gamma} D.embed-gamma))

-- A numerator at exactly the exponent returned by the operational formula.
-- Keep the equation outside a computational record to avoid costly positivity
-- checking of concrete dyadic arithmetic.
Clears : R.DComplex → ℕ → Set
Clears z k = Σ[ w ∈ R.ZComplex ] (D.gamma ^ k) * z ≡ D.embed w

private
  formula : ℤ → ℤ → ℕ → ℕ
  formula a b k = if R.evenℤ (a + b) then 2 * k ∸ 1 else 2 * k

  formula-clears : ∀ (z : R.DComplex) a b k →
    R.dyadic a k ≡ R._[i].re z → R.dyadic b k ≡ R._[i].im z →
    Clears z (formula a b k)
  formula-clears z a b zero ha hb with R.evenℤ (a + b)
  ... | true = R.Cplx a b , trans (D.*-identityˡ z) (sym (cong₂ R.Cplx
    (trans (sym (D.canonical (D.integer a))) ha) (trans (sym (D.canonical (D.integer b))) hb)))
  ... | false = R.Cplx a b , trans (D.*-identityˡ z) (sym (cong₂ R.Cplx
    (trans (sym (D.canonical (D.integer a))) ha) (trans (sym (D.canonical (D.integer b))) hb)))
  formula-clears z a b (suc n) ha hb with R.evenℤ (a + b) in eq
  ... | false = w , subst (λ k → (D.gamma ^ k) * z ≡ D.embed w) double h
    where
    w = (TC.i {R.ZComplex} ^ suc n) * R.Cplx a b
    h = clears-common z (R.Cplx a b) (suc n) (common-value z a b (suc n) ha hb)
    double : suc n + suc n ≡ 2 * suc n
    double = cong (λ k → suc n + k) (sym (NP.+-identityʳ (suc n)))
  ... | true = GD.divideGamma w , cancel-cleared z w (GD.divideGamma w) (2 * suc n ∸ 1)
      (subst (λ k → (D.gamma ^ k) * z ≡ D.embed w) split h)
      (GD.divide-complete w (G.even-mul (TC.i ^ suc n) (R.Cplx a b) (even-divisible (R.Cplx a b) eq)))
    where
    w = (TC.i {R.ZComplex} ^ suc n) * R.Cplx a b
    h = clears-common z (R.Cplx a b) (suc n) (common-value z a b (suc n) ha hb)
    split : suc n + suc n ≡ suc (2 * suc n ∸ 1)
    split = cong (λ k → suc n + k) (sym (NP.+-identityʳ (suc n)))

denominator-clears : ∀ z → Clears z (R.denomexpBy R.OnePlusIBase z)
denominator-clears (R.Cplx x y) with R.align-dyadic x y | align-correct x y
... | a , b , k | ha , hb = formula-clears (R.Cplx x y) a b k ha hb

clears-upscale : (z : R.DComplex) (n m : ℕ) → n ≤ m → Clears z n → Clears z m
clears-upscale z n m le (w , h) = G.powγ d * w ,
  trans {j = (D.gamma ^ (d + n)) * z}
    (cong (λ k → (D.gamma ^ k) * z) (sym (NP.m∸n+n≡m le)))
    (trans {j = (D.gamma ^ d) * ((D.gamma ^ n) * z)} (sym (D.Powers.action-compose D.gamma d n z))
      (trans {j = (D.gamma ^ d) * D.embed w}
        (cong ((D.gamma ^ d) *_) {x = (D.gamma ^ n) * z} {y = D.embed w} h)
        (trans {j = D.embed (G.powγ d) * D.embed w}
          (cong (_* D.embed w) {x = D.gamma ^ d} {y = D.embed (G.powγ d)} (sym (D.embed-power d)))
          (sym (D.embed-* (G.powγ d) w)))))
  where d = m ∸ n

private
  factor-whole : (z : R.DComplex) (k : ℕ) → Clears z k →
    D.embed (R.to-whole {R.DComplex} {R.ZComplex} (z * (D.gamma ^ k))) ≡ z * (D.gamma ^ k)
  factor-whole z k (w , h) = trans {j = D.embed w}
    (cong D.embed {x = R.to-whole {R.DComplex} {R.ZComplex} (z * (D.gamma ^ k))} {y = w}
      (trans {j = R.to-whole {R.DComplex} {R.ZComplex} (D.embed w)}
        (cong (R.to-whole {R.DComplex} {R.ZComplex}) {x = z * (D.gamma ^ k)} {y = D.embed w} factored)
        (D.whole-embed w))) (sym factored)
    where
    factored : z * (D.gamma ^ k) ≡ D.embed w
    factored = trans {j = (D.gamma ^ k) * z} (D.*-comm z (D.gamma ^ k)) h

abstract
  denominator-factor-whole-at : (z : R.DComplex) (k : ℕ) → R.denomexpBy R.OnePlusIBase z ≤ k →
    D.embed (R.to-whole {R.DComplex} {R.ZComplex} (R.denomexp-factorBy R.OnePlusIBase z k)) ≡
      R.denomexp-factorBy R.OnePlusIBase z k
  denominator-factor-whole-at z k le = factor-whole z k
    (clears-upscale z (R.denomexpBy R.OnePlusIBase z) k le (denominator-clears z))

  -- The executable to-whole operation is exact at the computed exponent.
  denominator-factor-whole : ∀ (z : R.DComplex) →
    let k = R.denomexpBy R.OnePlusIBase z
        f = R.denomexp-factorBy R.OnePlusIBase z k
    in D.embed (R.to-whole {R.DComplex} {R.ZComplex} f) ≡ f
  denominator-factor-whole z = denominator-factor-whole-at z (R.denomexpBy R.OnePlusIBase z) NP.≤-refl

  -- No reconstruction test or supplied denominator witness is needed.
  denominator-reconstruct : ∀ (z : R.DComplex) →
    let k = R.denomexpBy R.OnePlusIBase z
        f = R.denomexp-factorBy R.OnePlusIBase z k
    in (D.inverseGamma ^ k) * D.embed (R.to-whole {R.DComplex} {R.ZComplex} f) ≡ z
  denominator-reconstruct z = D.restore-cleared k z (R.to-whole {R.DComplex} {R.ZComplex} f)
    (trans {j = f} (D.*-comm (D.gamma ^ k) z) (sym (denominator-factor-whole z)))
    where
    k : ℕ
    k = R.denomexpBy R.OnePlusIBase z
    f : R.DComplex
    f = R.denomexp-factorBy R.OnePlusIBase z k
