{-# OPTIONS --safe --without-K #-}

-- Correctness of the operational 1+i denominator on dyadic Gaussian scalars.
module Quantum.Synthesis.Ring.Properties.GammaDenominator where

import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Ring.Properties.Dyadic as DP
import Quantum.Synthesis.Ring.Properties.DyadicComplex as D
import GauInt.Gamma as G
import GauInt.Gamma.Division as GD
import GauInt.Parity as GP
import GauInt.Algebra as ZG
import Typeclasses.Properties as Power
open import Algebra.Bundles using (CommutativeRing)
open import Instances as TC using (_+_; _*_; _^_; 1#)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Data.Integer.Base using (ℤ; +_)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Bool.Base using (true; false; T; if_then_else_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
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

private
  module ZPowers = Power.Powers {A = R.ZComplex} {{R.SemiRingCplx}}
    (CommutativeRing.*-isCommutativeMonoid ZG.gaussianRing)

  even-double : ∀ a → R.evenℤ (a Z.* (+ 2)) ≡ true
  even-double a = trans (cong R.evenℕ (ZP.abs-* a (+ 2)))
    (cong (λ n → n Data.Nat.≡ᵇ 0) (ND.m*n%n≡0 Z.∣ a ∣ 2))

  double-coordinates : ∀ a b → R.Cplx a b * G.powγ 2 ≡ R.Cplx ((Z.- b) Z.* (+ 2)) (a Z.* (+ 2))
  double-coordinates a b = cong₂ R.Cplx
    (solve 2 (λ a b → a :* con (+ 0) :- b :* con (+ 2) := (:- b) :* con (+ 2)) refl a b)
    (solve 2 (λ a b → a :* con (+ 2) :+ b :* con (+ 0) := a :* con (+ 2)) refl a b)
    where open +-*-Solver

  double-even : ∀ w q → w ≡ q * G.powγ 2 →
    R.evenℤ (R._[i].re w) ≡ true × R.evenℤ (R._[i].im w) ≡ true
  double-even w (R.Cplx a b) h =
    trans (cong (λ z → R.evenℤ (R._[i].re z)) eq) (even-double (Z.- b)) ,
    trans (cong (λ z → R.evenℤ (R._[i].im z)) eq) (even-double a)
    where eq = trans h (double-coordinates a b)

  canonical-odd : ∀ a n → .(T (R.Canonical a (suc n))) → R.evenℤ a ≡ true → ⊥
  canonical-odd a n ca h with R.evenℤ a
  ... | true = ⊥-elim-irr ca
  ... | false with h
  ...   | ()

  NoDouble : R.ZComplex → Set
  NoDouble w = ∀ q → w ≡ q * G.powγ 2 → ⊥

  PrimitivePair : ℤ × ℤ × ℕ → Set
  PrimitivePair (a , b , zero) = ⊤
  PrimitivePair (a , b , suc n) = NoDouble (R.Cplx a b)

  primitive-left : ∀ a b n → .(T (R.Canonical a n)) → PrimitivePair (a , b , n)
  primitive-left a b zero ca = tt
  primitive-left a b (suc n) ca q h = canonical-odd a n ca (proj₁ (double-even (R.Cplx a b) q h))

  primitive-right : ∀ a b n → .(T (R.Canonical b n)) → PrimitivePair (a , b , n)
  primitive-right a b zero cb = tt
  primitive-right a b (suc n) cb q h = canonical-odd b n cb (proj₂ (double-even (R.Cplx a b) q h))

align-primitive : ∀ x y → PrimitivePair (R.align-dyadic x y)
align-primitive (R.Dyadic' a n ca) (R.Dyadic' b m cb) with n ≤ᵇ m
... | true = primitive-right (R.shiftL a (m ∸ n)) b m cb
... | false = primitive-left a (R.shiftL b (n ∸ m)) n ca

private
  unit-i-power : ∀ k → ZG.Unit ((TC.i {R.ZComplex}) ^ k)
  unit-i-power zero = refl
  unit-i-power (suc k) = subst ZG.Unit (sym (ZPowers.^-suc TC.i k))
    (ZG.unit-product TC.i (TC.i ^ k) refl (unit-i-power k))

  no-double-unit : ∀ u w → ZG.Unit u → NoDouble w → NoDouble (u * w)
  no-double-unit u w hu nondiv q h = nondiv (TC.adj u * q)
    (trans (sym (ZG.unit-unscale u w hu))
      (trans (cong (TC.adj u *_) h) (sym (ZG.*-assoc (TC.adj u) q (G.powγ 2)))))

  false-not-true : false ≡ true → ⊥
  false-not-true ()

  false-not-even : ∀ w → R.evenℤ (R._[i].re w + R._[i].im w) ≡ false → ¬ G.Evenγ w
  false-not-even w h even = false-not-true (trans (sym h)
    (cong (λ n → n Data.Nat.≡ᵇ 0) (GP.even-parity-zero w even)))

  -- Compare two clearings after multiplying the lower one by gamma^t.
  smaller-factor : (z : R.DComplex) (n t : ℕ) (w : R.ZComplex) →
    (D.gamma ^ (t + n)) * z ≡ D.embed w → Clears z n →
    Σ[ q ∈ R.ZComplex ] w ≡ q * G.powγ t
  smaller-factor z n t w high (q , low) = q , trans
    (D.embed-injective {a = w} {b = G.powγ t * q} eq) (ZG.*-comm (G.powγ t) q)
    where
    eq : D.embed w ≡ D.embed (G.powγ t * q)
    eq = trans {j = (D.gamma ^ (t + n)) * z} (sym high)
      (trans {j = (D.gamma ^ t) * ((D.gamma ^ n) * z)} (sym (D.Powers.action-compose D.gamma t n z))
        (trans {j = (D.gamma ^ t) * D.embed q}
          (cong ((D.gamma ^ t) *_) {x = (D.gamma ^ n) * z} {y = D.embed q} low)
          (trans {j = D.embed (G.powγ t) * D.embed q}
            (cong (_* D.embed q) {x = D.gamma ^ t} {y = D.embed (G.powγ t)} (sym (D.embed-power t)))
            (sym (D.embed-* (G.powγ t) q)))))

  bound-not-even : (z : R.DComplex) (n : ℕ) (w : R.ZComplex) →
    (D.gamma ^ suc n) * z ≡ D.embed w → ¬ G.Evenγ w →
    ∀ m → Clears z m → suc n ≤ m
  bound-not-even z n w high odd m low with suc n NP.≤? m
  ... | yes le = le
  ... | no lt = ⊥-elim (odd (smaller-factor z n 1 w high
    (clears-upscale z m n (NP.≤-pred (NP.≰⇒> lt)) low)))

  bound-no-double : (z : R.DComplex) (n : ℕ) (w : R.ZComplex) →
    (D.gamma ^ suc (suc n)) * z ≡ D.embed w → NoDouble w →
    ∀ m → Clears z m → suc n ≤ m
  bound-no-double z n w high nondiv m low with suc n NP.≤? m
  ... | yes le = le
  ... | no lt = ⊥-elim (contradiction (smaller-factor z n 2 w high
    (clears-upscale z m n (NP.≤-pred (NP.≰⇒> lt)) low)))
    where
    contradiction : (Σ[ q ∈ R.ZComplex ] w ≡ q * G.powγ 2) → ⊥
    contradiction (q , h) = nondiv q h

  formula-minimal : (z : R.DComplex) (a b : ℤ) (k : ℕ) →
    R.dyadic a k ≡ R._[i].re z → R.dyadic b k ≡ R._[i].im z →
    PrimitivePair (a , b , k) → ∀ m → Clears z m → formula a b k ≤ m
  formula-minimal z a b zero ha hb nondiv m low with R.evenℤ (a + b)
  ... | true = z≤n
  ... | false = z≤n
  formula-minimal z a b (suc n) ha hb nondiv m low with R.evenℤ (a + b) in eq
  ... | false = subst (_≤ m) double (bound-not-even z (n + suc n) w high odd m low)
    where
    u : R.ZComplex
    u = TC.i ^ suc n
    w : R.ZComplex
    w = u * R.Cplx a b
    high : (D.gamma ^ (suc n + suc n)) * z ≡ D.embed w
    high = clears-common z (R.Cplx a b) (suc n) (common-value z a b (suc n) ha hb)
    odd : ¬ G.Evenγ w
    odd even = false-not-even (R.Cplx a b) eq (G.even-unscale u (R.Cplx a b) (unit-i-power (suc n)) even)
    double : suc n + suc n ≡ 2 * suc n
    double = cong (λ k → suc n + k) (sym (NP.+-identityʳ (suc n)))
  ... | true = subst (_≤ m) (sym oneLess) (bound-no-double z (n + n) w high
      (no-double-unit u (R.Cplx a b) (unit-i-power (suc n)) nondiv) m low)
    where
    u : R.ZComplex
    u = TC.i ^ suc n
    w : R.ZComplex
    w = u * R.Cplx a b
    high : (D.gamma ^ suc (suc (n + n))) * z ≡ D.embed w
    high = subst (λ k → (D.gamma ^ k) * z ≡ D.embed w) (cong suc (NP.+-suc n n))
      (clears-common z (R.Cplx a b) (suc n) (common-value z a b (suc n) ha hb))
    oneLess : 2 * suc n ∸ 1 ≡ suc (n + n)
    oneLess = trans (cong (n Data.Nat.+_) (NP.+-identityʳ (suc n))) (NP.+-suc n n)

-- The operational exponent is least among every possible integer clearing.
denominator-minimal : (z : R.DComplex) (m : ℕ) → Clears z m → R.denomexpBy R.OnePlusIBase z ≤ m
denominator-minimal (R.Cplx x y) m low with R.align-dyadic x y | align-correct x y | align-primitive x y
... | a , b , k | ha , hb | nondiv = formula-minimal (R.Cplx x y) a b k ha hb nondiv m low
