{-# OPTIONS --safe --without-K #-}

-- Denominator witnesses about actual dyadic matrices, without ScaledMatrix.
module Quantum.Synthesis.Ring.Properties.Gaussian.Matrix.Clearing where

import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Matrix as E
import Quantum.Synthesis.Ring.Properties.DyadicComplex as D
import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma as G
import Quantum.Synthesis.Ring.Properties.Gaussian.Matrix.Euc as V
open import Instances as TC using (_*_; _^_)
open import Data.Nat.Base as N using (ℕ; zero; suc; _+_; _≤_)
import Data.Nat.Properties as NP
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Bool.Base using (T; true; false)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

private
  max-left : ∀ a b → a ≤ TC.max a b
  max-left a b with a N.≤ᵇ b in eq
  ... | true = NP.≤ᵇ⇒≤ a b (subst T (sym eq) tt)
  ... | false = NP.≤-refl

  max-right : ∀ a b → b ≤ TC.max a b
  max-right a b with a N.≤ᵇ b in eq
  ... | true = NP.≤-refl
  ... | false = NP.≰⇒≥ (λ h → subst T eq (NP.≤⇒≤ᵇ h))

  vector-bound : ∀ {C : Set} {Base : Set} {{d : R.DenomExp Base C}} {n}
    (xs : Vec C n) i → R.denomexpBy Base (lookup xs i) ≤ R.denomexpBy Base xs
  vector-bound {Base = Base} (x ∷ xs) zero = max-left (R.denomexpBy Base x) (R.denomexpBy Base xs)
  vector-bound {Base = Base} (x ∷ xs) (suc i) = NP.≤-trans (vector-bound {Base = Base} xs i)
    (max-right (R.denomexpBy Base x) (R.denomexpBy Base xs))

bitBound : ∀ {m n} → E.Matrix m n R.DComplex → ℕ
bitBound = R.denomexpBy R.TwoBase

entry-bound : ∀ {m n} (A : E.Matrix m n R.DComplex) i j →
  R.denomexpBy R.TwoBase (V.view A i j) ≤ bitBound A
entry-bound (E.Matrix' columns) i j = NP.≤-trans
  (vector-bound {Base = R.TwoBase} (lookup columns j) i)
  (vector-bound {Base = R.TwoBase} columns j)

embed : ∀ {m n} → E.Matrix m n R.ZComplex → E.Matrix m n R.DComplex
embed = E.matrix-map D.embed

scale : ∀ {m n} → ℕ → E.Matrix m n R.DComplex → E.Matrix m n R.DComplex
scale k A = (D.gamma ^ k) E.scalarmult A

record Witness {m n} (A : E.Matrix m n R.DComplex) : Set where
  constructor witness
  field
    exponent : ℕ
    numerator : E.Matrix m n R.ZComplex
    clears : scale exponent A ≡ embed numerator
open Witness public

reconstruct : ∀ {m n} → ℕ → E.Matrix m n R.ZComplex → E.Matrix m n R.DComplex
reconstruct k N = (D.inverseGamma ^ k) E.scalarmult (embed N)

given : ∀ {m n} k (N : E.Matrix m n R.ZComplex) → Witness (reconstruct k N)
given k N = witness {A = reconstruct k N} k N (V.ext {A = scale k (reconstruct k N)} {B = embed N} point)
  where
  point : ∀ i j → V.view (scale k (reconstruct k N)) i j ≡ V.view (embed N) i j
  point i j = trans {j = (D.gamma ^ k) * ((D.inverseGamma ^ k) * V.view (embed N) i j)}
    (trans (V.map-view ((D.gamma ^ k) *_) (reconstruct k N) i j)
      (cong ((D.gamma ^ k) *_) {x = V.view (reconstruct k N) i j}
        {y = (D.inverseGamma ^ k) * V.view (embed N) i j}
        (V.map-view ((D.inverseGamma ^ k) *_) (embed N) i j)))
    (D.clear-restored k (V.view (embed N) i j))

reconstruct-witness : ∀ {m n} {A : E.Matrix m n R.DComplex} (w : Witness A) →
  reconstruct (exponent w) (numerator w) ≡ A
reconstruct-witness {A = A} w = V.ext {A = reconstruct (exponent w) (numerator w)} {B = A} point
  where
  k = exponent w
  N = numerator w

  entry-clears : ∀ i j → (D.gamma ^ k) * V.view A i j ≡ D.embed (V.view N i j)
  entry-clears i j = trans (sym (V.map-view ((D.gamma ^ k) *_) A i j))
    (trans (cong (λ M → V.view M i j) (clears w)) (V.map-view D.embed N i j))

  point : ∀ i j → V.view (reconstruct k N) i j ≡ V.view A i j
  point i j = trans {j = (D.inverseGamma ^ k) * D.embed (V.view N i j)}
    (trans (V.map-view ((D.inverseGamma ^ k) *_) (embed N) i j)
      (cong ((D.inverseGamma ^ k) *_) {x = V.view (embed N) i j} {y = D.embed (V.view N i j)}
        (V.map-view D.embed N i j)))
    (D.restore-cleared k (V.view A i j) (V.view N i j) (entry-clears i j))

embed-injective : ∀ {m n} {A B : E.Matrix m n R.ZComplex} → embed A ≡ embed B → A ≡ B
embed-injective {A = A} {B} h = V.ext {A = A} {B = B} (λ i j →
  D.embed-injective {a = V.view A i j} {b = V.view B i j}
    (trans (sym (V.map-view D.embed A i j))
      (trans (cong (λ M → V.view M i j) h) (V.map-view D.embed B i j))))

scale-injective : ∀ {m n} k {A B : E.Matrix m n R.DComplex} → scale k A ≡ scale k B → A ≡ B
scale-injective k {A} {B} h = V.ext {A = A} {B = B} (λ i j →
  D.gamma-cancel k {x = V.view A i j} {y = V.view B i j}
    (trans (sym (V.map-view ((D.gamma ^ k) *_) A i j))
      (trans (cong (λ M → V.view M i j) h) (V.map-view ((D.gamma ^ k) *_) B i j))))

numerator-unique : ∀ {m n} {A : E.Matrix m n R.DComplex} (u v : Witness A) →
  exponent u ≡ exponent v → numerator u ≡ numerator v
numerator-unique {A = A} u v h = embed-injective {A = numerator u} {B = numerator v}
  (trans (sym (clears u)) (trans (cong (λ k → scale k A) h) (clears v)))

scale-compose : ∀ {m n} k l (A : E.Matrix m n R.DComplex) → scale k (scale l A) ≡ scale (k + l) A
scale-compose k l A =
  trans {j = E.matrix-map (λ z → (D.gamma ^ k) * ((D.gamma ^ l) * z)) A}
    (V.map-compose ((D.gamma ^ k) *_) ((D.gamma ^ l) *_) A)
    (V.map-cong (λ z → (D.gamma ^ k) * ((D.gamma ^ l) * z)) ((D.gamma ^ (k + l)) *_)
      (D.Powers.action-compose D.gamma k l) A)

integerScale : ∀ {m n} → ℕ → E.Matrix m n R.ZComplex → E.Matrix m n R.ZComplex
integerScale k N = G.powγ k E.scalarmult N

scale-embed : ∀ {m n} k (N : E.Matrix m n R.ZComplex) → scale k (embed N) ≡ embed (integerScale k N)
scale-embed k N = V.ext {A = scale k (embed N)} {B = embed (integerScale k N)} (λ i j →
  trans {j = (D.gamma ^ k) * D.embed (V.view N i j)}
    (trans (V.map-view ((D.gamma ^ k) *_) (embed N) i j)
      (cong ((D.gamma ^ k) *_) {x = V.view (embed N) i j} {y = D.embed (V.view N i j)} (V.map-view D.embed N i j)))
    (trans {j = D.embed (G.powγ k * V.view N i j)}
      (trans (cong (_* D.embed (V.view N i j)) {x = D.gamma ^ k} {y = D.embed (G.powγ k)} (sym (D.embed-power k)))
        (sym (D.embed-* (G.powγ k) (V.view N i j))))
      (sym (trans (V.map-view D.embed (integerScale k N) i j)
        (cong D.embed (V.map-view (G.powγ k *_) N i j))))))

scaled-numerator : ∀ {m n} {A : E.Matrix m n R.DComplex} (w : Witness A) l →
  embed (integerScale l (numerator w)) ≡ scale (l + exponent w) A
scaled-numerator {A = A} w l = trans (sym (scale-embed l (numerator w)))
  (trans (cong (scale l) {x = embed (numerator w)} {y = scale (exponent w) A} (sym (clears w)))
    (scale-compose l (exponent w) A))

cross-cancel : ∀ {m n} {A B : E.Matrix m n R.DComplex} (u : Witness A) (v : Witness B) →
  integerScale (exponent v) (numerator u) ≡ integerScale (exponent u) (numerator v) → A ≡ B
cross-cancel {A = A} {B} u v h = scale-injective (exponent v + exponent u) {A = A} {B = B}
  (trans (sym (scaled-numerator u (exponent v)))
    (trans (cong embed h)
      (trans (scaled-numerator v (exponent u))
        (cong (λ k → scale k B) (NP.+-comm (exponent u) (exponent v))))))

cross-equal : ∀ {m n} {A B : E.Matrix m n R.DComplex} (u : Witness A) (v : Witness B) → A ≡ B →
  integerScale (exponent v) (numerator u) ≡ integerScale (exponent u) (numerator v)
cross-equal {A = A} {B} u v h = embed-injective
  {A = integerScale (exponent v) (numerator u)} {B = integerScale (exponent u) (numerator v)}
  (trans (scaled-numerator u (exponent v))
    (trans (cong (scale (exponent v + exponent u)) {x = A} {y = B} h)
      (trans (cong (λ k → scale k B) (NP.+-comm (exponent v) (exponent u)))
        (sym (scaled-numerator v (exponent u))))))

coarse : ∀ {m n} (A : E.Matrix m n R.DComplex) → Witness A
coarse A = witness (k + k) (E.matrix-map (λ z → D.coarseNumerator z k) A) (V.ext point)
  where
  k = bitBound A

  scalar : ∀ i j → (D.gamma ^ (k + k)) * V.view A i j ≡ D.embed (D.coarseNumerator (V.view A i j) k)
  scalar i j = D.coarse-clears (V.view A i j) k
    (NP.≤-trans (max-left (R.Dyadic.exponent (R._[i].re (V.view A i j)))
      (R.Dyadic.exponent (R._[i].im (V.view A i j)))) (entry-bound A i j))
    (NP.≤-trans (max-right (R.Dyadic.exponent (R._[i].re (V.view A i j)))
      (R.Dyadic.exponent (R._[i].im (V.view A i j)))) (entry-bound A i j))

  point : ∀ i j → V.view (scale (k + k) A) i j ≡
    V.view (embed (E.matrix-map (λ z → D.coarseNumerator z k) A)) i j
  point i j = trans (V.map-view ((D.gamma ^ (k + k)) *_) A i j)
    (trans (scalar i j)
      (sym (trans (V.map-view D.embed (E.matrix-map (λ z → D.coarseNumerator z k) A) i j)
        (cong D.embed (V.map-view (λ z → D.coarseNumerator z k) A i j)))))
