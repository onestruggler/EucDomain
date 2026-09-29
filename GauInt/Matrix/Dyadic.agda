{-# OPTIONS --safe --without-K #-}

-- Actual matrix values over 𝔻[i]. DenomExpMatrix supplies their common
-- 1+i denominator; numerator/exponent presentations are a proof boundary.
module GauInt.Matrix.Dyadic where

import Quantum.Synthesis.Ring as R
import Quantum.Synthesis.Matrix as E
open import Instances as TC using (_*_; _^_)
import GauInt.Matrix.Euc as Z
import Quantum.Synthesis.Ring.Properties.DyadicComplex as Scalar
import GauInt.Gamma as G
import GauInt.Matrix.Clearing as C
import GauInt.Matrix.Normalization as N
import GauInt.Matrix.Normalization.Minimal as NM
open import GauInt.Matrix using (Mat)
open import GauInt.Matrix.Presentation using (ScaledMatrix; scaled; numerator; exponent; Equivalent)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

Matrix : ℕ → Set
Matrix n = E.Matrix n n R.DComplex

-- Input exponents may be nonminimal. Store the value, not that exponent.
fromNumerator : ∀ {n} → Mat n → ℕ → Matrix n
fromNumerator N k = (Scalar.inverseGamma ^ k) E.scalarmult (E.matrix-map R.fromZComplex (Z.pack N))

encode : ∀ {n} → ScaledMatrix n → Matrix n
encode A = fromNumerator (numerator A) (exponent A)

level : ∀ {n} → Matrix n → ℕ
level = R.denomexpBy R.OnePlusIBase

decompose : ∀ {n} → Matrix n → ScaledMatrix n
decompose {n} A = present (R.denomexp-decomposeBy {Matrix n} {Z.Matrix n n} R.OnePlusIBase A)
  where
  present : Z.Matrix n n × ℕ → ScaledMatrix n
  present (N , k) = scaled (Z.view N) k

multiply : ∀ {n} → Matrix n → Matrix n → Matrix n
multiply = E._·*·_

-- DenomExp is an operational class. Do not silently assume a law for it:
-- certify reconstruction at the boundary to the existing integer proofs.
record Decomposition {n} (A : Matrix n) : Set where
  constructor decomposed
  field
    witness : ScaledMatrix n
    reconstructs : encode witness ≡ A
open Decomposition public

fromNumerator-reconstruct : ∀ {n} (N : Mat n) k → fromNumerator N k ≡ C.reconstruct k (Z.pack N)
fromNumerator-reconstruct N k = cong (λ M → (Scalar.inverseGamma ^ k) E.scalarmult M)
  (Z.ext {A = E.matrix-map R.fromZComplex (Z.pack N)} {B = C.embed (Z.pack N)} (λ i j →
    trans (Z.map-view R.fromZComplex (Z.pack N) i j)
      (trans (Scalar.fromZComplex-embed (Z.view (Z.pack N) i j))
        (sym (Z.map-view Scalar.embed (Z.pack N) i j)))))

asWitness : ∀ {n} (A : ScaledMatrix n) → C.Witness (encode A)
asWitness A = C.witness {A = encode A} k N
  (trans (cong (C.scale k) {x = encode A} {y = C.reconstruct k N}
    (fromNumerator-reconstruct (numerator A) k)) (C.clears (C.given k N)))
  where
  k = exponent A
  N = Z.pack (numerator A)

private
  scaled-entry : ∀ {n} k (N : Mat n) i j →
    Z.view (C.integerScale k (Z.pack N)) i j ≡ G.powγ k * N i j
  scaled-entry k N i j = trans (Z.map-view (G.powγ k *_) (Z.pack N) i j)
    (cong (G.powγ k *_) {x = Z.view (Z.pack N) i j} {y = N i j} (Z.view-pack N i j))

equivalent-values : ∀ {n} (A B : ScaledMatrix n) → Equivalent A B → encode A ≡ encode B
equivalent-values A B h = C.cross-cancel {A = encode A} {B = encode B} (asWitness A) (asWitness B)
  (Z.ext {A = C.integerScale (exponent B) (Z.pack (numerator A))}
    {B = C.integerScale (exponent A) (Z.pack (numerator B))} (λ i j →
      trans (scaled-entry (exponent B) (numerator A) i j)
        (trans (h i j) (sym (scaled-entry (exponent A) (numerator B) i j)))))

values-equivalent : ∀ {n} (A B : ScaledMatrix n) → encode A ≡ encode B → Equivalent A B
values-equivalent A B h i j = trans (sym (scaled-entry (exponent B) (numerator A) i j))
  (trans (cong (λ M → Z.view M i j)
    (C.cross-equal {A = encode A} {B = encode B} (asWitness A) (asWitness B) h))
    (scaled-entry (exponent A) (numerator B) i j))

-- Bridge the existing presentation encoding to the proved matrix witnesses.
-- The executable encoding itself is unchanged.
fromWitness : ∀ {n} {A : Matrix n} → C.Witness A → Decomposition A
fromWitness {A = A} w = decomposed (scaled (Z.view N) k)
  (trans encoding (C.reconstruct-witness {A = A} w))
  where
  N = C.numerator w
  k = C.exponent w

  mapped : E.matrix-map R.fromZComplex (Z.pack (Z.view N)) ≡ C.embed N
  mapped = trans (cong (E.matrix-map R.fromZComplex) (Z.pack-view N))
    (Z.ext {A = E.matrix-map R.fromZComplex N} {B = C.embed N} (λ i j →
      trans (Z.map-view R.fromZComplex N i j)
        (trans (Scalar.fromZComplex-embed (Z.view N i j)) (sym (Z.map-view Scalar.embed N i j)))))

  encoding : encode (scaled (Z.view N) k) ≡ C.reconstruct k N
  encoding = cong (λ M → (Scalar.inverseGamma ^ k) E.scalarmult M) mapped

-- Every actual matrix has a proved presentation. This construction does
-- not test whether the operational minimum-exponent extractor succeeded.
totalDecomposition : ∀ {n} (A : Matrix n) → Decomposition A
totalDecomposition A = fromWitness {A = A} (C.coarse A)

normalizeDecomposition : ∀ {n} {A : Matrix n} → Decomposition A → Decomposition A
normalizeDecomposition {A = A} (decomposed P hp) = decomposed {A = A} Q
  (trans {j = encode P} (equivalent-values Q P (N.equivalent (N.normalize P))) hp)
  where Q = N.value (N.normalize P)

canonicalDecomposition : ∀ {n} (A : Matrix n) → Decomposition A
canonicalDecomposition A = normalizeDecomposition {A = A} (totalDecomposition A)

minimumExponent : ∀ {n} → Matrix n → ℕ
minimumExponent A = exponent (witness (canonicalDecomposition A))

canonicalWitness : ∀ {n} (A : Matrix n) → C.Witness A
canonicalWitness A = C.witness {A = A} (exponent P) (Z.pack (numerator P))
  (trans (cong (C.scale (exponent P)) {x = A} {y = encode P} (sym (reconstructs d)))
    (C.clears (asWitness P)))
  where
  d = canonicalDecomposition A
  P = witness d

minimum-realized : ∀ {n} (A : Matrix n) → C.exponent (canonicalWitness A) ≡ minimumExponent A
minimum-realized A = Relation.Binary.PropositionalEquality.refl

private
  normalized-bound : ∀ {n} {A : Matrix n} (d : Decomposition A) (Q : ScaledMatrix n) →
    encode Q ≡ A → exponent (witness (normalizeDecomposition {A = A} d)) ≤ exponent Q
  normalized-bound (decomposed P hp) Q hq = NM.normalize-lower P Q
    (values-equivalent P Q (trans hp (sym hq)))

minimum-encoding-bound : ∀ {n} (A : Matrix n) (P : ScaledMatrix n) →
  encode P ≡ A → minimumExponent A ≤ exponent P
minimum-encoding-bound A P h = normalized-bound {A = A} (totalDecomposition A) P h

minimum-witness-bound : ∀ {n} (A : Matrix n) (w : C.Witness A) → minimumExponent A ≤ C.exponent w
minimum-witness-bound A w = minimum-encoding-bound A (witness (fromWitness {A = A} w))
  (reconstructs (fromWitness {A = A} w))

checkDecomposition : ∀ {n} (A : Matrix n) → Maybe (Decomposition A)
checkDecomposition A = checked (encode (decompose A) TC.≟ A)
  where
  checked : Dec (encode (decompose A) ≡ A) → Maybe (Decomposition A)
  checked (yes h) = just (decomposed (decompose A) h)
  checked (no _) = nothing
