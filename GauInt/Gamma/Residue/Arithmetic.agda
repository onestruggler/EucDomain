{-# OPTIONS --safe --without-K #-}

-- Small-code computations with exact bridges to Gaussian Gram predicates.
module GauInt.Gamma.Residue.Arithmetic where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (conj-involutive)
open import GauInt.Matrix
open import GauInt.Matrix.Gram using (columnGram)
open import GauInt.Gamma.Residue using (Code; encode; decode; encode-decode; encode-add; encode-mul; encode-conj; encode-congruent; congruent-from-code)
import GauInt.Gamma.Congruence as G
import GauInt.Gamma.Residue.Tables as T
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

encode-add-fast : ∀ a b → encode (a + b) ≡ T.add (encode a) (encode b)
encode-add-fast a b = trans (encode-add a b) (sym (T.add-correct (encode a) (encode b)))

encode-mul-fast : ∀ a b → encode (a * b) ≡ T.multiply (encode a) (encode b)
encode-mul-fast a b = trans (encode-mul a b) (sym (T.multiply-correct (encode a) (encode b)))

encode-star-fast : ∀ a → encode (TC.adj a) ≡ T.star (encode a)
encode-star-fast a = trans (encode-conj a) (sym (T.star-correct (encode a)))

sumCode : ∀ {n} → (Fin n → Code) → Code
sumCode {zero} f = zero
sumCode {suc n} f = T.add (f zero) (sumCode (λ i → f (suc i)))

sumCode-cong : ∀ {n} (f g : Fin n → Code) → (∀ i → f i ≡ g i) → sumCode f ≡ sumCode g
sumCode-cong {zero} f g h = refl
sumCode-cong {suc n} f g h = cong₂ T.add (h zero) (sumCode-cong (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

encode-sum : ∀ {n} (f : Fin n → ZComplex) → encode (sum f) ≡ sumCode (λ i → encode (f i))
encode-sum {zero} f = refl
encode-sum {suc n} f = trans (encode-add-fast (f zero) (sum (λ i → f (suc i))))
  (cong (T.add (encode (f zero))) (encode-sum (λ i → f (suc i))))

innerCode : ∀ {n} → (Fin n → Code) → (Fin n → Code) → Code
innerCode f g = sumCode (λ i → T.multiply (f i) (T.star (g i)))

inner-correct : ∀ {n} (f g : Fin n → Code) →
  encode (sum (λ i → decode (f i) * TC.adj (decode (g i)))) ≡ innerCode f g
inner-correct f g = trans (encode-sum (λ i → decode (f i) * TC.adj (decode (g i))))
  (sumCode-cong _ _ (λ i → trans (encode-mul-fast (decode (f i)) (TC.adj (decode (g i))))
    (cong₂ T.multiply (encode-decode (f i))
      (trans (encode-star-fast (decode (g i))) (cong T.star (encode-decode (g i)))))))

mulCode : ∀ {n} → (Fin n → Fin n → Code) → (Fin n → Fin n → Code) → Fin n → Fin n → Code
mulCode L M i j = sumCode (λ k → T.multiply (L i k) (M k j))

encode-matrix-mul : ∀ {n} (L M : Mat n) i j →
  encode (mul L M i j) ≡ mulCode (λ a b → encode (L a b)) (λ a b → encode (M a b)) i j
encode-matrix-mul L M i j = trans (encode-sum (λ k → L i k * M k j))
  (sumCode-cong _ _ (λ k → encode-mul-fast (L i k) (M k j)))

columnCode : ∀ {n} → (Fin n → Fin n → Code) → Fin n → Fin n → Code
columnCode M i j = sumCode (λ k → T.multiply (T.star (M k i)) (M k j))

encode-columnGram : ∀ {n} (M : Mat n) i j →
  encode (columnGram M i j) ≡ columnCode (λ a b → encode (M a b)) i j
encode-columnGram M i j = trans (encode-sum (λ k → TC.adj (M k i) * TC.adj (TC.adj (M k j))))
  (sumCode-cong _ _ (λ k → trans (cong encode (cong (TC.adj (M k i) *_) (conj-involutive (M k j))))
    (trans (encode-mul-fast (TC.adj (M k i)) (M k j))
      (cong (λ c → T.multiply c (encode (M k j))) (encode-star-fast (M k i))))))

-- Only the small-code decision is evaluated. The Gaussian expressions and
-- their encoding proofs are retained as proof arguments, not recomputed.
reflect-congruence : ∀ a b ca cb → encode a ≡ ca → encode b ≡ cb → Dec (ca ≡ cb) → Dec (G.Cong 3 a b)
reflect-congruence a b ca cb ha hb (yes h) = yes (congruent-from-code a b (trans ha (trans h (sym hb))))
reflect-congruence a b ca cb ha hb (no hn) = no (λ h → hn (trans (sym ha) (trans (encode-congruent a b h) hb)))
