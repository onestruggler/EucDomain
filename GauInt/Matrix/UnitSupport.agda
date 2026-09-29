{-# OPTIONS --safe --without-K #-}

-- A Gaussian row of squared norm one has exactly one unit entry.
module GauInt.Matrix.UnitSupport where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra hiding (lift)
open import GauInt.Matrix
open import Integer.Sum using (intSum-cong; term-le-sum; intSum)
open import Integer.Squares using (square-nonnegative; entry; entryCode)
open import GauInt.NormParity using (norm-product-real)
open import Finite.Check
open import Data.Nat using (zero; suc; z≤n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (+_; +≤+)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

norm-nonnegative : ∀ (z : ZComplex) → (+ 0) Z.≤ TC.norm z
norm-nonnegative z = ZP.+-mono-≤ (square-nonnegative (re z)) (square-nonnegative (im z))

small-choice : ∀ z → TC.norm z Z.≤ (+ 1) → (z ≡ 0#) ⊎ Unit z
small-choice z h = finish (entryCode (re z) real-small) (entryCode (im z) imag-small)
  where
  real-small : re z Z.* re z Z.≤ (+ 1)
  real-small = ZP.≤-trans
    (subst (λ x → x Z.≤ TC.norm z) (ZP.+-identityʳ (re z Z.* re z))
      (ZP.+-monoʳ-≤ (re z Z.* re z) (square-nonnegative (im z)))) h
  imag-small : im z Z.* im z Z.≤ (+ 1)
  imag-small = ZP.≤-trans
    (subst (λ x → x Z.≤ TC.norm z) (ZP.+-identityˡ (im z Z.* im z))
      (ZP.+-monoˡ-≤ (im z Z.* im z) (square-nonnegative (re z)))) h
  finite : ∀ a b → TC.norm (Cplx (entry a) (entry b)) Z.≤ (+ 1) →
    (Cplx (entry a) (entry b) ≡ 0#) ⊎ Unit (Cplx (entry a) (entry b))
  finite = checkFin 3 _ (λ a → decAll 3 _ (λ b → decImplies
    (TC.norm (Cplx (entry a) (entry b)) ZP.≤? (+ 1))
    ((Cplx (entry a) (entry b) TC.≟ 0#) ⊎-dec
      ((Cplx (entry a) (entry b) * TC.adj (Cplx (entry a) (entry b))) TC.≟ 1#)))) tt
  finish : (Σ[ a ∈ Fin 3 ] entry a ≡ re z) → (Σ[ b ∈ Fin 3 ] entry b ≡ im z) → (z ≡ 0#) ⊎ Unit z
  finish (a , ha) (b , hb) = subst (λ w → (w ≡ 0#) ⊎ Unit w) eq
    (finite a b (subst (λ w → TC.norm w Z.≤ (+ 1)) (sym eq) h))
    where eq = cong₂ Cplx ha hb

unit-norm : ∀ z → Unit z → TC.norm z ≡ (+ 1)
unit-norm z h = trans (sym (norm-product-real z)) (cong re h)

norm-zero : ∀ (z : ZComplex) → TC.norm z ≡ (+ 0) → z ≡ 0#
norm-zero z hz = finish (small-choice z (subst (Z._≤ (+ 1)) (sym hz) (+≤+ z≤n)))
  where
  bad : (+ 1) ≡ (+ 0) → ⊥
  bad ()
  finish : (z ≡ 0#) ⊎ Unit z → z ≡ 0#
  finish (inj₁ h) = h
  finish (inj₂ h) = ⊥-elim (bad (trans (sym (unit-norm z h)) hz))

zero-sum-entry : ∀ {n} (v : Fin n → ZComplex) → intSum (λ i → TC.norm (v i)) ≡ (+ 0) → ∀ i → v i ≡ 0#
zero-sum-entry v h i = norm-zero (v i) (ZP.≤-antisym
  (subst (TC.norm (v i) Z.≤_) h (term-le-sum (λ i → TC.norm (v i)) (λ i → norm-nonnegative (v i)) i))
  (norm-nonnegative (v i)))

Support : ∀ {n} → (Fin n → ZComplex) → Set
Support {n} v = Σ[ i ∈ Fin n ] Unit (v i) × (∀ j → j ≢ i → v j ≡ 0#)

cancel-one : ∀ t → (+ 1) Z.+ t ≡ (+ 1) → t ≡ (+ 0)
cancel-one t h = trans (sym (ZP.+-identityˡ t))
  (trans (cong (Z._+ t) (sym (ZP.+-inverseˡ (+ 1))))
    (trans (ZP.+-assoc (Z.- (+ 1)) (+ 1) t)
      (trans (cong (λ x → (Z.- (+ 1)) Z.+ x) h) (ZP.+-inverseˡ (+ 1)))))

unit-row : ∀ {n} (v : Fin n → ZComplex) → intSum (λ i → TC.norm (v i)) ≡ (+ 1) → Support v
unit-row {zero} v ()
unit-row {suc n} v h with small-choice (v zero)
  (subst (TC.norm (v zero) Z.≤_) h (term-le-sum (λ i → TC.norm (v i)) (λ i → norm-nonnegative (v i)) zero))
... | inj₁ hz = lift (unit-row (λ i → v (suc i)) tail-one)
  where
  tail = intSum (λ i → TC.norm (v (suc i)))
  tail-one : tail ≡ (+ 1)
  tail-one = trans (sym (ZP.+-identityˡ tail)) (trans (cong (Z._+ tail) (sym (cong TC.norm hz))) h)
  lift : Support (λ i → v (suc i)) → Support v
  lift (i , hu , hs) = suc i , hu , λ
    { zero neq → hz
    ; (suc j) neq → hs j (λ eq → neq (cong suc eq)) }
... | inj₂ hu = zero , hu , zeros
  where
  tail = intSum (λ i → TC.norm (v (suc i)))
  tail-zero : tail ≡ (+ 0)
  tail-zero = cancel-one tail (trans (cong (Z._+ tail) (sym (unit-norm (v zero) hu))) h)
  zeros : ∀ j → j ≢ zero → v j ≡ 0#
  zeros zero neq = ⊥-elim (neq refl)
  zeros (suc j) neq = zero-sum-entry (λ i → v (suc i)) tail-zero j

real-sum : ∀ {n} (f : Fin n → ZComplex) → re (sum f) ≡ intSum (λ i → re (f i))
real-sum {zero} f = refl
real-sum {suc n} f = cong (λ x → re (f zero) Z.+ x) (real-sum (λ i → f (suc i)))

row-norm : ∀ {n} (M : Mat n) i → gram M i i ≡ 1# → intSum (λ j → TC.norm (M i j)) ≡ (+ 1)
row-norm M i h = trans (sym (trans (real-sum (λ j → M i j * TC.adj (M i j)))
  (intSum-cong (λ j → re (M i j * TC.adj (M i j))) (λ j → TC.norm (M i j)) (λ j → norm-product-real (M i j))))) (cong re h)
