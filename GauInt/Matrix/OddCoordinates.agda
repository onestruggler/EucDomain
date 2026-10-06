{-# OPTIONS --safe --without-K #-}

-- Direct congruences for odd Gaussian entries; no alignment search is assumed.
module GauInt.Matrix.OddCoordinates where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Matrix
open import GauInt.Gamma using () renaming (gaussianParity to parity)
open import GauInt.Parity using (parity-integer)
open import GauInt.Matrix.ResidueArithmetic using (coordinates; coordinates-sum)
open import Integer.Sum using (intSum)
open import Integer.Congruence
import Integer.Sum as S
import Integer.Parity as IP
open import Data.Integer using (ℤ; +_; _/ℕ_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

halfCoordinate : ZComplex → ℤ
halfCoordinate z = coordinates z /ℕ 2

odd-coordinate : ∀ z → parity z ≡ 1 → coordinates z ≡ + 1 Z.+ (+ 2) Z.* halfCoordinate z
odd-coordinate z h = trans (IP.parity-decomposition (coordinates z))
  (cong (λ n → + n Z.+ (+ 2) Z.* halfCoordinate z) (trans (sym (parity-integer z)) h))

oddForm : ℤ → ℤ → ZComplex
oddForm p a = Cplx ((+ 1) Z.+ (+ 2) Z.* p Z.- a) a

odd-form : ∀ z → parity z ≡ 1 → z ≡ oddForm (halfCoordinate z) (im z)
odd-form (Cplx a b) h = cong₂ Cplx
  (trans (solve 2 (λ a b → a := (a :+ b) :- b) refl a b)
    (cong (λ x → x Z.- b) (odd-coordinate (Cplx a b) h))) refl

form-imag : ∀ p q a b → Cong (+ 2) (im (oddForm p a * TC.adj (oddForm q b))) (a Z.- b)
form-imag p q a b = a Z.* q Z.- p Z.* b , solve 4 (λ p q a b →
  (con (+ 1) :+ con (+ 2) :* p :- a) :* (:- b) :+ a :* (con (+ 1) :+ con (+ 2) :* q :- b)
  := (a :- b) :+ con (+ 2) :* (a :* q :- p :* b)) refl p q a b

form-coordinate : ∀ p q a b → Cong (+ 4) (coordinates (oddForm p a * TC.adj (oddForm q b)))
  (+ 1 Z.+ (+ 2) Z.* (p Z.+ q Z.- b Z.+ a Z.* b))
form-coordinate p q a b = p Z.* q Z.- p Z.* b , solve 4 (λ p q a b →
  ((con (+ 1) :+ con (+ 2) :* p :- a) :* (con (+ 1) :+ con (+ 2) :* q :- b) :- a :* (:- b)) :+
  ((con (+ 1) :+ con (+ 2) :* p :- a) :* (:- b) :+ a :* (con (+ 1) :+ con (+ 2) :* q :- b)) :=
  (con (+ 1) :+ con (+ 2) :* (p :+ q :- b :+ a :* b)) :+ con (+ 4) :* (p :* q :- p :* b)) refl p q a b

odd-imag : ∀ z w → parity z ≡ 1 → parity w ≡ 1 → Cong (+ 2) (im (z * TC.adj w)) (im z Z.- im w)
odd-imag z w hz hw = subst (λ x → Cong (+ 2) (im x) (im z Z.- im w))
  (cong₂ _*_ (sym (odd-form z hz)) (cong TC.adj (sym (odd-form w hw))))
  (form-imag (halfCoordinate z) (halfCoordinate w) (im z) (im w))

odd-coordinate-product : ∀ z w → parity z ≡ 1 → parity w ≡ 1 → Cong (+ 4) (coordinates (z * TC.adj w))
  (+ 1 Z.+ (+ 2) Z.* (halfCoordinate z Z.+ halfCoordinate w Z.- im w Z.+ im z Z.* im w))
odd-coordinate-product z w hz hw = subst (λ x → Cong (+ 4) (coordinates x)
  (+ 1 Z.+ (+ 2) Z.* (halfCoordinate z Z.+ halfCoordinate w Z.- im w Z.+ im z Z.* im w)))
  (cong₂ _*_ (sym (odd-form z hz)) (cong TC.adj (sym (odd-form w hw))))
  (form-coordinate (halfCoordinate z) (halfCoordinate w) (im z) (im w))

imag-sum : ∀ {n} (f : Fin n → ZComplex) → im (sum f) ≡ intSum (λ i → im (f i))
imag-sum {zero} f = refl
imag-sum {suc n} f = cong (λ x → im (f zero) Z.+ x) (imag-sum (λ i → f (suc i)))

sum-affine-four : ∀ (f : Fin 4 → ℤ) → intSum (λ i → + 1 Z.+ (+ 2) Z.* f i) ≡ + 4 Z.+ (+ 2) Z.* intSum f
sum-affine-four f = trans (S.sum-add (λ _ → + 1) (λ i → (+ 2) Z.* f i))
  (cong (λ x → + 4 Z.+ x) (S.sum-scale (+ 2) f))

half-zero : ∀ x → Cong (+ 4) (+ 0) (+ 4 Z.+ (+ 2) Z.* x) → Cong (+ 2) x (+ 0)
half-zero x (q , h) = Z.- (+ 1) Z.- q , ZP.*-cancelˡ-≡ (+ 2) x (+ 0 Z.+ (+ 2) Z.* (Z.- (+ 1) Z.- q))
  (trans (solve 2 (λ x q → con (+ 2) :* x :=
    ((con (+ 4) :+ con (+ 2) :* x) :+ con (+ 4) :* q) :+ con (+ 2) :*
      (con (+ 0) :+ con (+ 2) :* ((:- con (+ 1)) :- q))) refl x q)
    (trans (cong (λ t → t Z.+ (+ 2) Z.* (+ 0 Z.+ (+ 2) Z.* (Z.- (+ 1) Z.- q))) (sym h))
      (ZP.+-identityˡ ((+ 2) Z.* (+ 0 Z.+ (+ 2) Z.* (Z.- (+ 1) Z.- q))))))

rowIm : ∀ {n} → Mat n → Fin n → ℤ
rowIm M i = intSum (λ k → im (M i k))

rowHalf : ∀ {n} → Mat n → Fin n → ℤ
rowHalf M i = intSum (λ k → halfCoordinate (M i k))

imagDot : ∀ {n} → Mat n → Fin n → Fin n → ℤ
imagDot M i j = intSum (λ k → im (M i k) Z.* im (M j k))

odd-row-imag : ∀ {n} (M : Mat n) → (∀ i j → parity (M i j) ≡ 1) → ∀ i j → gram M i j ≡ 0# →
  Cong (+ 2) (+ 0) (rowIm M i Z.- rowIm M j)
odd-row-imag M h i j hg = subst (λ x → Cong (+ 2) x (rowIm M i Z.- rowIm M j)) (cong im hg)
  (subst (λ x → Cong (+ 2) x (rowIm M i Z.- rowIm M j)) (sym (imag-sum (λ k → M i k * TC.adj (M j k))))
    (subst (Cong (+ 2) (intSum (λ k → im (M i k * TC.adj (M j k)))))
      (S.sum-sub (λ k → im (M i k)) (λ k → im (M j k)))
      (cong-sum (+ 2) (λ k → im (M i k * TC.adj (M j k))) (λ k → im (M i k) Z.- im (M j k)) (λ k → odd-imag (M i k) (M j k) (h i k) (h j k)))))

odd-row-coordinate : ∀ (M : Mat 4) → (∀ i j → parity (M i j) ≡ 1) → ∀ i j → gram M i j ≡ 0# →
  Cong (+ 2) (rowHalf M i Z.+ rowHalf M j Z.- rowIm M j Z.+ imagDot M i j) (+ 0)
odd-row-coordinate M h i j hg = subst (λ x → Cong (+ 2) x (+ 0)) separated
  (half-zero (intSum f) (subst (λ x → Cong (+ 4) x (+ 4 Z.+ (+ 2) Z.* intSum f)) (cong coordinates hg)
    (subst (λ x → Cong (+ 4) x (+ 4 Z.+ (+ 2) Z.* intSum f)) (sym (coordinates-sum (λ k → M i k * TC.adj (M j k))))
      (subst (Cong (+ 4) (intSum (λ k → coordinates (M i k * TC.adj (M j k)))) ) (sum-affine-four f)
        (cong-sum (+ 4) (λ k → coordinates (M i k * TC.adj (M j k))) (λ k → + 1 Z.+ (+ 2) Z.* f k) (λ k → odd-coordinate-product (M i k) (M j k) (h i k) (h j k)))))))
  where
  f : Fin 4 → ℤ
  f k = halfCoordinate (M i k) Z.+ halfCoordinate (M j k) Z.- im (M j k) Z.+ im (M i k) Z.* im (M j k)
  separated : intSum f ≡ rowHalf M i Z.+ rowHalf M j Z.- rowIm M j Z.+ imagDot M i j
  separated = trans (S.sum-add (λ k → halfCoordinate (M i k) Z.+ halfCoordinate (M j k) Z.- im (M j k))
    (λ k → im (M i k) Z.* im (M j k)))
    (cong (λ x → x Z.+ imagDot M i j) (trans (S.sum-sub (λ k → halfCoordinate (M i k) Z.+ halfCoordinate (M j k)) (λ k → im (M j k)))
      (cong (λ x → x Z.- rowIm M j) (S.sum-add (λ k → halfCoordinate (M i k)) (λ k → halfCoordinate (M j k))))))
