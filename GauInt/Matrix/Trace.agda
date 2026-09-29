{-# OPTIONS --safe --without-K #-}

-- Trace and positivity lemmas for recovering column Gram from row Gram.
module GauInt.Matrix.Trace where
open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.Matrix.Gram
open import Integer.Sum using (intSum-cong; sum-nonnegative; term-le-sum; intSum)
open import GauInt.Matrix.UnitSupport using (real-sum; norm-nonnegative; zero-sum-entry)
open import GauInt.NormParity using (norm-product-real)
open import Data.Integer using (+_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open GaussianSolver

trace : ∀ {n} → Mat n → ZComplex
trace M = sum (λ i → M i i)

trace-cong : ∀ {n} {M N : Mat n} → M ≈ N → trace M ≡ trace N
trace-cong h = sum-cong (λ i → h i i)

trace-mul : ∀ {n} (M N : Mat n) → trace (mul M N) ≡ trace (mul N M)
trace-mul M N = trans (sum-swap (λ i j → M i j * N j i))
  (sum-cong (λ i → sum-cong (λ j → *-comm (M j i) (N i j))))

trace-scale : ∀ {n} a (M : Mat n) → trace (scale a M) ≡ a * trace M
trace-scale a M = sum-mulˡ a (λ i → M i i)

sub : ∀ {n} → Mat n → Mat n → Mat n
sub M N i j = M i j - N i j

trace-sub : ∀ {n} (M N : Mat n) → trace (sub M N) ≡ trace M - trace N
trace-sub M N = sum-sub (λ i → M i i) (λ i → N i i)

mul-subˡ : ∀ {n} (A B C : Mat n) → mul (sub A B) C ≈ sub (mul A C) (mul B C)
mul-subˡ A B C i j = trans
  (sum-cong (λ k → solve 3 (λ a b c → (a :- b) :* c := a :* c :- b :* c) refl (A i k) (B i k) (C k j)))
  (sum-sub (λ k → A i k * C k j) (λ k → B i k * C k j))

mul-subʳ : ∀ {n} (A B C : Mat n) → mul A (sub B C) ≈ sub (mul A B) (mul A C)
mul-subʳ A B C i j = trans
  (sum-cong (λ k → solve 3 (λ a b c → a :* (b :- c) := a :* b :- a :* c) refl (A i k) (B k j) (C k j)))
  (sum-sub (λ k → A i k * B k j) (λ k → A i k * C k j))

mul-sub-both : ∀ {n} (A B C D : Mat n) → mul (sub A B) (sub C D) ≈
  sub (sub (mul A C) (mul B C)) (sub (mul A D) (mul B D))
mul-sub-both A B C D i j = trans (mul-subʳ (sub A B) C D i j)
  (cong₂ _-_ (mul-subˡ A B C i j) (mul-subˡ A B D i j))

adjoint-twice : ∀ {n} (M : Mat n) → adjoint (adjoint M) ≈ M
adjoint-twice M i j = conj-involutive (M i j)

trace-norm : ∀ {n} (M : Mat n) → re (trace (gram M)) ≡ intSum (λ i → intSum (λ j → TC.norm (M i j)))
trace-norm M = trans (real-sum (λ i → gram M i i))
  (intSum-cong (λ i → re (gram M i i)) (λ i → intSum (λ j → TC.norm (M i j)))
    (λ i → trans (real-sum (λ j → M i j * TC.adj (M i j)))
      (intSum-cong (λ j → re (M i j * TC.adj (M i j))) (λ j → TC.norm (M i j)) (λ j → norm-product-real (M i j)))))

zero-trace-gram : ∀ {n} (M : Mat n) → trace (gram M) ≡ 0# → ∀ i j → M i j ≡ 0#
zero-trace-gram M h i = zero-sum-entry (M i) (ZP.≤-antisym
  (subst (λ x → normRow i Z.≤ x) total-zero (term-le-sum normRow nonnegative i)) (nonnegative i))
  where
  normRow = λ i → intSum (λ j → TC.norm (M i j))
  nonnegative : ∀ i → (+ 0) Z.≤ normRow i
  nonnegative i = sum-nonnegative (λ j → TC.norm (M i j)) (λ j → norm-nonnegative (M i j))
  total-zero : intSum normRow ≡ (+ 0)
  total-zero = trans (sym (trace-norm M)) (cong re h)
