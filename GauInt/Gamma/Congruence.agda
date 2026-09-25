{-# OPTIONS --safe --without-K #-}

-- Constructive congruences modulo arbitrary powers of gamma.
module GauInt.Gamma.Congruence where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (γ; powγ)
open import GauInt.Algebra
open import GauInt.Gamma using (γ-cancel)
open import GauInt.Gamma using (Evenγ) renaming (gaussianParity to parity)
open import GauInt.Gamma.Division using (divideGamma; divide-multiple; divide-complete)
import GauInt.Parity as GP
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.GeneralisedArithmetic as Iteration
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open GaussianSolver

Cong : ℕ → ZComplex → ZComplex → Set
Cong n a b = Σ[ q ∈ ZComplex ] a ≡ b + q * powγ n

cong-refl : ∀ n a → Cong n a a
cong-refl n a = 0# , sym (solve 2 (λ a p → a :+ con 0# :* p := a) refl a (powγ n))

cong-sym : ∀ n a b → Cong n a b → Cong n b a
cong-sym n a b (q , h) = - q , trans
  (solve 3 (λ b q p → b := (b :+ q :* p) :+ (:- q) :* p) refl b q (powγ n))
  (cong (λ x → x + (- q) * powγ n) (sym h))

cong-trans : ∀ n a b c → Cong n a b → Cong n b c → Cong n a c
cong-trans n a b c (q , hq) (r , hr) = r + q , trans hq
  (trans (cong (λ x → x + q * powγ n) hr)
    (solve 4 (λ c r q p → (c :+ r :* p) :+ q :* p := c :+ (r :+ q) :* p) refl c r q (powγ n)))

cong-add : ∀ n a b c d → Cong n a b → Cong n c d → Cong n (a + c) (b + d)
cong-add n a b c d (q , hq) (r , hr) = q + r , trans (cong₂ _+_ hq hr)
  (solve 5 (λ b d q r p → (b :+ q :* p) :+ (d :+ r :* p) := (b :+ d) :+ (q :+ r) :* p) refl b d q r (powγ n))

cong-mul : ∀ n a b c d → Cong n a b → Cong n c d → Cong n (a * c) (b * d)
cong-mul n a b c d (q , hq) (r , hr) = b * r + q * d + (q * r) * powγ n ,
  trans (cong₂ _*_ hq hr) (solve 5 (λ b d q r p →
    (b :+ q :* p) :* (d :+ r :* p) := b :* d :+ (b :* r :+ q :* d :+ (q :* r) :* p) :* p) refl b d q r (powγ n))

conjugatePhase : ℕ → ZComplex
conjugatePhase = Iteration.fold 1# (_* (- TC.i))

conjugate-power : ∀ n → TC.adj (powγ n) ≡ conjugatePhase n * powγ n
conjugate-power zero = refl
conjugate-power (suc n) = trans (conj-mul (powγ n) γ)
  (trans (cong (_* TC.adj γ) (conjugate-power n))
    (solve 2 (λ u p → (u :* p) :* con (TC.adj γ) := (u :* con (- TC.i)) :* (p :* con γ)) refl (conjugatePhase n) (powγ n)))

cong-conj : ∀ n a b → Cong n a b → Cong n (TC.adj a) (TC.adj b)
cong-conj n a b (q , h) = TC.adj q * conjugatePhase n , trans (cong TC.adj h)
  (trans (conj-add b (q * powγ n)) (cong (TC.adj b TC.+_)
    (trans (conj-mul q (powγ n)) (trans (cong (TC.adj q *_) (conjugate-power n)) (sym (*-assoc (TC.adj q) (conjugatePhase n) (powγ n)))))))

lower : ∀ n a b → Cong (suc n) a b → Cong n a b
lower n a b (q , h) = q * γ , trans h
  (cong (b TC.+_) (solve 2 (λ q p → q :* (p :* con γ) := (q :* con γ) :* p) refl q (powγ n)))

quotient : ℕ → ZComplex → ZComplex
quotient zero z = z
quotient (suc n) z = quotient n (divideGamma z)

quotient-multiple : ∀ n q → quotient n (q * powγ n) ≡ q
quotient-multiple zero q = *-identityʳ q
quotient-multiple (suc n) q = trans
  (cong (quotient n) (trans (cong divideGamma (sym (*-assoc q (powγ n) γ))) (divide-multiple (q * powγ n))))
  (quotient-multiple n q)

recover-quotient : ∀ n a b q → a ≡ b + q * powγ n → quotient n (a - b) ≡ q
recover-quotient n a b q h = trans
  (cong (quotient n) (trans (cong (_- b) h) (solve 2 (λ b x → (b :+ x) :- b := x) refl b (q * powγ n))))
  (quotient-multiple n q)

decideWith : ∀ n a b → Dec (a ≡ b + quotient n (a - b) * powγ n) → Dec (Cong n a b)
decideWith n a b (yes h) = yes (quotient n (a - b) , h)
decideWith n a b (no hn) = no (λ { (q , h) → hn (trans h
  (cong (λ x → b + x * powγ n) (sym (recover-quotient n a b q h)))) })

cong? : ∀ n a b → Dec (Cong n a b)
cong? n a b = decideWith n a b (a TC.≟ (b + quotient n (a - b) * powγ n))

even-transport : ∀ n a b → Cong (suc n) a b → Evenγ b → Evenγ a
even-transport n a b (q , hq) (r , hr) = r + q * powγ n , trans hq
  (trans (cong (λ x → x + q * powγ (suc n)) hr)
    (solve 3 (λ r q p → r :* con γ :+ q :* (p :* con γ) := (r :+ q :* p) :* con γ) refl r q (powγ n)))

parity-congruent : ∀ n a b → Cong (suc n) a b → parity a ≡ parity b
parity-congruent n a b h = finish (GP.parity-cases a) (GP.parity-cases b)
  where
  bad : 1 ≡ 0 → ⊥
  bad ()
  finish : (parity a ≡ 0 Data.Sum.⊎ parity a ≡ 1) → (parity b ≡ 0 Data.Sum.⊎ parity b ≡ 1) → parity a ≡ parity b
  finish (inj₁ ha) (inj₁ hb) = trans ha (sym hb)
  finish (inj₂ ha) (inj₂ hb) = trans ha (sym hb)
  finish (inj₁ ha) (inj₂ hb) = ⊥-elim (bad (trans (sym hb) (GP.even-parity-zero b
    (even-transport n b a (cong-sym (suc n) a b h) (GP.zero-parity-even a ha)))))
  finish (inj₂ ha) (inj₁ hb) = ⊥-elim (bad (trans (sym ha) (GP.even-parity-zero a
    (even-transport n a b h (GP.zero-parity-even b hb)))))

divide-congruent : ∀ n a b → Evenγ a → Evenγ b → Cong (suc n) a b → Cong n (divideGamma a) (divideGamma b)
divide-congruent n a b ha hb (q , h) = q , γ-cancel
  (trans (divide-complete a ha) (trans h (trans (cong (λ x → x + q * powγ (suc n)) (sym (divide-complete b hb)))
    (solve 3 (λ b q p → con γ :* b :+ q :* (p :* con γ) := con γ :* (b :+ q :* p)) refl (divideGamma b) q (powγ n)))))
