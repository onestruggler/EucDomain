-- Tools for computing with the canonical representation of the
-- dyadic fractions 𝔻 = ℤ[½] and with the embedding
--
--   from-whole : ℤ[i] → 𝔻[i]
--
-- of the ring of integers (Quantum.Synthesis.Ring.WholePart). They
-- are used for the least denominator exponent (Definition II.1) in
-- Kopt.Properties.Lde and for the K action in Kopt.Properties.Algebra.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.DyadicTools where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∨_ ; T ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim ; ⊥-elim-irr)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NatP
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as IntP
open import Data.Product.Base using (_×_ ; _,_ ; ∃)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Instances
open import Quantum.Synthesis.Ring
open import Kopt.Base
open import Kopt.Properties.Gamma

private
  recompute-T : ∀ b -> .(T b) -> T b
  recompute-T true _ = tt
  recompute-T false p = ⊥-elim-irr p

  T-contra : ∀ {b} -> T b -> T (not b) -> ⊥
  T-contra {true} _ ()
  T-contra {false} () _

  T-∨ʳ : ∀ x {y} -> T y -> T (x ∨ y)
  T-∨ʳ true _ = tt
  T-∨ʳ false p = p

  re-eq : ∀ {A : Set} {x y u v : A} -> Cplx x y ≡ Cplx u v -> x ≡ u
  re-eq refl = refl

  im-eq : ∀ {A : Set} {x y u v : A} -> Cplx x y ≡ Cplx u v -> y ≡ v
  im-eq refl = refl

-- ----------------------------------------------------------------------
-- * The canonical representation

-- Any (a, 0) is canonical, and (a, n) is canonical for odd a.
canon-0 : ∀ a -> T (Canonical a 0)
canon-0 a = tt

canon-odd : ∀ a n -> T (not (evenℤ a)) -> T (Canonical a n)
canon-odd a n h = T-∨ʳ (n Nat.≡ᵇ 0) h

-- A dyadic fraction with a positive exponent has an odd numerator.
-- (The canonicity field is irrelevant, but T is decidable, so the
-- proof can be recomputed.)
canonical-odd : ∀ a n -> .(T (Canonical a (suc n))) -> T (not (evenℤ a))
canonical-odd a n c = recompute-T (not (evenℤ a)) c

-- The smart constructor on canonical arguments.
dyadic-0 : ∀ a -> dyadic a 0 ≡ Dyadic' a 0 (canon-0 a)
dyadic-0 (+ zero) = refl
dyadic-0 (+ suc n) = refl
dyadic-0 -[1+ n ] = refl

dyadic-odd : ∀ a n (h : T (not (evenℤ a))) -> dyadic a n ≡ Dyadic' a n (canon-odd a n h)
dyadic-odd (+ zero) n h = ⊥-elim h
dyadic-odd (+ suc m) zero h = dyadic-0 (+ suc m)
dyadic-odd -[1+ m ] zero h = dyadic-0 -[1+ m ]
dyadic-odd a@(+ suc m) (suc n) h with T? (evenℤ a)
... | yes e = ⊥-elim (T-contra e h)
... | no _ = refl
dyadic-odd a@(-[1+ m ]) (suc n) h with T? (evenℤ a)
... | yes e = ⊥-elim (T-contra e h)
... | no _ = refl

dyadic-canon : ∀ a n (c : T (Canonical a n)) -> dyadic a n ≡ Dyadic' a n c
dyadic-canon a zero c = dyadic-0 a
dyadic-canon a (suc n) c = dyadic-odd a (suc n) c

-- One halving step of the smart constructor.
dyadic-even-step : ∀ a n -> T (evenℤ a) -> dyadic a (suc n) ≡ dyadic (shiftR a 1) n
dyadic-even-step (+ zero) n e = refl
dyadic-even-step a@(+ suc m) n e with T? (evenℤ a)
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e e)
dyadic-even-step a@(-[1+ m ]) n e with T? (evenℤ a)
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e e)

-- ----------------------------------------------------------------------
-- * from-whole : ℤ → 𝔻

fromℤ-Dyadic : ∀ a -> (Dyadic ∋ from-whole a) ≡ Dyadic' a 0 (canon-0 a)
fromℤ-Dyadic (+ zero) = refl
fromℤ-Dyadic (+ suc n) = refl
fromℤ-Dyadic -[1+ n ] = dyadic-0 -[1+ n ]

fromℤ-+ : ∀ a b -> (Dyadic ∋ from-whole (a + b)) ≡ from-whole a + from-whole b
fromℤ-+ a b = begin
  from-whole (a + b)                   ≡⟨ fromℤ-Dyadic (a + b) ⟩
  Dyadic' (a + b) 0 (canon-0 (a + b))  ≡⟨ sym (dyadic-canon (a + b) 0 (canon-0 (a + b))) ⟩
  dyadic (a + b) 0                     ≡⟨ cong (λ z -> dyadic z 0) (cong (Int._+ b) (sym (IntP.*-identityʳ a))) ⟩
  dyadic ((a * + 1) + b) 0             ≡⟨ sym (cong₂ (λ u v -> u + v) (fromℤ-Dyadic a) (fromℤ-Dyadic b)) ⟩
  from-whole a + from-whole b          ∎
  where open ≡-Reasoning

fromℤ-* : ∀ a b -> (Dyadic ∋ from-whole (a * b)) ≡ from-whole a * from-whole b
fromℤ-* a b = begin
  from-whole (a * b)                   ≡⟨ fromℤ-Dyadic (a * b) ⟩
  Dyadic' (a * b) 0 (canon-0 (a * b))  ≡⟨ sym (dyadic-canon (a * b) 0 (canon-0 (a * b))) ⟩
  dyadic (a * b) 0                     ≡⟨ sym (cong₂ (λ u v -> u * v) (fromℤ-Dyadic a) (fromℤ-Dyadic b)) ⟩
  from-whole a * from-whole b          ∎
  where open ≡-Reasoning

fromℤ-neg : ∀ a -> (Dyadic ∋ from-whole (Int.- a)) ≡ - from-whole a
fromℤ-neg a = begin
  from-whole (Int.- a)                          ≡⟨ fromℤ-Dyadic (Int.- a) ⟩
  Dyadic' (Int.- a) 0 (canon-0 (Int.- a))       ≡⟨ sym (dyadic-canon (Int.- a) 0 (canon-0 (Int.- a))) ⟩
  dyadic (Int.- a) 0                            ≡⟨ sym (cong (λ d -> - d) (fromℤ-Dyadic a)) ⟩
  - from-whole a                                ∎
  where open ≡-Reasoning

fromℤ-minus : ∀ a b -> (Dyadic ∋ from-whole (a - b)) ≡ from-whole a - from-whole b
fromℤ-minus a b = trans (fromℤ-+ a (Int.- b)) (cong (λ z -> from-whole a + z) (fromℤ-neg b))

fromℤ-injective : ∀ {a b} -> (Dyadic ∋ from-whole a) ≡ from-whole b -> a ≡ b
fromℤ-injective {a} {b} e = cong Dyadic.numerator
  (trans (sym (fromℤ-Dyadic a)) (trans e (fromℤ-Dyadic b)))

to-whole-fromℤ : ∀ a -> to-whole (Dyadic ∋ from-whole a) ≡ a
to-whole-fromℤ a = trans (cong (λ d -> to-whole d) (fromℤ-Dyadic a)) (IntP.*-identityʳ a)

-- ----------------------------------------------------------------------
-- * from-whole : ℤ[i] → 𝔻[i] is an injective ring homomorphism

from-whole-+ : ∀ (z w : ZComplex) -> (DComplex ∋ from-whole (z + w)) ≡ from-whole z + from-whole w
from-whole-+ (Cplx a b) (Cplx c d) = cong₂ Cplx (fromℤ-+ a c) (fromℤ-+ b d)

from-whole-neg : ∀ (z : ZComplex) -> (DComplex ∋ from-whole (- z)) ≡ - from-whole z
from-whole-neg (Cplx a b) = cong₂ Cplx (fromℤ-neg a) (fromℤ-neg b)

from-whole-minus : ∀ (z w : ZComplex) -> (DComplex ∋ from-whole (z - w)) ≡ from-whole z - from-whole w
from-whole-minus z w = trans (from-whole-+ z (- w)) (cong (λ u -> from-whole z + u) (from-whole-neg w))

from-whole-* : ∀ (z w : ZComplex) -> (DComplex ∋ from-whole (z * w)) ≡ from-whole z * from-whole w
from-whole-* (Cplx a b) (Cplx c d) = cong₂ Cplx
  (trans (fromℤ-minus (a * c) (b * d)) (cong₂ (λ u v -> u - v) (fromℤ-* a c) (fromℤ-* b d)))
  (trans (fromℤ-+ (a * d) (b * c)) (cong₂ (λ u v -> u + v) (fromℤ-* a d) (fromℤ-* b c)))

from-whole-injective : ∀ {z w : ZComplex} -> (DComplex ∋ from-whole z) ≡ from-whole w -> z ≡ w
from-whole-injective {Cplx a b} {Cplx c d} e =
  cong₂ Cplx (fromℤ-injective (re-eq e)) (fromℤ-injective (im-eq e))

to-whole-from-whole : ∀ (z : ZComplex) -> to-whole (DComplex ∋ from-whole z) ≡ z
to-whole-from-whole (Cplx a b) = cong₂ Cplx (to-whole-fromℤ a) (to-whole-fromℤ b)

-- The embedding respects the constants of Section II.
from-whole-0 : (DComplex ∋ from-whole 0#) ≡ 0#
from-whole-0 = refl

from-whole-1 : (DComplex ∋ from-whole 1#) ≡ 1#
from-whole-1 = refl

from-whole-i : (DComplex ∋ from-whole i) ≡ i
from-whole-i = refl

from-whole-γ : (DComplex ∋ from-whole γ) ≡ γ
from-whole-γ = refl

-- Powers.
from-whole-↑ : ∀ (z : ZComplex) n -> (DComplex ∋ from-whole (z ↑ n)) ≡ (from-whole z) ↑ n
from-whole-↑ z zero = refl
from-whole-↑ z (suc n) = trans (from-whole-* z (z ↑ n)) (cong (λ w -> from-whole z * w) (from-whole-↑ z n))

from-whole-γ↑ : ∀ n -> (DComplex ∋ from-whole (γ ↑ n)) ≡ (γ {DComplex}) ↑ n
from-whole-γ↑ n = trans (from-whole-↑ γ n) (cong (λ z -> z ↑ n) from-whole-γ)
