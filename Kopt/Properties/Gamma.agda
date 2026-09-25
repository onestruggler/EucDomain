-- Section II of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the algebra of the Gaussian prime γ = 1 + i in ℤ[i], the parity of
-- Definition II.4, the norm (Lemma II.5), congruences modulo powers
-- of γ and the cancellation Lemma II.6.
--
-- This module does not open Literals, so that the ℕ literals in the
-- ring solver calls are ordinary natural numbers; elements of ℤ[i]
-- are written with 0#, 1#, fromℕ, i and the constructor Cplx.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.Gamma where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NatP
import Data.Nat.DivMod as NDM
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as IntP
import Data.Integer.DivMod as IDM
import Data.Integer.Solver as IntSolver
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
import GauInt.Properties as GP

private
  module ℤS = IntSolver.+-*-Solver
  module GS = ZSolver commutativeRing-ZComplex

  false≢true : false ≡ true -> ⊥
  false≢true ()

  2ℤ : ℤ
  2ℤ = + 2

-- ----------------------------------------------------------------------
-- * Powers
--
-- The framework's _^_ (Typeclasses.SemiRing) is computed by repeated
-- squaring and cannot be unfolded for a symbolic exponent (its helper
-- functions live in an inaccessible where block), so the statements
-- below use the structural power x ↑ n = x * ... * x instead.

infixr 8 _↑_
_↑_ : {A : Set} {{_ : Ring A}} -> A -> ℕ -> A
x ↑ zero = 1#
x ↑ suc n = x * (x ↑ n)

-- ----------------------------------------------------------------------
-- * Parity of natural numbers and integers

-- Every natural number is of the form 2k or 2k+1.
ℕ-parity : ∀ n -> (∃ λ k -> n ≡ 2 Nat.* k) ⊎ (∃ λ k -> n ≡ suc (2 Nat.* k))
ℕ-parity zero = inj₁ (0 , refl)
ℕ-parity (suc zero) = inj₂ (0 , refl)
ℕ-parity (suc (suc n)) with ℕ-parity n
... | inj₁ (k , e) = inj₁ (suc k , trans (cong (λ m -> suc (suc m)) e) (sym (NatP.*-suc 2 k)))
... | inj₂ (k , e) = inj₂ (suc k , trans (cong (λ m -> suc (suc m)) e) (cong suc (sym (NatP.*-suc 2 k))))

private
  pos-suc : ∀ m -> + (suc m) ≡ + m + + 1
  pos-suc m = cong +_ (NatP.+-comm 1 m)

  pos-odd : ∀ n k -> n ≡ suc (2 Nat.* k) -> + n ≡ 2ℤ * + k + + 1
  pos-odd n k e = trans (cong +_ e)
    (trans (pos-suc (2 Nat.* k)) (cong (Int._+ + 1) (IntP.pos-* 2 k)))

-- Every integer is of the form 2k or 2k+1.
ℤ-parity : ∀ z -> (∃ λ k -> z ≡ 2ℤ * k) ⊎ (∃ λ k -> z ≡ 2ℤ * k + + 1)
ℤ-parity (+ n) with ℕ-parity n
... | inj₁ (k , e) = inj₁ (+ k , trans (cong +_ e) (IntP.pos-* 2 k))
... | inj₂ (k , e) = inj₂ (+ k , pos-odd n k e)
ℤ-parity -[1+ n ] with ℕ-parity (suc n)
... | inj₁ (k , e) = inj₁ (Int.- (+ k) ,
      trans (cong (Int.-_) (trans (cong +_ e) (IntP.pos-* 2 k))) (IntP.neg-distribʳ-* 2ℤ (+ k)))
... | inj₂ (k , e) = inj₂ (Int.- (+ suc k) , (begin
      -[1+ n ]                       ≡⟨ cong (Int.-_) (pos-odd (suc n) k e) ⟩
      Int.- (2ℤ * + k + + 1)         ≡⟨ solve 1 (λ x -> :- (con (+ 2) :* x :+ con (+ 1))
                                          := con (+ 2) :* (:- (x :+ con (+ 1))) :+ con (+ 1)) refl (+ k) ⟩
      2ℤ * (Int.- (+ k + + 1)) + + 1 ≡⟨ cong (λ z -> 2ℤ * (Int.- z) + + 1) (sym (pos-suc k)) ⟩
      2ℤ * (Int.- (+ suc k)) + + 1   ∎))
      where
        open ≡-Reasoning
        open ℤS

-- Multiples of 2 are even, and 2k+1 is odd.
even-2* : ∀ k -> evenℤ (2ℤ * k) ≡ true
even-2* k = begin
  evenℕ ∣ 2ℤ * k ∣        ≡⟨ cong evenℕ (IntP.abs-* 2ℤ k) ⟩
  evenℕ (2 Nat.* ∣ k ∣)   ≡⟨ cong evenℕ (NatP.*-comm 2 ∣ k ∣) ⟩
  evenℕ (∣ k ∣ Nat.* 2)   ≡⟨ cong (Nat._≡ᵇ 0) (NDM.m*n%n≡0 ∣ k ∣ 2) ⟩
  true                    ∎
  where open ≡-Reasoning

private
  -- (These two are also in Quantum.Synthesis.Ring.Properties.Dyadic,
  -- but private there.)
  even⇒%2≡0 : ∀ a -> evenℤ a ≡ true -> a Int.%ℕ 2 ≡ 0
  even⇒%2≡0 (+ n) eq = NatP.≡ᵇ⇒≡ (n Nat.% 2) 0 (subst T (sym eq) tt)
  even⇒%2≡0 -[1+ n ] eq with suc n Nat.% 2 | NatP.≡ᵇ⇒≡ (suc n Nat.% 2) 0 (subst T (sym eq) tt)
  ... | zero | _ = refl
  ... | suc _ | ()

  -- For even a, a/2 ⋅ 2 = a.
  shiftR-even : ∀ a -> evenℤ a ≡ true -> shiftR a 1 * 2ℤ ≡ a
  shiftR-even a eq = sym (begin
    a                                     ≡⟨ IDM.a≡a%n+[a/n]*n a (+ 2) ⟩
    + (a Int.%ℕ 2) + shiftR a 1 * 2ℤ      ≡⟨ cong (λ r -> + r + shiftR a 1 * 2ℤ) (even⇒%2≡0 a eq) ⟩
    + 0 + shiftR a 1 * 2ℤ                 ≡⟨ IntP.+-identityˡ _ ⟩
    shiftR a 1 * 2ℤ                       ∎)
    where open ≡-Reasoning

  one-even-absurd : ∀ (m k : ℤ) -> 2ℤ * k + + 1 ≡ m * 2ℤ -> ⊥
  one-even-absurd m k e = false≢true (trans (cong evenℤ step) (even-2* (m - k)))
    where
      open ≡-Reasoning
      open ℤS
      step : + 1 ≡ 2ℤ * (m - k)
      step = begin
        + 1                          ≡⟨ solve 1 (λ x -> con (+ 1)
                                          := (con (+ 2) :* x :+ con (+ 1)) :- con (+ 2) :* x) refl k ⟩
        (2ℤ * k + + 1) - 2ℤ * k      ≡⟨ cong (Int._- 2ℤ * k) e ⟩
        m * 2ℤ - 2ℤ * k              ≡⟨ solve 2 (λ x y -> x :* con (+ 2) :- con (+ 2) :* y
                                          := con (+ 2) :* (x :- y)) refl m k ⟩
        2ℤ * (m - k)                 ∎

odd-2*+1 : ∀ k -> evenℤ (2ℤ * k + + 1) ≡ false
odd-2*+1 k with evenℤ (2ℤ * k + + 1) in eq
... | false = refl
... | true = ⊥-elim (one-even-absurd (shiftR (2ℤ * k + + 1) 1) k (sym (shiftR-even _ eq)))

-- Reading off the decomposition from the boolean test.
even⇒2∣ : ∀ z -> evenℤ z ≡ true -> ∃ λ k -> z ≡ 2ℤ * k
even⇒2∣ z h with ℤ-parity z
... | inj₁ p = p
... | inj₂ (k , e) = ⊥-elim (false≢true (trans (sym (trans (cong evenℤ e) (odd-2*+1 k))) h))

odd⇒2∣+1 : ∀ z -> evenℤ z ≡ false -> ∃ λ k -> z ≡ 2ℤ * k + + 1
odd⇒2∣+1 z h with ℤ-parity z
... | inj₂ p = p
... | inj₁ (k , e) = ⊥-elim (false≢true (trans (sym h) (trans (cong evenℤ e) (even-2* k))))

-- Adding a multiple of 2 does not change the parity.
even-cong-2 : ∀ z w k -> z ≡ w + 2ℤ * k -> evenℤ z ≡ evenℤ w
even-cong-2 z w k e with ℤ-parity w
... | inj₁ (j , ew) = trans (trans (cong evenℤ zeq) (even-2* (j + k))) (sym (trans (cong evenℤ ew) (even-2* j)))
  where
    open ≡-Reasoning
    open ℤS
    zeq : z ≡ 2ℤ * (j + k)
    zeq = begin
      z                  ≡⟨ e ⟩
      w + 2ℤ * k         ≡⟨ cong (Int._+ 2ℤ * k) ew ⟩
      2ℤ * j + 2ℤ * k    ≡⟨ solve 2 (λ x y -> con (+ 2) :* x :+ con (+ 2) :* y
                              := con (+ 2) :* (x :+ y)) refl j k ⟩
      2ℤ * (j + k)       ∎
... | inj₂ (j , ew) = trans (trans (cong evenℤ zeq) (odd-2*+1 (j + k))) (sym (trans (cong evenℤ ew) (odd-2*+1 j)))
  where
    open ≡-Reasoning
    open ℤS
    zeq : z ≡ 2ℤ * (j + k) + + 1
    zeq = begin
      z                              ≡⟨ e ⟩
      w + 2ℤ * k                     ≡⟨ cong (Int._+ 2ℤ * k) ew ⟩
      (2ℤ * j + + 1) + 2ℤ * k        ≡⟨ solve 2 (λ x y -> (con (+ 2) :* x :+ con (+ 1)) :+ con (+ 2) :* y
                                          := con (+ 2) :* (x :+ y) :+ con (+ 1)) refl j k ⟩
      2ℤ * (j + k) + + 1             ∎

-- a² has the same parity as a.
sq-parity : ∀ a -> ∃ λ k -> a * a ≡ a + 2ℤ * k
sq-parity a with ℤ-parity a
... | inj₁ (m , e) = (2ℤ * m * m - m) , (begin
      a * a                               ≡⟨ cong₂ Int._*_ e e ⟩
      (2ℤ * m) * (2ℤ * m)                 ≡⟨ solve 1 (λ x -> (con (+ 2) :* x) :* (con (+ 2) :* x)
                                               := con (+ 2) :* x :+ con (+ 2) :* (con (+ 2) :* x :* x :- x)) refl m ⟩
      (2ℤ * m) + 2ℤ * (2ℤ * m * m - m)    ≡⟨ cong (Int._+ 2ℤ * (2ℤ * m * m - m)) (sym e) ⟩
      a + 2ℤ * (2ℤ * m * m - m)           ∎)
  where
    open ≡-Reasoning
    open ℤS
... | inj₂ (m , e) = (2ℤ * m * m + m) , (begin
      a * a                                       ≡⟨ cong₂ Int._*_ e e ⟩
      (2ℤ * m + + 1) * (2ℤ * m + + 1)             ≡⟨ solve 1 (λ x -> (con (+ 2) :* x :+ con (+ 1)) :* (con (+ 2) :* x :+ con (+ 1))
                                                       := (con (+ 2) :* x :+ con (+ 1)) :+ con (+ 2) :* (con (+ 2) :* x :* x :+ x)) refl m ⟩
      (2ℤ * m + + 1) + 2ℤ * (2ℤ * m * m + m)      ≡⟨ cong (Int._+ 2ℤ * (2ℤ * m * m + m)) (sym e) ⟩
      a + 2ℤ * (2ℤ * m * m + m)                   ∎)
  where
    open ≡-Reasoning
    open ℤS

-- ----------------------------------------------------------------------
-- * The Gaussian prime γ = 1 + i

-- γ = 1 + i, γ† = 1 - i, γ² = 2i and γγ† = 2 (Section II).
γ-def : (γ {ZComplex}) ≡ Cplx (+ 1) (+ 1)
γ-def = refl

γ†-def : (γ† {ZComplex}) ≡ Cplx (+ 1) (Int.- (+ 1))
γ†-def = refl

γ-squared : (γ {ZComplex}) * γ ≡ fromℕ 2 * i
γ-squared = refl

γ-γ† : (γ {ZComplex}) * γ† ≡ fromℕ 2
γ-γ† = refl

-- γ† = -i γ.
γ†≡-iγ : (γ† {ZComplex}) ≡ (- i) * γ
γ†≡-iγ = refl

γ≢0 : ¬ ((γ {ZComplex}) ≡ 0#)
γ≢0 ()

-- ----------------------------------------------------------------------
-- * Parity of Gaussian integers (Definition II.4)

private
  if-even : ∀ b -> (if b then Even else Odd) ≡ Even -> b ≡ true
  if-even true _ = refl
  if-even false ()

  if-odd : ∀ b -> (if b then Even else Odd) ≡ Odd -> b ≡ false
  if-odd false _ = refl
  if-odd true ()

-- x = a + bi is even if and only if a + b is an even integer.
even-sum : ∀ a b -> parityℤ[i] (Cplx a b) ≡ Even -> evenℤ (a + b) ≡ true
even-sum a b p = if-even _ p

odd-sum : ∀ a b -> parityℤ[i] (Cplx a b) ≡ Odd -> evenℤ (a + b) ≡ false
odd-sum a b p = if-odd _ p

from-even : ∀ a b -> evenℤ (a + b) ≡ true -> parityℤ[i] (Cplx a b) ≡ Even
from-even a b e = cong (λ t -> if t then Even else Odd) e

from-odd : ∀ a b -> evenℤ (a + b) ≡ false -> parityℤ[i] (Cplx a b) ≡ Odd
from-odd a b e = cong (λ t -> if t then Even else Odd) e

-- Multiplication by γ, in coordinates.
γ*-Cplx : ∀ c d -> γ * Cplx c d ≡ Cplx (c - d) (d + c)
γ*-Cplx c d = cong₂ Cplx (cong₂ Int._-_ (IntP.*-identityˡ c) (IntP.*-identityˡ d))
                         (cong₂ Int._+_ (IntP.*-identityˡ d) (IntP.*-identityˡ c))

private
  diff-even : ∀ a b -> evenℤ (a + b) ≡ true -> evenℤ (b - a) ≡ true
  diff-even a b e with even⇒2∣ (a + b) e
  ... | k , eq = trans (cong evenℤ lemma) (even-2* (k - a))
    where
      open ≡-Reasoning
      open ℤS
      lemma : b - a ≡ 2ℤ * (k - a)
      lemma = begin
        b - a               ≡⟨ solve 2 (λ x y -> y :- x := (x :+ y) :- con (+ 2) :* x) refl a b ⟩
        (a + b) - 2ℤ * a    ≡⟨ cong (Int._- 2ℤ * a) eq ⟩
        2ℤ * k - 2ℤ * a     ≡⟨ solve 2 (λ x y -> con (+ 2) :* x :- con (+ 2) :* y
                                 := con (+ 2) :* (x :- y)) refl k a ⟩
        2ℤ * (k - a)        ∎

  cancel₁ : ∀ p q a b -> p * 2ℤ ≡ a + b -> q * 2ℤ ≡ b - a -> p - q ≡ a
  cancel₁ p q a b hp hq = IntP.*-cancelʳ-≡ (p - q) a 2ℤ (begin
    (p - q) * 2ℤ        ≡⟨ solve 2 (λ x y -> (x :- y) :* con (+ 2) := x :* con (+ 2) :- y :* con (+ 2)) refl p q ⟩
    p * 2ℤ - q * 2ℤ     ≡⟨ cong₂ Int._-_ hp hq ⟩
    (a + b) - (b - a)   ≡⟨ solve 2 (λ x y -> (x :+ y) :- (y :- x) := x :* con (+ 2)) refl a b ⟩
    a * 2ℤ              ∎)
    where
      open ≡-Reasoning
      open ℤS

  cancel₂ : ∀ p q a b -> p * 2ℤ ≡ a + b -> q * 2ℤ ≡ b - a -> q + p ≡ b
  cancel₂ p q a b hp hq = IntP.*-cancelʳ-≡ (q + p) b 2ℤ (begin
    (q + p) * 2ℤ        ≡⟨ solve 2 (λ x y -> (y :+ x) :* con (+ 2) := x :* con (+ 2) :+ y :* con (+ 2)) refl p q ⟩
    p * 2ℤ + q * 2ℤ     ≡⟨ cong₂ Int._+_ hp hq ⟩
    (a + b) + (b - a)   ≡⟨ solve 2 (λ x y -> (x :+ y) :+ (y :- x) := y :* con (+ 2)) refl a b ⟩
    b * 2ℤ              ∎)
    where
      open ≡-Reasoning
      open ℤS

-- Division by γ is exact for even Gaussian integers: γ ⋅ (x/γ) = x.
γ-div-even : ∀ x -> parityℤ[i] x ≡ Even -> γ * (x /γ) ≡ x
γ-div-even (Cplx a b) p = trans (γ*-Cplx (shiftR (a + b) 1) (shiftR (b - a) 1)) (cong₂ Cplx
  (cancel₁ (shiftR (a + b) 1) (shiftR (b - a) 1) a b (shiftR-even (a + b) ea) (shiftR-even (b - a) eb))
  (cancel₂ (shiftR (a + b) 1) (shiftR (b - a) 1) a b (shiftR-even (a + b) ea) (shiftR-even (b - a) eb)))
  where
    ea : evenℤ (a + b) ≡ true
    ea = even-sum a b p
    eb : evenℤ (b - a) ≡ true
    eb = diff-even a b ea

-- Definition II.4: x is even if and only if γ divides x.
even⇒divides : ∀ x -> parityℤ[i] x ≡ Even -> ∃ λ y -> x ≡ γ * y
even⇒divides x p = (x /γ) , sym (γ-div-even x p)

γ*-even : ∀ y -> parityℤ[i] (γ * y) ≡ Even
γ*-even (Cplx c d) = trans (cong parityℤ[i] (γ*-Cplx c d))
  (from-even (c - d) (d + c) (trans (cong evenℤ lemma) (even-2* c)))
  where
    open ℤS
    lemma : (c - d) + (d + c) ≡ 2ℤ * c
    lemma = solve 2 (λ x y -> (x :- y) :+ (y :+ x) := con (+ 2) :* x) refl c d

divides⇒even : ∀ x y -> x ≡ γ * y -> parityℤ[i] x ≡ Even
divides⇒even x y e = trans (cong parityℤ[i] e) (γ*-even y)

-- For odd x, x - 1 is even, so x = 1 + γ ⋅ ((x-1)/γ).
odd⇒even-1 : ∀ x -> parityℤ[i] x ≡ Odd -> parityℤ[i] (x - 1#) ≡ Even
odd⇒even-1 (Cplx a b) p with odd⇒2∣+1 (a + b) (odd-sum a b p)
... | k , e = from-even (a + Int.- (+ 1)) (b + Int.- (+ 0)) (trans (cong evenℤ lemma) (even-2* k))
  where
    open ≡-Reasoning
    open ℤS
    lemma : (a + Int.- (+ 1)) + (b + Int.- (+ 0)) ≡ 2ℤ * k
    lemma = begin
      (a + Int.- (+ 1)) + (b + Int.- (+ 0))   ≡⟨ solve 2 (λ x y -> (x :- con (+ 1)) :+ (y :- con (+ 0))
                                                   := (x :+ y) :- con (+ 1)) refl a b ⟩
      (a + b) - + 1                           ≡⟨ cong (Int._- + 1) e ⟩
      (2ℤ * k + + 1) - + 1                    ≡⟨ solve 1 (λ x -> (con (+ 2) :* x :+ con (+ 1)) :- con (+ 1)
                                                   := con (+ 2) :* x) refl k ⟩
      2ℤ * k                                  ∎

odd-div : ∀ x -> parityℤ[i] x ≡ Odd -> γ * ((x - 1#) /γ) ≡ x - 1#
odd-div x p = γ-div-even (x - 1#) (odd⇒even-1 x p)

-- γ is not a unit.
γ-not-unit : ∀ (u : ZComplex) -> ¬ (γ * u ≡ 1#)
γ-not-unit u e = bad (trans (sym (γ*-even u)) (cong parityℤ[i] e))
  where
    bad : Even ≡ Odd -> ⊥
    bad ()

-- ----------------------------------------------------------------------
-- * Parity is a ring homomorphism ℤ[i] → ℤ₂

private
  parity-+ℤ : ∀ s t -> (if evenℤ (s + t) then Even else Odd)
                     ≡ (if evenℤ s then Even else Odd) + (if evenℤ t then Even else Odd)
  parity-+ℤ s t with ℤ-parity s | ℤ-parity t
  ... | inj₁ (m , es) | inj₁ (n , et) =
        trans (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ sumeq) (even-2* (m + n))))
              (cong₂ (λ u v -> u + v) (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ es) (even-2* m))))
                                      (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ et) (even-2* n)))))
    where
      open ≡-Reasoning
      open ℤS
      sumeq : s + t ≡ 2ℤ * (m + n)
      sumeq = begin
        s + t                ≡⟨ cong₂ Int._+_ es et ⟩
        2ℤ * m + 2ℤ * n      ≡⟨ solve 2 (λ x y -> con (+ 2) :* x :+ con (+ 2) :* y := con (+ 2) :* (x :+ y)) refl m n ⟩
        2ℤ * (m + n)         ∎
  ... | inj₁ (m , es) | inj₂ (n , et) =
        trans (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ sumeq) (odd-2*+1 (m + n))))
              (cong₂ (λ u v -> u + v) (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ es) (even-2* m))))
                                      (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ et) (odd-2*+1 n)))))
    where
      open ≡-Reasoning
      open ℤS
      sumeq : s + t ≡ 2ℤ * (m + n) + + 1
      sumeq = begin
        s + t                          ≡⟨ cong₂ Int._+_ es et ⟩
        2ℤ * m + (2ℤ * n + + 1)        ≡⟨ solve 2 (λ x y -> con (+ 2) :* x :+ (con (+ 2) :* y :+ con (+ 1))
                                            := con (+ 2) :* (x :+ y) :+ con (+ 1)) refl m n ⟩
        2ℤ * (m + n) + + 1             ∎
  ... | inj₂ (m , es) | inj₁ (n , et) =
        trans (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ sumeq) (odd-2*+1 (m + n))))
              (cong₂ (λ u v -> u + v) (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ es) (odd-2*+1 m))))
                                      (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ et) (even-2* n)))))
    where
      open ≡-Reasoning
      open ℤS
      sumeq : s + t ≡ 2ℤ * (m + n) + + 1
      sumeq = begin
        s + t                          ≡⟨ cong₂ Int._+_ es et ⟩
        (2ℤ * m + + 1) + 2ℤ * n        ≡⟨ solve 2 (λ x y -> (con (+ 2) :* x :+ con (+ 1)) :+ con (+ 2) :* y
                                            := con (+ 2) :* (x :+ y) :+ con (+ 1)) refl m n ⟩
        2ℤ * (m + n) + + 1             ∎
  ... | inj₂ (m , es) | inj₂ (n , et) =
        trans (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ sumeq) (even-2* (m + n + + 1))))
              (cong₂ (λ u v -> u + v) (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ es) (odd-2*+1 m))))
                                      (sym (cong (λ z -> if z then Even else Odd) (trans (cong evenℤ et) (odd-2*+1 n)))))
    where
      open ≡-Reasoning
      open ℤS
      sumeq : s + t ≡ 2ℤ * (m + n + + 1)
      sumeq = begin
        s + t                                  ≡⟨ cong₂ Int._+_ es et ⟩
        (2ℤ * m + + 1) + (2ℤ * n + + 1)        ≡⟨ solve 2 (λ x y -> (con (+ 2) :* x :+ con (+ 1)) :+ (con (+ 2) :* y :+ con (+ 1))
                                                    := con (+ 2) :* (x :+ y :+ con (+ 1))) refl m n ⟩
        2ℤ * (m + n + + 1)                     ∎

-- Parity is additive.
parity-+ : ∀ (x y : ZComplex) -> parityℤ[i] (x + y) ≡ parityℤ[i] x + parityℤ[i] y
parity-+ (Cplx a b) (Cplx c d) =
  trans (cong (λ z -> if evenℤ z then Even else Odd) sumeq) (parity-+ℤ (a + b) (c + d))
  where
    open ℤS
    sumeq : (a + c) + (b + d) ≡ (a + b) + (c + d)
    sumeq = solve 4 (λ w x y z -> (w :+ y) :+ (x :+ z) := (w :+ x) :+ (y :+ z)) refl a b c d

-- ----------------------------------------------------------------------
-- * Lemma II.5: α is odd iff its norm ∥α∥² is an odd integer

lemma-II-5 : ∀ (x : ZComplex) -> parityℤ[i] x ≡ parity (normℤ[i] x)
lemma-II-5 (Cplx a b) with sq-parity a | sq-parity b
... | k , ea | l , eb = cong (λ z -> if z then Even else Odd) (sym (even-cong-2 (a * a + b * b) (a + b) (k + l) lemma))
  where
    open ≡-Reasoning
    open ℤS
    lemma : a * a + b * b ≡ (a + b) + 2ℤ * (k + l)
    lemma = begin
      a * a + b * b                            ≡⟨ cong₂ Int._+_ ea eb ⟩
      (a + 2ℤ * k) + (b + 2ℤ * l)              ≡⟨ solve 4 (λ w x y z -> (w :+ con (+ 2) :* y) :+ (x :+ con (+ 2) :* z)
                                                    := (w :+ x) :+ con (+ 2) :* (y :+ z)) refl a b k l ⟩
      (a + b) + 2ℤ * (k + l)                   ∎

lemma-II-5-odd : ∀ (x : ZComplex) -> parityℤ[i] x ≡ Odd -> evenℤ (normℤ[i] x) ≡ false
lemma-II-5-odd x p = if-odd _ (trans (sym (lemma-II-5 x)) p)

lemma-II-5-even : ∀ (x : ZComplex) -> parityℤ[i] x ≡ Even -> evenℤ (normℤ[i] x) ≡ true
lemma-II-5-even x p = if-even _ (trans (sym (lemma-II-5 x)) p)

-- ----------------------------------------------------------------------
-- * Congruences modulo an element of ℤ[i]

-- x ≡ y (mod m), i.e. ∃ k, x - y = k m. This is a record rather than
-- a Σ-type, so that the arguments x, y, m can be inferred (unifying
-- x - y with a meta is hopeless, since ℤ[i] is a record type).
infix 4 _≈_mod_
record _≈_mod_ (x y m : ZComplex) : Set where
  constructor mod-wit
  field
    witness : ZComplex
    witness-eq : x - y ≡ witness * m
open _≈_mod_ public

-- The formulation with an existential quantifier.
≈⇒∃ : ∀ {x y m} -> x ≈ y mod m -> ∃ λ k -> x - y ≡ k * m
≈⇒∃ (mod-wit k e) = k , e

∃⇒≈ : ∀ {x y m} -> (∃ λ k -> x - y ≡ k * m) -> x ≈ y mod m
∃⇒≈ (k , e) = mod-wit k e

≈-refl : ∀ {m} x -> x ≈ x mod m
≈-refl {m} x = mod-wit 0# (solve 2 (λ u v -> u :- u := con (+ 0) :* v) refl x m)
  where open GS

≈-reflexive : ∀ {m} {x y} -> x ≡ y -> x ≈ y mod m
≈-reflexive {m} {x} refl = ≈-refl x

-- Rewriting both sides of a congruence.
≈-resp : ∀ {x x' y y' m} -> x ≡ x' -> y ≡ y' -> x ≈ y mod m -> x' ≈ y' mod m
≈-resp refl refl p = p

≈-sym : ∀ {x y m} -> x ≈ y mod m -> y ≈ x mod m
≈-sym {x} {y} {m} (mod-wit k e) = mod-wit (- k) (begin
  y - x        ≡⟨ solve 2 (λ u v -> v :- u := :- (u :- v)) refl x y ⟩
  - (x - y)    ≡⟨ cong -_ e ⟩
  - (k * m)    ≡⟨ solve 2 (λ u v -> :- (u :* v) := (:- u) :* v) refl k m ⟩
  (- k) * m    ∎)
  where
    open ≡-Reasoning
    open GS

≈-trans : ∀ {x y z m} -> x ≈ y mod m -> y ≈ z mod m -> x ≈ z mod m
≈-trans {x} {y} {z} {m} (mod-wit k e) (mod-wit k' e') = mod-wit (k + k') (begin
  x - z                 ≡⟨ solve 3 (λ u v w -> u :- w := (u :- v) :+ (v :- w)) refl x y z ⟩
  (x - y) + (y - z)     ≡⟨ cong₂ _+_ e e' ⟩
  k * m + k' * m        ≡⟨ solve 3 (λ u v w -> u :* w :+ v :* w := (u :+ v) :* w) refl k k' m ⟩
  (k + k') * m          ∎)
  where
    open ≡-Reasoning
    open GS

≈-+ : ∀ {x y u v m} -> x ≈ y mod m -> u ≈ v mod m -> (x + u) ≈ (y + v) mod m
≈-+ {x} {y} {u} {v} {m} (mod-wit k e) (mod-wit k' e') = mod-wit (k + k') (begin
  (x + u) - (y + v)         ≡⟨ solve 4 (λ a b c d -> (a :+ c) :- (b :+ d) := (a :- b) :+ (c :- d)) refl x y u v ⟩
  (x - y) + (u - v)         ≡⟨ cong₂ _+_ e e' ⟩
  k * m + k' * m            ≡⟨ solve 3 (λ a b c -> a :* c :+ b :* c := (a :+ b) :* c) refl k k' m ⟩
  (k + k') * m              ∎)
  where
    open ≡-Reasoning
    open GS

≈-neg : ∀ {x y m} -> x ≈ y mod m -> (- x) ≈ (- y) mod m
≈-neg {x} {y} {m} (mod-wit k e) = mod-wit (- k) (begin
  (- x) - (- y)     ≡⟨ solve 2 (λ a b -> (:- a) :- (:- b) := :- (a :- b)) refl x y ⟩
  - (x - y)         ≡⟨ cong -_ e ⟩
  - (k * m)         ≡⟨ solve 2 (λ a b -> :- (a :* b) := (:- a) :* b) refl k m ⟩
  (- k) * m         ∎)
  where
    open ≡-Reasoning
    open GS

≈-* : ∀ {x y u v m} -> x ≈ y mod m -> u ≈ v mod m -> (x * u) ≈ (y * v) mod m
≈-* {x} {y} {u} {v} {m} (mod-wit k e) (mod-wit k' e') = mod-wit (k * u + y * k') (begin
  (x * u) - (y * v)                   ≡⟨ solve 4 (λ a b c d -> (a :* c) :- (b :* d) := (a :- b) :* c :+ b :* (c :- d)) refl x y u v ⟩
  (x - y) * u + y * (u - v)           ≡⟨ cong₂ (λ s t -> s * u + y * t) e e' ⟩
  (k * m) * u + y * (k' * m)          ≡⟨ solve 5 (λ a b c d f -> (a :* b) :* c :+ d :* (f :* b)
                                           := (a :* c :+ d :* f) :* b) refl k m u y k' ⟩
  (k * u + y * k') * m                ∎)
  where
    open ≡-Reasoning
    open GS

≈-*ˡ : ∀ {x y m} z -> x ≈ y mod m -> (z * x) ≈ (z * y) mod m
≈-*ˡ {x} {y} {m} z p = ≈-* {z} {z} {x} {y} {m} (≈-refl z) p

≈-*ʳ : ∀ {x y m} z -> x ≈ y mod m -> (x * z) ≈ (y * z) mod m
≈-*ʳ {x} {y} {m} z p = ≈-* {x} {y} {z} {z} {m} p (≈-refl z)

-- Weakening the modulus.
≈-factor : ∀ {x y m n} -> x ≈ y mod (m * n) -> x ≈ y mod m
≈-factor {x} {y} {m} {n} (mod-wit k e) = mod-wit (k * n) (trans e (solve 3 (λ a b c -> a :* (b :* c) := (a :* c) :* b) refl k m n))
  where open GS

-- ----------------------------------------------------------------------
-- * Lemma II.6 (cancellation of γ)

lemma-II-6 : ∀ {α β : ZComplex} {n} -> (α * γ) ≈ (β * γ) mod (γ ↑ suc n) -> α ≈ β mod (γ ↑ n)
lemma-II-6 {α} {β} {n} (mod-wit k e) = mod-wit k (GP.*-alc-𝔾 γ (α - β) (k * (γ ↑ n)) γ≢0 (begin
  γ * (α - β)            ≡⟨ solve 3 (λ g a b -> g :* (a :- b) := a :* g :- b :* g) refl γ α β ⟩
  α * γ - β * γ          ≡⟨ e ⟩
  k * (γ * (γ ↑ n))      ≡⟨ solve 3 (λ a g p -> a :* (g :* p) := g :* (a :* p)) refl k γ (γ ↑ n) ⟩
  γ * (k * (γ ↑ n))      ∎))
  where
    open ≡-Reasoning
    open GS
