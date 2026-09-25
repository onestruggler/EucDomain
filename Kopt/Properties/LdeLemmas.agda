-- Parity is multiplicative, Lemmas II.7 and II.8 of Bian & Feng, and
-- the behaviour of the least denominator exponent under sums, units
-- and division by γ (needed for Remark II.10). See
-- Kopt.Properties.Algebra for the rest of Section II.
--
-- Note: the ring solver is never used for 𝔻[i]; see the comment on
-- CRLemmas in Kopt.Properties.Lde.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.LdeLemmas where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; T ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as IntP
import Data.Integer.Solver as IntSolver
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
open import Kopt.Properties.Gamma
open import Kopt.Properties.DyadicTools
open import Kopt.Properties.Residue
open import Kopt.Properties.Lde

private
  module ℤS = IntSolver.+-*-Solver
  module DR = IsCommutativeRing isCommutativeRing-DComplex
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex

  if-cong : ∀ {z w : Bool} -> z ≡ w -> (if z then Even else Odd) ≡ (if w then Even else Odd)
  if-cong e = cong (λ b -> if b then Even else Odd) e

  pos⇒suc′ : ∀ (n j : ℕ) -> j Nat.< n -> ∃ λ p -> n ≡ suc p
  pos⇒suc′ (suc p) j _ = p , refl

-- ----------------------------------------------------------------------
-- * Parity is multiplicative

private
  parity-*ℤ : ∀ (s t : ℤ) -> parity (s * t) ≡ parity s * parity t
  parity-*ℤ s t with ℤ-parity s | ℤ-parity t
  ... | inj₁ (u , es) | inj₁ (v , et) =
        trans (if-cong (trans (cong evenℤ eq) (even-2* ((+ 2) * u * v))))
              (sym (cong₂ (λ p q -> p * q) (if-cong (trans (cong evenℤ es) (even-2* u)))
                                           (if-cong (trans (cong evenℤ et) (even-2* v)))))
    where
      open ℤS
      eq : s * t ≡ (+ 2) * ((+ 2) * u * v)
      eq = trans (cong₂ Int._*_ es et)
                 (solve 2 (λ x y -> (con (+ 2) :* x) :* (con (+ 2) :* y) := con (+ 2) :* (con (+ 2) :* x :* y))
                        refl u v)
  ... | inj₁ (u , es) | inj₂ (v , et) =
        trans (if-cong (trans (cong evenℤ eq) (even-2* (u * ((+ 2) * v + + 1)))))
              (sym (cong₂ (λ p q -> p * q) (if-cong (trans (cong evenℤ es) (even-2* u)))
                                           (if-cong (trans (cong evenℤ et) (odd-2*+1 v)))))
    where
      open ℤS
      eq : s * t ≡ (+ 2) * (u * ((+ 2) * v + + 1))
      eq = trans (cong₂ Int._*_ es et)
                 (solve 2 (λ x y -> (con (+ 2) :* x) :* (con (+ 2) :* y :+ con (+ 1))
                            := con (+ 2) :* (x :* (con (+ 2) :* y :+ con (+ 1)))) refl u v)
  ... | inj₂ (u , es) | inj₁ (v , et) =
        trans (if-cong (trans (cong evenℤ eq) (even-2* (((+ 2) * u + + 1) * v))))
              (sym (cong₂ (λ p q -> p * q) (if-cong (trans (cong evenℤ es) (odd-2*+1 u)))
                                           (if-cong (trans (cong evenℤ et) (even-2* v)))))
    where
      open ℤS
      eq : s * t ≡ (+ 2) * (((+ 2) * u + + 1) * v)
      eq = trans (cong₂ Int._*_ es et)
                 (solve 2 (λ x y -> (con (+ 2) :* x :+ con (+ 1)) :* (con (+ 2) :* y)
                            := con (+ 2) :* ((con (+ 2) :* x :+ con (+ 1)) :* y)) refl u v)
  ... | inj₂ (u , es) | inj₂ (v , et) =
        trans (if-cong (trans (cong evenℤ eq) (odd-2*+1 ((+ 2) * u * v + u + v))))
              (sym (cong₂ (λ p q -> p * q) (if-cong (trans (cong evenℤ es) (odd-2*+1 u)))
                                           (if-cong (trans (cong evenℤ et) (odd-2*+1 v)))))
    where
      open ℤS
      eq : s * t ≡ (+ 2) * ((+ 2) * u * v + u + v) + + 1
      eq = trans (cong₂ Int._*_ es et)
                 (solve 2 (λ x y -> (con (+ 2) :* x :+ con (+ 1)) :* (con (+ 2) :* y :+ con (+ 1))
                            := con (+ 2) :* (con (+ 2) :* x :* y :+ x :+ y) :+ con (+ 1)) refl u v)

-- Parity is a ring homomorphism ℤ[i] → ℤ₂ (using Lemma II.5 and the
-- multiplicativity of the norm).
parity-* : ∀ (x y : ZComplex) -> parityℤ[i] (x * y) ≡ parityℤ[i] x * parityℤ[i] y
parity-* x y = begin
  parityℤ[i] (x * y)                         ≡⟨ lemma-II-5 (x * y) ⟩
  parity (normℤ[i] (x * y))                  ≡⟨ cong parity (norm-*-ZComplex x y) ⟩
  parity (normℤ[i] x * normℤ[i] y)           ≡⟨ parity-*ℤ (normℤ[i] x) (normℤ[i] y) ⟩
  parity (normℤ[i] x) * parity (normℤ[i] y)  ≡⟨ sym (cong₂ (λ p q -> p * q) (lemma-II-5 x) (lemma-II-5 y)) ⟩
  parityℤ[i] x * parityℤ[i] y                ∎
  where open ≡-Reasoning

parity-minus : ∀ (x y : ZComplex) -> parityℤ[i] (x - y) ≡ parityℤ[i] x + parityℤ[i] y
parity-minus x y = trans (parity-+ x (- y)) (cong (λ z -> parityℤ[i] x + z) (parity-neg y))

-- The first digit of a residue is the parity.
parity-of-ρ : ∀ n X b (bs : Residue n) -> ρ (suc n) X ≡ b ∷ bs -> parityℤ[i] X ≡ b
parity-of-ρ n X b bs e = trans (sym (ρ-head n X)) (cong Vec.head e)

-- ----------------------------------------------------------------------
-- * 1/γ in 𝔻[i]

invγ : DComplex
invγ = 1/γ

γ-invγ : (γ {DComplex}) * invγ ≡ 1#
γ-invγ = refl

invγ-γ : invγ * (γ {DComplex}) ≡ 1#
invγ-γ = refl

-- ----------------------------------------------------------------------
-- * Lemma II.7: for k = lde t > 0, γᵏt is odd

-- If γᵏ⁺¹t is an even Gaussian integer, then γᵏt is a Gaussian integer.
DenomExpγ-pred : ∀ (t : DComplex) (k : ℕ) (y : ZComplex) -> t * (γ ↑ suc k) ≡ from-whole (γ * y) -> t * (γ ↑ k) ≡ from-whole y
DenomExpγ-pred t k y h = begin
  t * (γ ↑ k)                            ≡⟨ sym (DR.*-identityˡ (t * (γ ↑ k))) ⟩
  1# * (t * (γ ↑ k))                     ≡⟨ cong (λ z -> z * (t * (γ ↑ k))) (sym invγ-γ) ⟩
  (invγ * γ) * (t * (γ ↑ k))             ≡⟨ trans (DR.*-assoc invγ γ (t * (γ ↑ k)))
                                              (cong (λ z -> invγ * z) (DL.swapˡ γ t (γ ↑ k))) ⟩
  invγ * (t * (γ * (γ ↑ k)))             ≡⟨ cong (λ z -> invγ * z) h ⟩
  invγ * from-whole (γ * y)              ≡⟨ cong (λ z -> invγ * z) (from-whole-* γ y) ⟩
  invγ * (from-whole γ * from-whole y)   ≡⟨ cong (λ z -> invγ * (z * from-whole y)) from-whole-γ ⟩
  invγ * (γ * from-whole y)              ≡⟨ sym (DR.*-assoc invγ γ (from-whole y)) ⟩
  (invγ * γ) * from-whole y              ≡⟨ cong (λ z -> z * from-whole y) invγ-γ ⟩
  1# * from-whole y                      ≡⟨ DR.*-identityˡ (from-whole y) ⟩
  from-whole y                           ∎
  where open ≡-Reasoning

-- Lemma II.7.
lemma-II-7 : ∀ (t : DComplex) (k : ℕ) (z : ZComplex) -> lde t ≡ suc k -> t * (γ ↑ suc k) ≡ from-whole z -> parityℤ[i] z ≡ Odd
lemma-II-7 t k z e h with parityℤ[i] z in pz
... | Odd = refl
... | Even = ⊥-elim (NatP.n≮n k (subst (λ n -> n Nat.≤ k) e small))
  where
    y : ZComplex
    y = z /γ
    lower : DenomExpγ k t
    lower = denom-exp y (DenomExpγ-pred t k y (trans h (cong (λ w -> DComplex ∋ from-whole w) (sym (γ-div-even z pz)))))
    small : lde t Nat.≤ k
    small = lde-least t k lower

-- ----------------------------------------------------------------------
-- * Lemma II.8: subadditivity of lde

-- γ^(l+l')(xy) is integral whenever γˡx and γ^l'y are.
DenomExpγ-* : ∀ (x y : DComplex) (j k : ℕ) -> DenomExpγ j x -> DenomExpγ k y -> DenomExpγ (j Nat.+ k) (x * y)
DenomExpγ-* x y j k (denom-exp zx hx) (denom-exp zy hy) = denom-exp (zx * zy) (begin
  (x * y) * (γ ↑ (j Nat.+ k))                  ≡⟨ cong (λ z -> (x * y) * z) (↑-+ isCommutativeRing-DComplex γ j k) ⟩
  (x * y) * ((γ ↑ j) * (γ ↑ k))                ≡⟨ DL.interchange x y (γ ↑ j) (γ ↑ k) ⟩
  (x * (γ ↑ j)) * (y * (γ ↑ k))                ≡⟨ cong₂ (λ u v -> u * v) hx hy ⟩
  from-whole zx * from-whole zy                ≡⟨ sym (from-whole-* zx zy) ⟩
  from-whole (zx * zy)                         ∎)
  where open ≡-Reasoning

-- Lemma II.8 (subadditivity).
lemma-II-8 : ∀ (x y : DComplex) -> lde (x * y) Nat.≤ lde x Nat.+ lde y
lemma-II-8 x y = lde-least (x * y) (lde x Nat.+ lde y)
  (DenomExpγ-* x y (lde x) (lde y) (lde-denom-exp x) (lde-denom-exp y))

-- Lemma II.8 (equality for odd arguments). By Lemma II.7 the
-- hypotheses hold automatically when lde x and lde y are positive.
lemma-II-8-odd : ∀ (x y : DComplex) (zx zy : ZComplex) ->
                 x * (γ ↑ lde x) ≡ from-whole zx -> y * (γ ↑ lde y) ≡ from-whole zy ->
                 parityℤ[i] zx ≡ Odd -> parityℤ[i] zy ≡ Odd ->
                 lde (x * y) ≡ lde x Nat.+ lde y
lemma-II-8-odd x y zx zy hx hy ox oy = NatP.≤-antisym (lemma-II-8 x y) ≥-part
  where
    open ≡-Reasoning
    prod : (x * y) * (γ ↑ (lde x Nat.+ lde y)) ≡ from-whole (zx * zy)
    prod = whole-eq (DenomExpγ-* x y (lde x) (lde y) (denom-exp zx hx) (denom-exp zy hy))
    odd-prod : parityℤ[i] (zx * zy) ≡ Odd
    odd-prod = trans (parity-* zx zy) (cong₂ (λ p q -> p * q) ox oy)
    bad : Odd ≡ Even -> ⊥
    bad ()
    contra : ∀ j -> DenomExpγ j (x * y) -> j Nat.< (lde x Nat.+ lde y) -> ⊥
    contra j hj j< = bad (trans (sym odd-prod) even-prod)
      where
        p : ℕ
        p = proj₁ (pos⇒suc′ (lde x Nat.+ lde y) j j<)
        pe : lde x Nat.+ lde y ≡ suc p
        pe = proj₂ (pos⇒suc′ (lde x Nat.+ lde y) j j<)
        lower : DenomExpγ p (x * y)
        lower = DenomExpγ-≤ (NatP.≤-pred (subst (λ n -> j Nat.< n) pe j<)) hj
        step : from-whole (zx * zy) ≡ from-whole (whole lower * γ)
        step = begin
          from-whole (zx * zy)                     ≡⟨ sym prod ⟩
          (x * y) * (γ ↑ (lde x Nat.+ lde y))      ≡⟨ cong (λ n -> (x * y) * (γ ↑ n)) pe ⟩
          (x * y) * (γ * (γ ↑ p))                  ≡⟨ DL.assoc-swap (x * y) γ (γ ↑ p) ⟩
          ((x * y) * (γ ↑ p)) * γ                  ≡⟨ cong (λ z -> z * γ) (whole-eq lower) ⟩
          from-whole (whole lower) * γ             ≡⟨ cong (λ z -> from-whole (whole lower) * z) (sym from-whole-γ) ⟩
          from-whole (whole lower) * from-whole γ  ≡⟨ sym (from-whole-* (whole lower) γ) ⟩
          from-whole (whole lower * γ)             ∎
        even-prod : parityℤ[i] (zx * zy) ≡ Even
        even-prod = divides⇒even (zx * zy) (whole lower)
          (trans (from-whole-injective step) (ZR.*-comm (whole lower) γ))
    ≥-part : lde x Nat.+ lde y Nat.≤ lde (x * y)
    ≥-part = NatP.≮⇒≥ (λ p -> contra (lde (x * y)) (lde-denom-exp (x * y)) p)

-- ----------------------------------------------------------------------
-- * The lde of sums, of units and of x/γ

max-≤ˡ : ∀ (p q : ℕ) -> p Nat.≤ max p q
max-≤ˡ p q with p Nat.≤ᵇ q in le
... | true = NatP.≤ᵇ⇒≤ p q (subst T (sym le) tt)
... | false = NatP.≤-refl

max-≤ʳ : ∀ (p q : ℕ) -> q Nat.≤ max p q
max-≤ʳ p q with p Nat.≤ᵇ q in le
... | true = NatP.≤-refl
... | false = NatP.≰⇒≥ (λ h -> subst T le (NatP.≤⇒≤ᵇ h))

max-lub : ∀ {p q r : ℕ} -> p Nat.≤ r -> q Nat.≤ r -> max p q Nat.≤ r
max-lub {p} {q} hp hq with p Nat.≤ᵇ q
... | true = hq
... | false = hp

-- lde(x+y) ≤ max (lde x) (lde y).
lde-+ : ∀ (x y : DComplex) -> lde (x + y) Nat.≤ max (lde x) (lde y)
lde-+ x y = lde-least (x + y) (max (lde x) (lde y)) (denom-exp (zx + zy) (begin
  (x + y) * (γ ↑ M)                    ≡⟨ DR.distribʳ (γ ↑ M) x y ⟩
  (x * (γ ↑ M)) + (y * (γ ↑ M))        ≡⟨ cong₂ (λ u v -> u + v) hx hy ⟩
  from-whole zx + from-whole zy        ≡⟨ sym (from-whole-+ zx zy) ⟩
  from-whole (zx + zy)                 ∎))
  where
    open ≡-Reasoning
    M : ℕ
    M = max (lde x) (lde y)
    dx : DenomExpγ M x
    dx = DenomExpγ-≤ (max-≤ˡ (lde x) (lde y)) (lde-denom-exp x)
    dy : DenomExpγ M y
    dy = DenomExpγ-≤ (max-≤ʳ (lde x) (lde y)) (lde-denom-exp y)
    zx : ZComplex
    zx = whole dx
    zy : ZComplex
    zy = whole dy
    hx : x * (γ ↑ M) ≡ from-whole zx
    hx = whole-eq dx
    hy : y * (γ ↑ M) ≡ from-whole zy
    hy = whole-eq dy

-- Multiplying by a Gaussian integer does not increase the lde.
lde-whole-≤ : ∀ (u : ZComplex) (x : DComplex) -> lde (from-whole u * x) Nat.≤ lde x
lde-whole-≤ u x = lde-least (from-whole u * x) (lde x) (denom-exp (u * whole dx) (begin
  (from-whole u * x) * (γ ↑ lde x)         ≡⟨ DR.*-assoc (from-whole u) x (γ ↑ lde x) ⟩
  from-whole u * (x * (γ ↑ lde x))         ≡⟨ cong (λ z -> from-whole u * z) (whole-eq dx) ⟩
  from-whole u * from-whole (whole dx)     ≡⟨ sym (from-whole-* u (whole dx)) ⟩
  from-whole (u * whole dx)                ∎))
  where
    open ≡-Reasoning
    dx : DenomExpγ (lde x) x
    dx = lde-denom-exp x

-- Multiplication by i does not change the lde.
lde-i : ∀ (x : DComplex) -> lde (i * x) ≡ lde x
lde-i x = NatP.≤-antisym le ge
  where
    le : lde (i * x) Nat.≤ lde x
    le = lde-whole-≤ i x
    x≡ : (- i) * (i * x) ≡ x
    x≡ = trans (sym (DR.*-assoc (- i) i x)) (DR.*-identityˡ x)
    ge : lde x Nat.≤ lde (i * x)
    ge = subst (λ z -> lde z Nat.≤ lde (i * x)) x≡ (lde-whole-≤ (- i) (i * x))

-- Dividing by γ increases the lde by at most one.
lde-invγ : ∀ (x : DComplex) -> lde (x * invγ) Nat.≤ suc (lde x)
lde-invγ x = lde-least (x * invγ) (suc (lde x)) (denom-exp (whole dx) (begin
  (x * invγ) * (γ * (γ ↑ lde x))    ≡⟨ DL.interchange2 x invγ γ (γ ↑ lde x) ⟩
  (x * (γ ↑ lde x)) * (invγ * γ)    ≡⟨ cong (λ z -> (x * (γ ↑ lde x)) * z) invγ-γ ⟩
  (x * (γ ↑ lde x)) * 1#            ≡⟨ DR.*-identityʳ (x * (γ ↑ lde x)) ⟩
  x * (γ ↑ lde x)                   ≡⟨ whole-eq dx ⟩
  from-whole (whole dx)             ∎))
  where
    open ≡-Reasoning
    dx : DenomExpγ (lde x) x
    dx = lde-denom-exp x

-- ----------------------------------------------------------------------
