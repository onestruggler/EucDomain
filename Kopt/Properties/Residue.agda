-- Section II B of Bian & Feng: the residues ρₙ : ℤ[i] → ℤ[i]/(γⁿ),
-- represented by binary strings b₀b₁...bₙ₋₁.
--
-- The main results are: ρₙ(x) represents the class of x modulo γⁿ
-- (ρ-sound), distinct binary strings represent distinct classes
-- (value-injective), hence ρₙ(x) is the unique string congruent to x
-- (ρ-unique); ρₙ is stable under increasing n (ρ-trunc); the shift
-- equations (ρ-RS, ρ-LS); and the residue arithmetic modulo γ² and
-- γ³ of Section II B.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.Residue where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer.Base as Int using (ℤ ; +_)
import Data.Integer.Properties as IntP
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
open import Kopt.Properties.Gamma
import GauInt.Properties as GP

private
  module GS = ZSolver commutativeRing-ZComplex
  module CR = IsCommutativeRing isCommutativeRing-ZComplex
  module ADJ = IsInvolutiveRingEndo adj-ZComplex

  odd≢even : Odd ≡ Even -> ⊥
  odd≢even ()

  even≢odd : Even ≡ Odd -> ⊥
  even≢odd ()

-- ----------------------------------------------------------------------
-- * The defining equations of ρ

-- ρ is defined by a case distinction on the parity of its argument;
-- these two lemmas expose the two cases.
ρ-even-step : ∀ n x -> parityℤ[i] x ≡ Even -> ρ (suc n) x ≡ Even ∷ ρ n (x /γ)
ρ-even-step n x p with parityℤ[i] x
... | Even = refl
... | Odd = ⊥-elim (odd≢even p)

ρ-odd-step : ∀ n x -> parityℤ[i] x ≡ Odd -> ρ (suc n) x ≡ Odd ∷ ρ n ((x - 1#) /γ)
ρ-odd-step n x p with parityℤ[i] x
... | Odd = refl
... | Even = ⊥-elim (even≢odd p)

-- The first digit of ρ is the parity.
ρ-head : ∀ n x -> Vec.head (ρ (suc n) x) ≡ parityℤ[i] x
ρ-head n x with parityℤ[i] x
... | Even = refl
... | Odd = refl

-- ----------------------------------------------------------------------
-- * Values of residues

-- The digit b as an element of ℤ[i].
digit : Z2 -> ZComplex
digit Even = 0#
digit Odd = 1#

value-cons : ∀ {n} b (bs : Residue n) -> value-of-residue (b ∷ bs) ≡ digit b + value-of-residue bs * γ
value-cons Even bs = sym (CR.+-identityˡ _)
value-cons Odd bs = refl

-- Multiples of γ are even.
parity-*γ : ∀ (x : ZComplex) -> parityℤ[i] (x * γ) ≡ Even
parity-*γ x = trans (cong parityℤ[i] (CR.*-comm x γ)) (γ*-even x)

-- The parity of a value is its first digit.
parity-value : ∀ {n} b (bs : Residue n) -> parityℤ[i] (value-of-residue (b ∷ bs)) ≡ b
parity-value Even bs = parity-*γ (value-of-residue bs)
parity-value Odd bs = trans (parity-+ 1# (value-of-residue bs * γ))
                            (cong (λ z -> Odd + z) (parity-*γ (value-of-residue bs)))

-- ----------------------------------------------------------------------
-- * ρₙ(x) is the residue of x modulo γⁿ

-- One step: from a congruence modulo γⁿ to one modulo γⁿ⁺¹.
≈-γ-step : ∀ {y v n} -> y ≈ v mod (γ ↑ n) -> (γ * y) ≈ (v * γ) mod (γ ↑ suc n)
≈-γ-step {y} {v} {n} (mod-wit k e) = mod-wit k (begin
  γ * y - v * γ         ≡⟨ solve 3 (λ g a b -> g :* a :- b :* g := g :* (a :- b)) refl γ y v ⟩
  γ * (y - v)           ≡⟨ cong (γ *_) e ⟩
  γ * (k * (γ ↑ n))     ≡⟨ solve 3 (λ g a p -> g :* (a :* p) := a :* (g :* p)) refl γ k (γ ↑ n) ⟩
  k * (γ * (γ ↑ n))     ∎)
  where
    open ≡-Reasoning
    open GS

-- Correctness of ρ: x ≡ value-of-residue (ρ n x) (mod γⁿ).
ρ-sound : ∀ n x -> x ≈ value-of-residue (ρ n x) mod (γ ↑ n)
ρ-sound zero x = mod-wit x (GS.solve 1 (λ u -> u :- con (+ 0) := u :* con (+ 1)) refl x)
  where open GS
ρ-sound (suc n) x with parityℤ[i] x in eq
... | Even = subst (λ w -> w ≈ (value-of-residue (ρ n (x /γ)) * γ) mod (γ ↑ suc n))
                   (γ-div-even x eq) (≈-γ-step {n = n} (ρ-sound n (x /γ)))
... | Odd = ≈-resp e1 e2 (≈-+ base (≈-refl 1#))
  where
    open GS
    y : ZComplex
    y = (x - 1#) /γ
    v : ZComplex
    v = value-of-residue (ρ n y)
    base : (x - 1#) ≈ (v * γ) mod (γ ↑ suc n)
    base = subst (λ w -> w ≈ (v * γ) mod (γ ↑ suc n)) (odd-div x eq) (≈-γ-step {n = n} (ρ-sound n y))
    e1 : (x - 1#) + 1# ≡ x
    e1 = solve 1 (λ u -> (u :- con (+ 1)) :+ con (+ 1) := u) refl x
    e2 : v * γ + 1# ≡ 1# + v * γ
    e2 = solve 2 (λ u g -> u :* g :+ con (+ 1) := con (+ 1) :+ u :* g) refl v γ

-- ----------------------------------------------------------------------
-- * Distinct binary strings are distinct residue classes

private
  Z2-+-cancel : ∀ (a b : Z2) -> a + b ≡ Even -> a ≡ b
  Z2-+-cancel Even Even _ = refl
  Z2-+-cancel Even Odd ()
  Z2-+-cancel Odd Even ()
  Z2-+-cancel Odd Odd _ = refl

parity-neg : ∀ (x : ZComplex) -> parityℤ[i] (- x) ≡ parityℤ[i] x
parity-neg x = Z2-+-cancel _ _ (trans (sym (parity-+ (- x) x)) (cong parityℤ[i] (CR.-‿inverseˡ x)))

-- Congruent elements have the same parity.
mod-γ⇒parity : ∀ {x y} -> x ≈ y mod γ -> parityℤ[i] x ≡ parityℤ[i] y
mod-γ⇒parity {x} {y} (mod-wit k e) = Z2-+-cancel _ _ (begin
  parityℤ[i] x + parityℤ[i] y     ≡⟨ cong (λ z -> parityℤ[i] x + z) (sym (parity-neg y)) ⟩
  parityℤ[i] x + parityℤ[i] (- y) ≡⟨ sym (parity-+ x (- y)) ⟩
  parityℤ[i] (x - y)              ≡⟨ cong parityℤ[i] e ⟩
  parityℤ[i] (k * γ)              ≡⟨ parity-*γ k ⟩
  Even                            ∎)
  where open ≡-Reasoning

-- A congruence modulo γⁿ⁺¹ is one modulo γ.
≈-γ-weaken : ∀ {x y n} -> x ≈ y mod (γ ↑ suc n) -> x ≈ y mod γ
≈-γ-weaken {x} {y} {n} p = ≈-factor {x} {y} {γ} {γ ↑ n} p

-- Injectivity of value-of-residue on residues (Section II B).
value-injective : ∀ {n} (bs bs' : Residue n) ->
                  value-of-residue bs ≈ value-of-residue bs' mod (γ ↑ n) -> bs ≡ bs'
value-injective [] [] p = refl
value-injective {suc n} (b ∷ bs) (b' ∷ bs') p = cong₂ _∷_ head-eq (value-injective bs bs' tail-≈)
  where
    open ≡-Reasoning
    open GS
    head-eq : b ≡ b'
    head-eq = trans (sym (parity-value b bs))
                    (trans (mod-γ⇒parity (≈-γ-weaken {n = n} p)) (parity-value b' bs'))
    shifted : (value-of-residue bs * γ) ≈ (value-of-residue bs' * γ) mod (γ ↑ suc n)
    shifted = ≈-resp e1 e2 (≈-+ p (≈-refl (- digit b)))
      where
        e1 : value-of-residue (b ∷ bs) + (- digit b) ≡ value-of-residue bs * γ
        e1 = trans (cong (_+ (- digit b)) (value-cons b bs))
                   (solve 2 (λ d u -> (d :+ u) :- d := u) refl (digit b) (value-of-residue bs * γ))
        e2 : value-of-residue (b' ∷ bs') + (- digit b) ≡ value-of-residue bs' * γ
        e2 = trans (cong (_+ (- digit b)) (trans (value-cons b' bs') (cong (λ d -> digit d + value-of-residue bs' * γ) (sym head-eq))))
                   (solve 2 (λ d u -> (d :+ u) :- d := u) refl (digit b) (value-of-residue bs' * γ))
    tail-≈ : value-of-residue bs ≈ value-of-residue bs' mod (γ ↑ n)
    tail-≈ = lemma-II-6 {value-of-residue bs} {value-of-residue bs'} {n} shifted

-- ----------------------------------------------------------------------
-- * ρ is the unique representative

-- Congruent elements have the same residue.
ρ-mod : ∀ n {x y} -> x ≈ y mod (γ ↑ n) -> ρ n x ≡ ρ n y
ρ-mod n {x} {y} p = value-injective (ρ n x) (ρ n y)
  (≈-trans (≈-sym (ρ-sound n x)) (≈-trans p (ρ-sound n y)))

-- ρₙ is a retraction of value-of-residue.
ρ-value : ∀ {n} (bs : Residue n) -> ρ n (value-of-residue bs) ≡ bs
ρ-value {n} bs = value-injective (ρ n (value-of-residue bs)) bs (≈-sym (ρ-sound n (value-of-residue bs)))

ρ-unique : ∀ n x (bs : Residue n) -> x ≈ value-of-residue bs mod (γ ↑ n) -> ρ n x ≡ bs
ρ-unique n x bs p = trans (ρ-mod n p) (ρ-value bs)

-- Conversely, elements with the same residue are congruent.
ρ-complete : ∀ n {x y} -> ρ n x ≡ ρ n y -> x ≈ y mod (γ ↑ n)
ρ-complete n {x} {y} e =
  ≈-trans (ρ-sound n x) (≈-trans (≈-reflexive (cong value-of-residue e)) (≈-sym (ρ-sound n y)))

-- ----------------------------------------------------------------------
-- * Stability under increasing n

-- The first n digits of a residue of length n+1.
trunc : ∀ {n} -> Residue (suc n) -> Residue n
trunc {zero} (b ∷ []) = []
trunc {suc n} (b ∷ bs) = b ∷ trunc bs

private
  trunc-1 : ∀ (bs : Residue 1) -> trunc bs ≡ []
  trunc-1 (b ∷ []) = refl

-- ρₙ is stable under increasing n: the first n digits of ρₙ₊₁(x) are ρₙ(x).
ρ-trunc : ∀ n x -> trunc (ρ (suc n) x) ≡ ρ n x
ρ-trunc zero x = trunc-1 (ρ 1 x)
ρ-trunc (suc n) x with parityℤ[i] x
... | Even = cong (Even ∷_) (ρ-trunc n (x /γ))
... | Odd = cong (Odd ∷_) (ρ-trunc n ((x - 1#) /γ))

-- ----------------------------------------------------------------------
-- * The shifts of Lemma II.9

-- Multiplying by γ shifts the digits to the right.
ρ-RS : ∀ n x -> ρ (suc n) (γ * x) ≡ RS (ρ n x)
ρ-RS n x = trans (ρ-even-step n (γ * x) (γ*-even x)) (cong (Even ∷_) (cong (ρ n) div-γ))
  where
    div-γ : (γ * x) /γ ≡ x
    div-γ = GP.*-alc-𝔾 γ ((γ * x) /γ) x γ≢0 (γ-div-even (γ * x) (γ*-even x))

-- Dividing an even number by γ shifts the digits to the left.
ρ-LS : ∀ n x -> parityℤ[i] x ≡ Even -> ρ n (x /γ) ≡ LS (ρ (suc n) x)
ρ-LS n x p = sym (cong LS (ρ-even-step n x p))

-- ----------------------------------------------------------------------
-- * Conjugation

adj-minus : ∀ (x y : ZComplex) -> (x - y) † ≡ x † - y †
adj-minus (Cplx a b) (Cplx c d) = cong (Cplx (a + (Int.- c))) (IntP.neg-distrib-+ b (Int.- d))

-- (γⁿ)† = (-i)ⁿγⁿ, since γ† = -iγ.
adj-γ↑ : ∀ n -> ((γ {ZComplex}) ↑ n) † ≡ ((- i) ↑ n) * (γ ↑ n)
adj-γ↑ zero = refl
adj-γ↑ (suc n) = begin
  (γ * (γ ↑ n)) †                        ≡⟨ ADJ.f-* γ (γ ↑ n) ⟩
  (γ †) * ((γ ↑ n) †)                    ≡⟨ cong (λ z -> (γ †) * z) (adj-γ↑ n) ⟩
  ((- i) * γ) * (((- i) ↑ n) * (γ ↑ n))  ≡⟨ solve 4 (λ u g p q -> (u :* g) :* (p :* q) := (u :* p) :* (g :* q))
                                              refl (- i) γ ((- i) ↑ n) (γ ↑ n) ⟩
  ((- i) * ((- i) ↑ n)) * (γ * (γ ↑ n))  ∎
  where
    open ≡-Reasoning
    open GS

-- Congruences modulo γⁿ are preserved by conjugation.
≈-adj : ∀ {x y n} -> x ≈ y mod (γ ↑ n) -> (x †) ≈ (y †) mod (γ ↑ n)
≈-adj {x} {y} {n} (mod-wit k e) = mod-wit ((k †) * ((- i) ↑ n)) (begin
  x † - y †                        ≡⟨ sym (adj-minus x y) ⟩
  (x - y) †                        ≡⟨ cong (λ z -> z †) e ⟩
  (k * (γ ↑ n)) †                  ≡⟨ ADJ.f-* k (γ ↑ n) ⟩
  (k †) * ((γ ↑ n) †)              ≡⟨ cong (λ z -> (k †) * z) (adj-γ↑ n) ⟩
  (k †) * (((- i) ↑ n) * (γ ↑ n))  ≡⟨ solve 3 (λ a u p -> a :* (u :* p) := (a :* u) :* p)
                                        refl (k †) ((- i) ↑ n) (γ ↑ n) ⟩
  ((k †) * ((- i) ↑ n)) * (γ ↑ n)  ∎)
  where
    open ≡-Reasoning
    open GS

-- ----------------------------------------------------------------------
-- * The residue arithmetic of Section II B

-- Modulo γ², addition is bitwise xor (and every element is its own
-- additive inverse).
add₂ : Residue 2 -> Residue 2 -> Residue 2
add₂ (a ∷ b ∷ []) (a' ∷ b' ∷ []) = (a + a') ∷ (b + b') ∷ []

-- (b₀+b₁γ)(b'₀+b'₁γ) = b₀b'₀ + (b₀b'₁+b₁b'₀)γ (mod γ²). In particular,
-- multiplication by 01 = γ is a right shift, and 11·b₀b₁ = b₀(b₁⊕b₀).
mul₂ : Residue 2 -> Residue 2 -> Residue 2
mul₂ (a ∷ b ∷ []) (a' ∷ b' ∷ []) = (a * a') ∷ (a * b' + b * a') ∷ []

-- Modulo γ³ there is a carry b₀b'₀ into the last digit, since 2 ≡ γ².
add₃ : Residue 3 -> Residue 3 -> Residue 3
add₃ (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ []) = (a + a') ∷ (b + b') ∷ (c + c' + a * a') ∷ []

-- The truncated product of the polynomials in γ. In particular,
-- multiplication by 010 / 001 is a right shift by 1 / 2.
mul₃ : Residue 3 -> Residue 3 -> Residue 3
mul₃ (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ []) = (a * a') ∷ (a * b' + b * a') ∷ (a * c' + b * b' + c * a') ∷ []

-- -(b₀b₁b₂) = b₀b₁(b₂⊕b₀).
neg₃ : Residue 3 -> Residue 3
neg₃ (a ∷ b ∷ c ∷ []) = a ∷ b ∷ (c + a) ∷ []

-- ρ₃(x†) = ab(c⊕b) if ρ₃(x) = abc.
conj₃ : Residue 3 -> Residue 3
conj₃ (a ∷ b ∷ c ∷ []) = a ∷ b ∷ (c + b) ∷ []

-- The finite tables: the rules hold for the values of residues.
private
  tbl-add₂ : ∀ (u v : Residue 2) -> ρ 2 (value-of-residue u + value-of-residue v) ≡ add₂ u v
  tbl-add₂ (Even ∷ Even ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-add₂ (Even ∷ Even ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-add₂ (Even ∷ Even ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-add₂ (Even ∷ Even ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-add₂ (Even ∷ Odd ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-add₂ (Even ∷ Odd ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-add₂ (Even ∷ Odd ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-add₂ (Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-add₂ (Odd ∷ Even ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-add₂ (Odd ∷ Even ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-add₂ (Odd ∷ Even ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-add₂ (Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-add₂ (Odd ∷ Odd ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-add₂ (Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-add₂ (Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-add₂ (Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ []) = refl

  tbl-mul₂ : ∀ (u v : Residue 2) -> ρ 2 (value-of-residue u * value-of-residue v) ≡ mul₂ u v
  tbl-mul₂ (Even ∷ Even ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-mul₂ (Even ∷ Even ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-mul₂ (Even ∷ Even ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-mul₂ (Even ∷ Even ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-mul₂ (Even ∷ Odd ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-mul₂ (Even ∷ Odd ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-mul₂ (Even ∷ Odd ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-mul₂ (Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-mul₂ (Odd ∷ Even ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-mul₂ (Odd ∷ Even ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-mul₂ (Odd ∷ Even ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-mul₂ (Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ []) = refl
  tbl-mul₂ (Odd ∷ Odd ∷ []) (Even ∷ Even ∷ []) = refl
  tbl-mul₂ (Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ []) = refl
  tbl-mul₂ (Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ []) = refl
  tbl-mul₂ (Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ []) = refl

  tbl-neg₂ : ∀ (u : Residue 2) -> ρ 2 (- value-of-residue u) ≡ u
  tbl-neg₂ (Even ∷ Even ∷ []) = refl
  tbl-neg₂ (Even ∷ Odd ∷ []) = refl
  tbl-neg₂ (Odd ∷ Even ∷ []) = refl
  tbl-neg₂ (Odd ∷ Odd ∷ []) = refl

  tbl-adj₂ : ∀ (u : Residue 2) -> ρ 2 ((value-of-residue u) †) ≡ u
  tbl-adj₂ (Even ∷ Even ∷ []) = refl
  tbl-adj₂ (Even ∷ Odd ∷ []) = refl
  tbl-adj₂ (Odd ∷ Even ∷ []) = refl
  tbl-adj₂ (Odd ∷ Odd ∷ []) = refl

  tbl-add₃ : ∀ (u v : Residue 3) -> ρ 3 (value-of-residue u + value-of-residue v) ≡ add₃ u v
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-add₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl

  tbl-mul₃ : ∀ (u v : Residue 3) -> ρ 3 (value-of-residue u * value-of-residue v) ≡ mul₃ u v
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Even ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Even ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Even ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-mul₃ (Odd ∷ Odd ∷ Odd ∷ []) (Odd ∷ Odd ∷ Odd ∷ []) = refl

  tbl-neg₃ : ∀ (u : Residue 3) -> ρ 3 (- value-of-residue u) ≡ neg₃ u
  tbl-neg₃ (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-neg₃ (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-neg₃ (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-neg₃ (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-neg₃ (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-neg₃ (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-neg₃ (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-neg₃ (Odd ∷ Odd ∷ Odd ∷ []) = refl

  tbl-adj₃ : ∀ (u : Residue 3) -> ρ 3 ((value-of-residue u) †) ≡ conj₃ u
  tbl-adj₃ (Even ∷ Even ∷ Even ∷ []) = refl
  tbl-adj₃ (Even ∷ Even ∷ Odd ∷ []) = refl
  tbl-adj₃ (Even ∷ Odd ∷ Even ∷ []) = refl
  tbl-adj₃ (Even ∷ Odd ∷ Odd ∷ []) = refl
  tbl-adj₃ (Odd ∷ Even ∷ Even ∷ []) = refl
  tbl-adj₃ (Odd ∷ Even ∷ Odd ∷ []) = refl
  tbl-adj₃ (Odd ∷ Odd ∷ Even ∷ []) = refl
  tbl-adj₃ (Odd ∷ Odd ∷ Odd ∷ []) = refl

-- ----------------------------------------------------------------------
-- * The rules, for arbitrary Gaussian integers

ρ₂-+ : ∀ x y -> ρ 2 (x + y) ≡ add₂ (ρ 2 x) (ρ 2 y)
ρ₂-+ x y = trans (ρ-mod 2 (≈-+ (ρ-sound 2 x) (ρ-sound 2 y))) (tbl-add₂ (ρ 2 x) (ρ 2 y))

ρ₂-* : ∀ x y -> ρ 2 (x * y) ≡ mul₂ (ρ 2 x) (ρ 2 y)
ρ₂-* x y = trans (ρ-mod 2 (≈-* (ρ-sound 2 x) (ρ-sound 2 y))) (tbl-mul₂ (ρ 2 x) (ρ 2 y))

-- Every element is its own additive inverse modulo γ².
ρ₂-neg : ∀ x -> ρ 2 (- x) ≡ ρ 2 x
ρ₂-neg x = trans (ρ-mod 2 (≈-neg (ρ-sound 2 x))) (tbl-neg₂ (ρ 2 x))

-- ρ₂ is stable under conjugation.
ρ₂-adj : ∀ x -> ρ 2 (x †) ≡ ρ 2 x
ρ₂-adj x = trans (ρ-mod 2 (≈-adj {n = 2} (ρ-sound 2 x))) (tbl-adj₂ (ρ 2 x))

ρ₃-+ : ∀ x y -> ρ 3 (x + y) ≡ add₃ (ρ 3 x) (ρ 3 y)
ρ₃-+ x y = trans (ρ-mod 3 (≈-+ (ρ-sound 3 x) (ρ-sound 3 y))) (tbl-add₃ (ρ 3 x) (ρ 3 y))

ρ₃-* : ∀ x y -> ρ 3 (x * y) ≡ mul₃ (ρ 3 x) (ρ 3 y)
ρ₃-* x y = trans (ρ-mod 3 (≈-* (ρ-sound 3 x) (ρ-sound 3 y))) (tbl-mul₃ (ρ 3 x) (ρ 3 y))

ρ₃-neg : ∀ x -> ρ 3 (- x) ≡ neg₃ (ρ 3 x)
ρ₃-neg x = trans (ρ-mod 3 (≈-neg (ρ-sound 3 x))) (tbl-neg₃ (ρ 3 x))

-- ρ₃(x†) = ab(c⊕b) when ρ₃(x) = abc.
ρ₃-adj : ∀ x -> ρ 3 (x †) ≡ conj₃ (ρ 3 x)
ρ₃-adj x = trans (ρ-mod 3 (≈-adj {n = 3} (ρ-sound 3 x))) (tbl-adj₃ (ρ 3 x))

-- Subtraction.
ρ₂-minus : ∀ x y -> ρ 2 (x - y) ≡ add₂ (ρ 2 x) (ρ 2 y)
ρ₂-minus x y = trans (ρ₂-+ x (- y)) (cong (λ w -> add₂ (ρ 2 x) w) (ρ₂-neg y))

ρ₃-minus : ∀ x y -> ρ 3 (x - y) ≡ add₃ (ρ 3 x) (neg₃ (ρ 3 y))
ρ₃-minus x y = trans (ρ₃-+ x (- y)) (cong (λ w -> add₃ (ρ 3 x) w) (ρ₃-neg y))

-- ----------------------------------------------------------------------
-- * The residues of i (Section II B)

ρ₂-i : ρ 2 i ≡ Odd ∷ Odd ∷ []
ρ₂-i = refl

ρ₃-i : ρ 3 i ≡ Odd ∷ Odd ∷ Odd ∷ []
ρ₃-i = refl

-- Since ρ₂(i) = 11: if x is odd then ρ₂(x) = 10 or ρ₂(ix) = 10.
ρ₂-normalize : ∀ x -> parityℤ[i] x ≡ Odd ->
               (ρ 2 x ≡ Odd ∷ Even ∷ []) ⊎ (ρ 2 (i * x) ≡ Odd ∷ Even ∷ [])
ρ₂-normalize x p with ρ 2 x in eq
... | Even ∷ _ ∷ [] = ⊥-elim (even≢odd (trans (sym (cong Vec.head eq)) (trans (ρ-head 1 x) p)))
... | Odd ∷ Even ∷ [] = inj₁ refl
... | Odd ∷ Odd ∷ [] = inj₂ (trans (ρ₂-* i x) (cong (λ w -> mul₂ (ρ 2 i) w) eq))

-- Since ρ₃(i) = 111: if x is odd then ρ₃(iᵏx) = 100 for some k ≤ 3.
ρ₃-normalize : ∀ x -> parityℤ[i] x ≡ Odd ->
               ∃ λ k -> (k ≤ 3) × (ρ 3 ((i ↑ k) * x) ≡ Odd ∷ Even ∷ Even ∷ [])
ρ₃-normalize x p with ρ 3 x in eq
... | Even ∷ _ ∷ _ ∷ [] = ⊥-elim (even≢odd (trans (sym (cong Vec.head eq)) (trans (ρ-head 2 x) p)))
... | Odd ∷ Even ∷ Even ∷ [] =
      0 , z≤n , trans (ρ₃-* (i ↑ 0) x) (cong (λ w -> mul₃ (ρ 3 (i ↑ 0)) w) eq)
... | Odd ∷ Odd ∷ Even ∷ [] =
      1 , s≤s z≤n , trans (ρ₃-* (i ↑ 1) x) (cong (λ w -> mul₃ (ρ 3 (i ↑ 1)) w) eq)
... | Odd ∷ Even ∷ Odd ∷ [] =
      2 , s≤s (s≤s z≤n) , trans (ρ₃-* (i ↑ 2) x) (cong (λ w -> mul₃ (ρ 3 (i ↑ 2)) w) eq)
... | Odd ∷ Odd ∷ Odd ∷ [] =
      3 , s≤s (s≤s (s≤s z≤n)) , trans (ρ₃-* (i ↑ 3) x) (cong (λ w -> mul₃ (ρ 3 (i ↑ 3)) w) eq)
