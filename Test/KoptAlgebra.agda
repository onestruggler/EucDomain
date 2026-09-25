-- Checks of the proofs in Kopt.Properties.* against the statements of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026), Section II.
--
-- The general lemmas are instantiated at concrete Gaussian integers,
-- and the results are compared with the tables of Section II B.

{-# OPTIONS --without-K --safe #-}

module Test.KoptAlgebra where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Kopt.Base
open import Kopt.Properties.Algebra

-- ----------------------------------------------------------------------
-- * γ = 1 + i is a Gaussian prime (Section II)

-- γ² = 2i and γγ† = 2, so γ² and 2 are associates.
_ : (ZComplex ∋ γ * γ) ≡ 2 * i
_ = γ-squared

_ : (ZComplex ∋ γ * γ†) ≡ 2
_ = γ-γ†

-- γ is not a unit, and γ ≠ 0.
_ : ∀ (u : ZComplex) -> γ * u ≡ 1 -> _
_ = γ-not-unit

-- Definition II.4: x is even iff γ divides x. 1 + 2i is odd, 1 + 3i is
-- even, and (1 + 3i)/γ = 2 + i.
_ : parityℤ[i] (1 + 2 * i) ≡ Odd
_ = refl

_ : parityℤ[i] (1 + 3 * i) ≡ Even
_ = refl

_ : (ZComplex ∋ γ * ((1 + 3 * i) /γ)) ≡ 1 + 3 * i
_ = γ-div-even (1 + 3 * i) refl

_ : (ZComplex ∋ (1 + 3 * i) /γ) ≡ 2 + i
_ = refl

-- The even numbers are exactly the multiples of γ.
_ : ∃ λ y -> (ZComplex ∋ 1 + 3 * i) ≡ γ * y
_ = even⇒divides (1 + 3 * i) refl

_ : parityℤ[i] (γ * (2 + 5 * i)) ≡ Even
_ = γ*-even (2 + 5 * i)

-- Lemma II.5: α is odd iff ∥α∥² is odd. ∥1+2i∥² = 5 and ∥1+3i∥² = 10.
_ : parityℤ[i] (1 + 2 * i) ≡ parity (normℤ[i] (1 + 2 * i))
_ = lemma-II-5 (1 + 2 * i)

_ : normℤ[i] (1 + 2 * i) ≡ 5
_ = refl

_ : evenℤ (normℤ[i] (1 + 2 * i)) ≡ false
_ = lemma-II-5-odd (1 + 2 * i) refl

_ : evenℤ (normℤ[i] (1 + 3 * i)) ≡ true
_ = lemma-II-5-even (1 + 3 * i) refl

-- Lemma II.6: γ can be cancelled. Here γ - iγ = 2 = -i γ², so
-- 1 ≡ i (mod γ).
_ : (ZComplex ∋ 1) ≈ i mod (γ ↑ 1)
_ = lemma-II-6 {1} {i} {1} (mod-wit (- i) refl)

-- ----------------------------------------------------------------------
-- * The residues ρₙ (Section II B)

-- Correctness of ρ: x ≡ value-of-residue (ρ n x) (mod γⁿ).
_ : ∃ λ k -> (ZComplex ∋ 3 + 5 * i) - value-of-residue (ρ 3 (3 + 5 * i)) ≡ k * (γ ↑ 3)
_ = ≈⇒∃ (ρ-sound 3 (3 + 5 * i))

-- Distinct binary strings are distinct classes, and ρₙ is the unique
-- representative.
_ : ρ 3 (value-of-residue (Odd ∷ Even ∷ Odd ∷ [])) ≡ Odd ∷ Even ∷ Odd ∷ []
_ = ρ-value (Odd ∷ Even ∷ Odd ∷ [])

_ : ρ 3 (2 + 2 * i) ≡ ρ 3 (2 + 2 * i + γ ↑ 3)
_ = ρ-mod 3 {2 + 2 * i} {2 + 2 * i + γ ↑ 3} (mod-wit (- 1) refl)

-- Stability under increasing n: the first two digits of ρ₃ are ρ₂.
_ : trunc (ρ 3 (3 + 5 * i)) ≡ ρ 2 (3 + 5 * i)
_ = ρ-trunc 2 (3 + 5 * i)

-- The ρ₃ table of Section II B, recomputed with the arithmetic rules.
-- 1 ↦ 100, -1 ↦ 101, i ↦ 111, -i ↦ 110, 0 ↦ 000, 1+i ↦ 010,
-- 1-i ↦ 011, 2 ↦ 001.
_ : ρ 3 1 ≡ Odd ∷ Even ∷ Even ∷ []
_ = refl

-- -(b₀b₁b₂) = b₀b₁(b₂⊕b₀), so -1 ↦ 101.
_ : ρ 3 (- 1) ≡ neg₃ (ρ 3 1)
_ = ρ₃-neg 1

_ : neg₃ (ρ 3 1) ≡ Odd ∷ Even ∷ Odd ∷ []
_ = refl

-- ρ₃(i) = 111 and -i ↦ 110.
_ : ρ 3 i ≡ Odd ∷ Odd ∷ Odd ∷ []
_ = ρ₃-i

_ : neg₃ (ρ 3 i) ≡ Odd ∷ Odd ∷ Even ∷ []
_ = refl

-- The addition rule mod γ³ has the carry b₀b′₀: 100 + 100 = 001, i.e.
-- 1 + 1 = 2.
_ : ρ 3 2 ≡ add₃ (ρ 3 1) (ρ 3 1)
_ = ρ₃-+ 1 1

_ : add₃ (ρ 3 1) (ρ 3 1) ≡ Even ∷ Even ∷ Odd ∷ []
_ = refl

-- Multiplication mod γ³: γ ⋅ γ = 2, i.e. 010 ⋅ 010 = 001, and i ⋅ i = -1.
_ : ρ 3 (γ * γ) ≡ mul₃ (ρ 3 γ) (ρ 3 γ)
_ = ρ₃-* γ γ

_ : mul₃ (ρ 3 γ) (ρ 3 γ) ≡ Even ∷ Even ∷ Odd ∷ []
_ = refl

_ : mul₃ (ρ 3 i) (ρ 3 i) ≡ ρ 3 (- 1)
_ = sym (ρ₃-* i i)

-- Modulo γ², addition is bitwise xor, every element is its own
-- additive inverse, and multiplication by 01 = γ is a right shift.
_ : ρ 2 (1 + i) ≡ add₂ (ρ 2 1) (ρ 2 i)
_ = ρ₂-+ 1 i

_ : ρ 2 (- (1 + 2 * i)) ≡ ρ 2 (1 + 2 * i)
_ = ρ₂-neg (1 + 2 * i)

_ : ρ 2 (γ * (1 + 2 * i)) ≡ mul₂ (ρ 2 γ) (ρ 2 (1 + 2 * i))
_ = ρ₂-* γ (1 + 2 * i)

-- ρ₂ is stable under conjugation, ρ₃ is not: ρ₃(x†) = ab(c⊕b).
_ : ρ 2 ((1 + 2 * i) †) ≡ ρ 2 (1 + 2 * i)
_ = ρ₂-adj (1 + 2 * i)

_ : ρ 3 (i †) ≡ conj₃ (ρ 3 i)
_ = ρ₃-adj i

_ : conj₃ (ρ 3 i) ≡ ρ 3 (- i)
_ = refl

-- ρ₂(i) = 11 and ρ₃(i) = 111, so an odd x can be normalized by a
-- power of i.
_ : ρ 2 i ≡ Odd ∷ Odd ∷ []
_ = ρ₂-i

_ : (ρ 2 (1 + 2 * i) ≡ Odd ∷ Even ∷ []) ⊎ (ρ 2 (i * (1 + 2 * i)) ≡ Odd ∷ Even ∷ [])
_ = ρ₂-normalize (1 + 2 * i) refl

_ : ∃ λ k -> (k ≤ 3) × (ρ 3 ((i ↑ k) * (1 + 2 * i)) ≡ Odd ∷ Even ∷ Even ∷ [])
_ = ρ₃-normalize (1 + 2 * i) refl

-- The shifts RS and LS (Lemma II.9).
_ : ρ 3 (γ * (1 + 2 * i)) ≡ RS (ρ 2 (1 + 2 * i))
_ = ρ-RS 2 (1 + 2 * i)

_ : ρ 2 ((1 + 3 * i) /γ) ≡ LS (ρ 3 (1 + 3 * i))
_ = ρ-LS 2 (1 + 3 * i) refl

-- ----------------------------------------------------------------------
-- * The K action (Section II C)

-- Two odd entries with ρ₃ = 100: K sends them to 0(b⊕b′⊕1) and
-- 0(b⊕b′), i.e. (1+1)/γ = 1-i has residue 01 and (1-1)/γ = 0 has
-- residue 00.
_ : (ρ 2 (((ZComplex ∋ 1) + 1) /γ) ≡ Even ∷ Odd ∷ []) ×
    (ρ 2 (((ZComplex ∋ 1) - 1) /γ) ≡ Even ∷ Even ∷ [])
_ = K-case-odd-odd 1 1 Even Even Even Even refl refl

-- ρ₃(1) = 100 and ρ₃(-1) = 101: the two entries are 00 and 01, since
-- (1 + (-1))/γ = 0 and (1 - (-1))/γ = 1 - i.
_ : (ρ 2 (((ZComplex ∋ 1) + (- 1)) /γ) ≡ Even ∷ Even ∷ []) ×
    (ρ 2 (((ZComplex ∋ 1) - (- 1)) /γ) ≡ Even ∷ Odd ∷ [])
_ = K-case-odd-odd 1 (- 1) Even Even Even Odd refl refl

-- One odd and one even entry: the lde increases, and both entries of
-- K[x,y]ᵀ have residue 1(b₀⊕b′₀)(b₁⊕b′₁).
_ : (ρ 3 ((ZComplex ∋ 1) + γ) ≡ Odd ∷ Odd ∷ Even ∷ []) ×
    (ρ 3 ((ZComplex ∋ 1) - γ) ≡ Odd ∷ Odd ∷ Even ∷ [])
_ = K-case-odd-even 1 γ Even Even Odd Even refl refl

-- Lemma II.9 for two odd entries: ρ₂(x ± y) = 0(b⊕b′).
_ : ρ 2 ((ZComplex ∋ 1) + i) ≡ Even ∷ Odd ∷ []
_ = lemma-II-9-+ 1 i Even Odd refl refl

-- ----------------------------------------------------------------------
-- * The least denominator exponent (Definition II.1)

-- u = 1/γ⁵ has lde 5, and γ⁵u = 1.
u5 : DComplex
u5 = 1/γ ^ 5

_ : lde u5 ≡ 5
_ = refl

_ : u5 * (γ ↑ 5) ≡ from-whole 1
_ = refl

-- Correctness: lde u is a denominator exponent, and the least one.
_ : DenomExpγ (lde u5) u5
_ = lde-denom-exp u5

_ : ∀ j -> DenomExpγ j u5 -> lde u5 ≤ j
_ = lde-least u5

-- Lemma II.7: γ⁵u = 1 is odd.
_ : parityℤ[i] 1 ≡ Odd
_ = lemma-II-7 u5 4 1 refl refl

-- Lemma II.8: subadditivity, with equality for odd arguments.
_ : lde (u5 * u5) ≤ lde u5 + lde u5
_ = lemma-II-8 u5 u5

_ : lde (u5 * u5) ≡ lde u5 + lde u5
_ = lemma-II-8-odd u5 u5 1 1 refl refl refl refl

_ : lde (u5 * u5) ≡ 10
_ = refl

-- ----------------------------------------------------------------------
-- * The K action on 𝔻[i] (Section II C) and Remark II.10

-- x = y = 1/γ have lde 1 and (3,1)-residue 100; K maps them to
-- entries with (2,1)-residues 01 and 00 (Lemma II.9).
_ : (ρ^ 1 2 ((1/γ + 1/γ) * invγ) ≡ Even ∷ Odd ∷ []) ×
    (ρ^ 1 2 ((1/γ - 1/γ) * invγ) ≡ Even ∷ Even ∷ [])
_ = K-residue-odd-odd 1 1/γ 1/γ 1 1 Even Even Even Even refl refl refl refl

-- The (n,l)-residue of Definition II.3.
_ : ρ^ 1 3 (DComplex ∋ 1/γ) ≡ ρ 3 1
_ = ρ^-whole 1 3 1/γ 1 refl

-- Remark II.10: K decreases the lde of a pair by at most one, i.e.
-- K⁻¹ = iK increases it by at most one.
_ : max (lde (i * (((DComplex ∋ 1/γ) + 1/γ) * invγ))) (lde (i * (((DComplex ∋ 1/γ) - 1/γ) * invγ)))
    ≤ suc (max (lde (DComplex ∋ 1/γ)) (lde (DComplex ∋ 1/γ)))
_ = remark-II-10 1/γ 1/γ
