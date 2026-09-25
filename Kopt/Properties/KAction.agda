-- Section II C of Bian & Feng: the effect of the gate
--
--   K = (1/γ) [[1,1],[1,-1]]
--
-- on the residues of a pair of entries, and the consequences of the
-- shift equations of Lemma II.9.
--
-- All the statements are about the integral representatives: if l is
-- a denominator exponent of x and y, with X = γˡx and Y = γˡy in
-- ℤ[i], then the entries of K[x,y]ᵀ are (X±Y)/γ divided by γˡ, so
--
--   ρˡ₂(K[x,y]ᵀ) = (ρ₂((X+Y)/γ) , ρ₂((X-Y)/γ)) ,
--
-- and, when the lde increases, ρˡ⁺¹₃(K[x,y]ᵀ) = (ρ₃(X+Y) , ρ₃(X-Y)).
-- The translation to 𝔻[i] is in Kopt.Properties.Algebra.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.KAction where

open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Kopt.Base
open import Kopt.Properties.Gamma
open import Kopt.Properties.Residue

-- ----------------------------------------------------------------------
-- * Small facts about ℤ₂

private
  z2-cancel : ∀ (u v : Z2) -> u + (v + Odd) + Odd ≡ u + v
  z2-cancel Even Even = refl
  z2-cancel Even Odd = refl
  z2-cancel Odd Even = refl
  z2-cancel Odd Odd = refl

  z2-carry : ∀ (u v : Z2) -> u + (v + Odd) + Even ≡ u + v + Odd
  z2-carry Even Even = refl
  z2-carry Even Odd = refl
  z2-carry Odd Even = refl
  z2-carry Odd Odd = refl

  z2-Even : ∀ (u : Z2) -> u + Even ≡ u
  z2-Even Even = refl
  z2-Even Odd = refl

  z2-cancel-E : ∀ (u v : Z2) -> u + (v + Even) + Even ≡ u + v
  z2-cancel-E Even Even = refl
  z2-cancel-E Even Odd = refl
  z2-cancel-E Odd Even = refl
  z2-cancel-E Odd Odd = refl

-- ----------------------------------------------------------------------
-- * The parity of a sum can be read off from its residue

private
  even-of-ρ₃ : ∀ Z {u v} -> ρ 3 Z ≡ Even ∷ u ∷ v ∷ [] -> parityℤ[i] Z ≡ Even
  even-of-ρ₃ Z e = trans (sym (ρ-head 2 Z)) (cong Vec.head e)

-- ----------------------------------------------------------------------
-- * Lemma II.9: adding two odd numbers
--
-- If ρ₂(X) = 1b and ρ₂(Y) = 1b′ then ρ₂(X ± Y) = 0(b⊕b′). (For x, y
-- of lde l > 0 these are the (2,l)-residues, so the lde of x ± y
-- drops by 1 if b⊕b′ = 1, and by at least 2 otherwise.)

lemma-II-9-+ : ∀ X Y b b' -> ρ 2 X ≡ Odd ∷ b ∷ [] -> ρ 2 Y ≡ Odd ∷ b' ∷ [] ->
               ρ 2 (X + Y) ≡ Even ∷ (b + b') ∷ []
lemma-II-9-+ X Y b b' hx hy = trans (ρ₂-+ X Y) (cong₂ add₂ hx hy)

lemma-II-9-- : ∀ X Y b b' -> ρ 2 X ≡ Odd ∷ b ∷ [] -> ρ 2 Y ≡ Odd ∷ b' ∷ [] ->
               ρ 2 (X - Y) ≡ Even ∷ (b + b') ∷ []
lemma-II-9-- X Y b b' hx hy = trans (ρ₂-minus X Y) (cong₂ add₂ hx hy)

-- ----------------------------------------------------------------------
-- * The four cases of the K action (Section II C)

-- (i) ρ₃(X) = 1b₀b₁ and ρ₃(Y) = 1b′₀b′₁: the sum and the difference
-- are even, and dividing them by γ gives the (2,l-1)-residues
--
--   [(b₀⊕b′₀)(b₁⊕b′₁⊕1) , (b₀⊕b′₀)(b₁⊕b′₁)] .

K-case-odd-odd : ∀ X Y b₀ b₁ b₀' b₁' ->
  ρ 3 X ≡ Odd ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Odd ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ 2 ((X + Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ []) ×
  (ρ 2 ((X - Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-case-odd-odd X Y b₀ b₁ b₀' b₁' hx hy = first , second
  where
    sum₃ : ρ 3 (X + Y) ≡ Even ∷ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ []
    sum₃ = trans (ρ₃-+ X Y) (cong₂ add₃ hx hy)
    dif₃ : ρ 3 (X - Y) ≡ Even ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    dif₃ = trans (trans (ρ₃-minus X Y) (cong₂ add₃ hx (cong neg₃ hy)))
                 (cong (λ w -> Even ∷ (b₀ + b₀') ∷ w ∷ []) (z2-cancel b₁ b₁'))
    first : ρ 2 ((X + Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ []
    first = trans (ρ-LS 2 (X + Y) (even-of-ρ₃ (X + Y) sum₃)) (cong LS sum₃)
    second : ρ 2 ((X - Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    second = trans (ρ-LS 2 (X - Y) (even-of-ρ₃ (X - Y) dif₃)) (cong LS dif₃)

-- (ii) ρ₃(X) = 0b₀b₁ and ρ₃(Y) = 0b′₀b′₁: both entries have residue
-- (b₀⊕b′₀)(b₁⊕b′₁).

K-case-even-even : ∀ X Y b₀ b₁ b₀' b₁' ->
  ρ 3 X ≡ Even ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Even ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ 2 ((X + Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ 2 ((X - Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-case-even-even X Y b₀ b₁ b₀' b₁' hx hy = first , second
  where
    sum₃ : ρ 3 (X + Y) ≡ Even ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    sum₃ = trans (trans (ρ₃-+ X Y) (cong₂ add₃ hx hy))
                 (cong (λ w -> Even ∷ (b₀ + b₀') ∷ w ∷ []) (z2-Even (b₁ + b₁')))
    dif₃ : ρ 3 (X - Y) ≡ Even ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    dif₃ = trans (trans (ρ₃-minus X Y) (cong₂ add₃ hx (cong neg₃ hy)))
                 (cong (λ w -> Even ∷ (b₀ + b₀') ∷ w ∷ []) (z2-cancel-E b₁ b₁'))
    first : ρ 2 ((X + Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    first = trans (ρ-LS 2 (X + Y) (even-of-ρ₃ (X + Y) sum₃)) (cong LS sum₃)
    second : ρ 2 ((X - Y) /γ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    second = trans (ρ-LS 2 (X - Y) (even-of-ρ₃ (X - Y) dif₃)) (cong LS dif₃)

-- (iii) ρ₃(X) = 1b₀b₁ and ρ₃(Y) = 0b′₀b′₁: the sum and the difference
-- are odd, so the lde increases; both have residue 1(b₀⊕b′₀)(b₁⊕b′₁).

K-case-odd-even : ∀ X Y b₀ b₁ b₀' b₁' ->
  ρ 3 X ≡ Odd ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Even ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ 3 (X + Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ 3 (X - Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-case-odd-even X Y b₀ b₁ b₀' b₁' hx hy = sum₃ , dif₃
  where
    sum₃ : ρ 3 (X + Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    sum₃ = trans (trans (ρ₃-+ X Y) (cong₂ add₃ hx hy))
                 (cong (λ w -> Odd ∷ (b₀ + b₀') ∷ w ∷ []) (z2-Even (b₁ + b₁')))
    dif₃ : ρ 3 (X - Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    dif₃ = trans (trans (ρ₃-minus X Y) (cong₂ add₃ hx (cong neg₃ hy)))
                 (cong (λ w -> Odd ∷ (b₀ + b₀') ∷ w ∷ []) (z2-cancel-E b₁ b₁'))

-- (iv) ρ₃(X) = 0b₀b₁ and ρ₃(Y) = 1b′₀b′₁: the residues are
-- 1(b₀⊕b′₀)(b₁⊕b′₁) and 1(b₀⊕b′₀)(b₁⊕b′₁⊕1).

K-case-even-odd : ∀ X Y b₀ b₁ b₀' b₁' ->
  ρ 3 X ≡ Even ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Odd ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ 3 (X + Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ 3 (X - Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ [])
K-case-even-odd X Y b₀ b₁ b₀' b₁' hx hy = sum₃ , dif₃
  where
    sum₃ : ρ 3 (X + Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []
    sum₃ = trans (trans (ρ₃-+ X Y) (cong₂ add₃ hx hy))
                 (cong (λ w -> Odd ∷ (b₀ + b₀') ∷ w ∷ []) (z2-Even (b₁ + b₁')))
    dif₃ : ρ 3 (X - Y) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ []
    dif₃ = trans (trans (ρ₃-minus X Y) (cong₂ add₃ hx (cong neg₃ hy)))
                 (cong (λ w -> Odd ∷ (b₀ + b₀') ∷ w ∷ []) (z2-carry b₁ b₁'))

-- ----------------------------------------------------------------------
-- * The special case of Lemma II.9
--
-- If ρ₃(X) = 10b and ρ₃(Y) = 10b′ then the two entries of K[x,y]ᵀ
-- have residues 0(b⊕b′⊕1) and 0(b⊕b′): one entry has lde l-1 and the
-- other at most l-2.

lemma-II-9-K : ∀ X Y b b' ->
  ρ 3 X ≡ Odd ∷ Even ∷ b ∷ [] -> ρ 3 Y ≡ Odd ∷ Even ∷ b' ∷ [] ->
  (ρ 2 ((X + Y) /γ) ≡ Even ∷ (b + b' + Odd) ∷ []) ×
  (ρ 2 ((X - Y) /γ) ≡ Even ∷ (b + b') ∷ [])
lemma-II-9-K X Y b b' hx hy = K-case-odd-odd X Y Even b Even b' hx hy
