-- The (n,l)-residues of Definition II.3 and the K action of Section
-- II C, for pairs of elements of 𝔻[i]. See Kopt.Properties.Algebra
-- for the rest of Section II.
--
-- Note: the ring solver is never used for 𝔻[i]; see the comment on
-- CRLemmas in Kopt.Properties.Lde.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.KResidue where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; T ; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NatP
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Product.Base using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Kopt.Base
open import Kopt.Properties.Gamma
open import Kopt.Properties.DyadicTools
open import Kopt.Properties.Residue
open import Kopt.Properties.KAction
open import Kopt.Properties.Lde
open import Kopt.Properties.LdeVars
open import Kopt.Properties.LdeLemmas

private
  module DR = IsCommutativeRing isCommutativeRing-DComplex

-- ρˡₙ(x) = ρₙ(γˡx), for l a denominator exponent of x.
ρ^ : (l n : ℕ) -> DComplex -> Residue n
ρ^ l n x = ρ n (to-whole (x * (γ ↑ l)))

ρ^-whole : ∀ (l n : ℕ) (x : DComplex) (X : ZComplex) -> x * (γ ↑ l) ≡ from-whole X -> ρ^ l n x ≡ ρ n X
ρ^-whole l n x X h = cong (ρ n) (trans (cong (λ z -> to-whole z) h) (to-whole-from-whole X))

-- K acts on a pair of entries by [x,y] ↦ [(x+y)/γ, (x-y)/γ].
K-pair : DComplex -> DComplex -> DComplex × DComplex
K-pair x y = ((x + y) * invγ , (x - y) * invγ)

-- The four chains below are the lemmas whole-div-+, whole-div-minus,
-- whole-up-+ and whole-up-minus of Kopt.Properties.LdeVars, which are
-- proved over VARIABLES g (for γ), u (for 1/γ), p (for γ↑l) and q
-- (for γ↑(l+1)). Here they are used at the concrete constants by pure
-- instantiation: the conclusion of the instantiated lemma is
-- syntactically the goal, and the hypotheses are from-whole-γ, γ-invγ
-- / invγ-γ and ↑-suc. Written out as reasoning chains at the
-- concrete constants (as they were), the four of them cost 705 s of
-- type checking, because every step converts two different
-- expressions denoting the same element of 𝔻[i], which unfolds the
-- whole dyadic arithmetic; this way they cost 66 s, of which 57 s is
-- the residual cost of the two whose statement contains γ↑(l+1) =
-- γ·γ↑l -- a product that reduces -- rather than the stuck γ↑l.

-- γˡ((x+y)/γ) = V when X = γˡx, Y = γˡy and X + Y = γV.
K-whole-gen : ∀ (l : ℕ) (x y : DComplex) (X Y V : ZComplex) ->
              x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y -> X + Y ≡ γ * V ->
              ((x + y) * invγ) * (γ ↑ l) ≡ from-whole V
K-whole-gen l x y X Y V hx hy e =
  whole-div-+ x y invγ γ (γ ↑ l) γ X Y V from-whole-γ γ-invγ hx hy e

K-whole-gen' : ∀ (l : ℕ) (x y : DComplex) (X Y V : ZComplex) ->
               x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y -> X - Y ≡ γ * V ->
               ((x - y) * invγ) * (γ ↑ l) ≡ from-whole V
K-whole-gen' l x y X Y V hx hy e =
  whole-div-minus x y invγ γ (γ ↑ l) γ X Y V from-whole-γ γ-invγ hx hy e

-- γˡ((x+y)/γ) = (X+Y)/γ when X = γˡx and Y = γˡy are integral and
-- X + Y is even.
K-whole : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) -> x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
          parityℤ[i] (X + Y) ≡ Even ->
          ((x + y) * invγ) * (γ ↑ l) ≡ from-whole ((X + Y) /γ)
K-whole l x y X Y hx hy pe =
  K-whole-gen l x y X Y ((X + Y) /γ) hx hy (sym (γ-div-even (X + Y) pe))

K-whole' : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) -> x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
           parityℤ[i] (X - Y) ≡ Even ->
           ((x - y) * invγ) * (γ ↑ l) ≡ from-whole ((X - Y) /γ)
K-whole' l x y X Y hx hy pe =
  K-whole-gen' l x y X Y ((X - Y) /γ) hx hy (sym (γ-div-even (X - Y) pe))

-- When the lde increases, the relevant level is l+1: γˡ⁺¹((x±y)/γ) = X±Y.
K-whole-up : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) -> x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
             ((x + y) * invγ) * (γ ↑ suc l) ≡ from-whole (X + Y)
K-whole-up l x y X Y hx hy =
  whole-up-+ x y invγ γ (γ ↑ l) (γ ↑ suc l) X Y invγ-γ (↑-suc γ l) hx hy

K-whole-up' : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) -> x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
              ((x - y) * invγ) * (γ ↑ suc l) ≡ from-whole (X - Y)
K-whole-up' l x y X Y hx hy =
  whole-up-minus x y invγ γ (γ ↑ l) (γ ↑ suc l) X Y invγ-γ (↑-suc γ l) hx hy

-- ----------------------------------------------------------------------
-- * The four cases of Section II C, for x, y ∈ 𝔻[i]

-- (i) both entries odd: the lde drops.
K-residue-odd-odd : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) (b₀ b₁ b₀' b₁' : Z2) ->
  x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
  ρ 3 X ≡ Odd ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Odd ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ^ l 2 ((x + y) * invγ) ≡ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ []) ×
  (ρ^ l 2 ((x - y) * invγ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-residue-odd-odd l x y X Y b₀ b₁ b₀' b₁' hx hy rx ry =
  trans (ρ^-whole l 2 ((x + y) * invγ) ((X + Y) /γ) (K-whole l x y X Y hx hy even+))
        (proj₁ (K-case-odd-odd X Y b₀ b₁ b₀' b₁' rx ry)) ,
  trans (ρ^-whole l 2 ((x - y) * invγ) ((X - Y) /γ) (K-whole' l x y X Y hx hy even-))
        (proj₂ (K-case-odd-odd X Y b₀ b₁ b₀' b₁' rx ry))
  where
    oddX : parityℤ[i] X ≡ Odd
    oddX = parity-of-ρ 2 X Odd _ rx
    oddY : parityℤ[i] Y ≡ Odd
    oddY = parity-of-ρ 2 Y Odd _ ry
    even+ : parityℤ[i] (X + Y) ≡ Even
    even+ = trans (parity-+ X Y) (cong₂ (λ p q -> p + q) oddX oddY)
    even- : parityℤ[i] (X - Y) ≡ Even
    even- = trans (parity-minus X Y) (cong₂ (λ p q -> p + q) oddX oddY)

-- (ii) both entries even.
K-residue-even-even : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) (b₀ b₁ b₀' b₁' : Z2) ->
  x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
  ρ 3 X ≡ Even ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Even ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ^ l 2 ((x + y) * invγ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ^ l 2 ((x - y) * invγ) ≡ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-residue-even-even l x y X Y b₀ b₁ b₀' b₁' hx hy rx ry =
  trans (ρ^-whole l 2 ((x + y) * invγ) ((X + Y) /γ) (K-whole l x y X Y hx hy even+))
        (proj₁ (K-case-even-even X Y b₀ b₁ b₀' b₁' rx ry)) ,
  trans (ρ^-whole l 2 ((x - y) * invγ) ((X - Y) /γ) (K-whole' l x y X Y hx hy even-))
        (proj₂ (K-case-even-even X Y b₀ b₁ b₀' b₁' rx ry))
  where
    evX : parityℤ[i] X ≡ Even
    evX = parity-of-ρ 2 X Even _ rx
    evY : parityℤ[i] Y ≡ Even
    evY = parity-of-ρ 2 Y Even _ ry
    even+ : parityℤ[i] (X + Y) ≡ Even
    even+ = trans (parity-+ X Y) (cong₂ (λ p q -> p + q) evX evY)
    even- : parityℤ[i] (X - Y) ≡ Even
    even- = trans (parity-minus X Y) (cong₂ (λ p q -> p + q) evX evY)

-- (iii) one odd, one even: the lde increases, so the residues are
-- taken at level l+1.
K-residue-odd-even : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) (b₀ b₁ b₀' b₁' : Z2) ->
  x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
  ρ 3 X ≡ Odd ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Even ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ^ (suc l) 3 ((x + y) * invγ) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ^ (suc l) 3 ((x - y) * invγ) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ [])
K-residue-odd-even l x y X Y b₀ b₁ b₀' b₁' hx hy rx ry =
  trans (ρ^-whole (suc l) 3 ((x + y) * invγ) (X + Y) (K-whole-up l x y X Y hx hy))
        (proj₁ (K-case-odd-even X Y b₀ b₁ b₀' b₁' rx ry)) ,
  trans (ρ^-whole (suc l) 3 ((x - y) * invγ) (X - Y) (K-whole-up' l x y X Y hx hy))
        (proj₂ (K-case-odd-even X Y b₀ b₁ b₀' b₁' rx ry))

-- (iv) one even, one odd.
K-residue-even-odd : ∀ (l : ℕ) (x y : DComplex) (X Y : ZComplex) (b₀ b₁ b₀' b₁' : Z2) ->
  x * (γ ↑ l) ≡ from-whole X -> y * (γ ↑ l) ≡ from-whole Y ->
  ρ 3 X ≡ Even ∷ b₀ ∷ b₁ ∷ [] -> ρ 3 Y ≡ Odd ∷ b₀' ∷ b₁' ∷ [] ->
  (ρ^ (suc l) 3 ((x + y) * invγ) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁') ∷ []) ×
  (ρ^ (suc l) 3 ((x - y) * invγ) ≡ Odd ∷ (b₀ + b₀') ∷ (b₁ + b₁' + Odd) ∷ [])
K-residue-even-odd l x y X Y b₀ b₁ b₀' b₁' hx hy rx ry =
  trans (ρ^-whole (suc l) 3 ((x + y) * invγ) (X + Y) (K-whole-up l x y X Y hx hy))
        (proj₁ (K-case-even-odd X Y b₀ b₁ b₀' b₁' rx ry)) ,
  trans (ρ^-whole (suc l) 3 ((x - y) * invγ) (X - Y) (K-whole-up' l x y X Y hx hy))
        (proj₂ (K-case-even-odd X Y b₀ b₁ b₀' b₁' rx ry))

