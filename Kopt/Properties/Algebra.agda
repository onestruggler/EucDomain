-- Section II ("Some algebra") of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026).
--
-- This module collects the results of
--
--   Kopt.Properties.Gamma        γ = 1+i, parity (Definition II.4),
--                                Lemma II.5, congruences, Lemma II.6,
--   Kopt.Properties.DyadicTools  the embedding ℤ[i] → 𝔻[i],
--   Kopt.Properties.Residue      the residues ρₙ (Section II B),
--   Kopt.Properties.KAction      the K action on residues (Section II C),
--   Kopt.Properties.Lde          Definition II.1 (correctness of lde),
--   Kopt.Properties.LdeLemmas    Lemmas II.7 and II.8,
--   Kopt.Properties.KResidue     Definition II.3 and the K action on 𝔻[i],
--
-- and adds the first half of Remark II.10: K decreases the lde of a
-- pair of entries by at most one.
--
-- Note: the ring solver is never used for 𝔻[i]; see the comment on
-- CRLemmas in Kopt.Properties.Lde.

{-# OPTIONS --without-K --safe #-}

module Kopt.Properties.Algebra where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; T ; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
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

open import Kopt.Properties.Gamma public
open import Kopt.Properties.DyadicTools public
open import Kopt.Properties.Residue public
open import Kopt.Properties.KAction public
open import Kopt.Properties.Lde public
open import Kopt.Properties.LdeLemmas public
open import Kopt.Properties.KResidue public

private
  module DR = IsCommutativeRing isCommutativeRing-DComplex

-- ----------------------------------------------------------------------
-- * Remark II.10 (first half)

private
  neg-eq : ∀ (q : DComplex) -> from-whole (- 1#) * q ≡ - q
  neg-eq q = trans (sym (DL.-‿distribˡ-* 1# q)) (cong (λ z -> - z) (DR.*-identityˡ q))

  neg-neg : ∀ (q : DComplex) -> from-whole (- 1#) * (- q) ≡ q
  neg-neg q = trans (neg-eq (- q)) (DL.-‿involutive q)

  lde-neg : ∀ (q : DComplex) -> lde (- q) ≡ lde q
  lde-neg q = NatP.≤-antisym
    (subst (λ z -> lde z Nat.≤ lde q) (neg-eq q) (lde-whole-≤ (- 1#) q))
    (subst (λ z -> lde z Nat.≤ lde (- q)) (neg-neg q) (lde-whole-≤ (- 1#) (- q)))

  lde-minus : ∀ (p q : DComplex) -> lde (p - q) Nat.≤ max (lde p) (lde q)
  lde-minus p q = subst (λ n -> lde (p - q) Nat.≤ max (lde p) n) (lde-neg q) (lde-+ p (- q))

-- Remark II.10, for a pair (u,v) that K maps to (x,y): the lde of
-- (x,y) is at most one more than the lde of (u,v).
remark-II-10-gen : ∀ (x y u v : DComplex) ->
                   i * ((u + v) * invγ) ≡ x -> i * ((u - v) * invγ) ≡ y ->
                   max (lde x) (lde y) Nat.≤ suc (max (lde u) (lde v))
remark-II-10-gen x y u v ex ey = max-lub bound-x bound-y
  where
    M : ℕ
    M = max (lde u) (lde v)
    bound-x : lde x Nat.≤ suc M
    bound-x = subst (λ z -> lde z Nat.≤ suc M) ex
      (subst (λ n -> n Nat.≤ suc M) (sym (lde-i ((u + v) * invγ)))
        (NatP.≤-trans (lde-invγ (u + v)) (s≤s (lde-+ u v))))
    bound-y : lde y Nat.≤ suc M
    bound-y = subst (λ z -> lde z Nat.≤ suc M) ey
      (subst (λ n -> n Nat.≤ suc M) (sym (lde-i ((u - v) * invγ)))
        (NatP.≤-trans (lde-invγ (u - v)) (s≤s (lde-minus u v))))

-- Remark II.10 (first half): K decreases the lde of a pair by at most
-- one. Since K⁻¹ = iK, this says that applying K⁻¹ to a pair (u,v)
-- increases the lde by at most one: if (u,v) = K[x,y]ᵀ then
-- (x,y) = K⁻¹[u,v]ᵀ = (i(u+v)/γ , i(u-v)/γ), so
--
--   lde(x,y) = max (lde x) (lde y) ≤ 1 + max (lde u) (lde v) = 1 + lde(K[x,y]ᵀ).
remark-II-10 : ∀ (u v : DComplex) ->
               max (lde (i * ((u + v) * invγ))) (lde (i * ((u - v) * invγ)))
               Nat.≤ suc (max (lde u) (lde v))
remark-II-10 u v = remark-II-10-gen (i * ((u + v) * invγ)) (i * ((u - v) * invγ)) u v refl refl
