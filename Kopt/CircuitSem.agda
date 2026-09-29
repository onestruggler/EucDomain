-- The circuits of Section III C implement the matrices they are meant
-- to implement, as a proof rather than as a check in Test.
--
-- Kopt.Permutations computes, for a permutation x, a circuit
-- perm-circuit-of x of at most three gates (Table I), and for a phase
-- tuple e a circuit diag-circuit-of e; that these implement
-- perm-matrix-of x and diag-matrix-of e is verified by running them on
-- the 24 permutations and the 256 phase tuples. Test.KoptPermutations
-- already does that; here the same checks are done with the enumeration
-- machinery of Kopt.Descent, so that the membership of a particular
-- permutation in all-perms turns the check into a statement about it.
-- That is what a proof about the circuits the algorithm emits needs: the
-- search of Kopt.Patterns returns a permutation together with its
-- membership, and nothing else is known about it.
--
-- The circuits are also K-free (gp-circuit? of Kopt.Optimality), which
-- with Remark II.10 is what makes them harmless to the lde.

{-# OPTIONS --without-K --safe #-}

module Kopt.CircuitSem where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Descent using (all-of ; all-of-∈ ; ∧-true ; _∈ˡ_)
open import Kopt.GPData using (==⇒≡)
open import Kopt.Optimality using (gp-circuit?)

-- ----------------------------------------------------------------------
-- * K-freeness of a concatenation

gp-circuit?-++ : (c d : Circuit) -> gp-circuit? c ≡ true -> gp-circuit? d ≡ true ->
                 gp-circuit? (c ++ d) ≡ true
gp-circuit?-++ [] d _ hd = hd
gp-circuit?-++ (g ∷ c) d hc hd =
  trans (cong (λ β -> β ∧ gp-circuit? (c ++ d)) (proj₁ (∧-true hc)))
        (gp-circuit?-++ c d (proj₂ (∧-true hc)) hd)

-- ----------------------------------------------------------------------
-- * The 24 permutation circuits (Table I)

private
  perm-check : Tuple4 -> Bool
  perm-check x = (⟦ perm-circuit-of x ⟧ == perm-matrix-of x) ∧ gp-circuit? (perm-circuit-of x)

  perm-all : all-of perm-check all-perms ≡ true
  perm-all = refl

  perm-parts : (x : Tuple4) -> x ∈ˡ all-perms ->
               ((⟦ perm-circuit-of x ⟧ == perm-matrix-of x) ≡ true)
                 × (gp-circuit? (perm-circuit-of x) ≡ true)
  perm-parts x m = ∧-true (all-of-∈ perm-check all-perms perm-all m)

perm-sem : (x : Tuple4) -> x ∈ˡ all-perms -> ⟦ perm-circuit-of x ⟧ ≡ perm-matrix-of x
perm-sem x m = ==⇒≡ (proj₁ (perm-parts x m))

perm-kfree : (x : Tuple4) -> x ∈ˡ all-perms -> gp-circuit? (perm-circuit-of x) ≡ true
perm-kfree x m = proj₂ (perm-parts x m)

-- ----------------------------------------------------------------------
-- * The 256 diagonal circuits
--
-- The phases are exponents of i, so the tuples range over {0,1,2,3}.
-- (The algorithm only ever uses the 16 tuples over {0,1}, but the whole
-- list costs no more to state and is what Test.KoptPermutations checks.)

all-phases : List Tuple4
all-phases =
  concatMap (λ a -> concatMap (λ b -> concatMap (λ c ->
    map (λ d -> (a , b , c , d)) digits) digits) digits) digits
  where
    digits : List ℕ
    digits = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

private
  diag-check : Tuple4 -> Bool
  diag-check e = (⟦ diag-circuit-of e ⟧ == diag-matrix-of e) ∧ gp-circuit? (diag-circuit-of e)

  diag-all : all-of diag-check all-phases ≡ true
  diag-all = refl

  diag-parts : (e : Tuple4) -> e ∈ˡ all-phases ->
               ((⟦ diag-circuit-of e ⟧ == diag-matrix-of e) ≡ true)
                 × (gp-circuit? (diag-circuit-of e) ≡ true)
  diag-parts e m = ∧-true (all-of-∈ diag-check all-phases diag-all m)

diag-sem : (e : Tuple4) -> e ∈ˡ all-phases -> ⟦ diag-circuit-of e ⟧ ≡ diag-matrix-of e
diag-sem e m = ==⇒≡ (proj₁ (diag-parts e m))

diag-kfree : (e : Tuple4) -> e ∈ˡ all-phases -> gp-circuit? (diag-circuit-of e) ≡ true
diag-kfree e m = proj₂ (diag-parts e m)
