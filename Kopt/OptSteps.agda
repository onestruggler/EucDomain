-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the facts about single steps of a descent that the induction of
-- Kopt.OptInduction needs, and that are about concrete 4×4 matrices
-- rather than about patterns:
--
--  * Remark II.10 for one K gate, in both directions and on both
--    sides: a K gate changes the lde by at most one (and, by
--    Kopt.Optimality, nothing else changes it at all), so along a list
--    of steps the lde changes by at most its K-count;
--  * the invertibility of a descent: every step can be undone by a
--    list of steps with the same K-count, because K₁⁻¹ = i·K₁. This is
--    what turns Lemma V.6 into the statement the induction needs.
--
-- It also states the one fact about Kopt.Patterns.patof that the
-- induction needs and that cannot be proved outside that module
-- (Lemma-IV-1-I).
--
-- Performance. Everything here is assembled from the cancellation
-- lemmas of the first section, whose statements contain nothing but
-- matrix *variables*; the only places where a concrete 4×4 matrix over
-- 𝔻[i] appears are the three closed facts i·K₁·K₁ = 1, K₁·K₁·i = 1 and
-- lde(K₁) = 1. Writing the same proofs inline, with ⟦K₁⟧g and
-- gp-mat i-gp substituted into every step, makes the conversion checker
-- normalise those matrices against a symbolic one over and over (the
-- record Matrix has eta, so a variable is expanded too) and pushes the
-- module past the twenty minute limit of agda-check.sh. This module is
-- also split off from Kopt.OptInduction for the same reason.

{-# OPTIONS --without-K --safe #-}

module Kopt.OptSteps where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s ; _∸_)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Patterns using (SixCases ; I ; II ; III ; IV ; IVt ; V ; VI ; patof ; DecEqSixCases)
open import Kopt.Descent
open import Kopt.Optimality

-- ----------------------------------------------------------------------
-- * Small helpers

false-true : false ≡ true -> ⊥
false-true ()

just-inj : {A : Set} {x y : A} -> _≡_ {A = Maybe A} (just x) (just y) -> x ≡ y
just-inj refl = refl

-- Case analysis on a boolean test that guards an if. The two branches
-- are explicit arguments: an "if" on a neutral scrutinee is a blocked
-- term, which the unifier does not decompose, so they cannot be
-- inferred from the hypothesis.
if-true : (b x y : Bool) -> (if b then x else y) ≡ true ->
          ((b ≡ true) × (x ≡ true)) ⊎ ((b ≡ false) × (y ≡ true))
if-true true x y e = inj₁ (refl , e)
if-true false x y e = inj₂ (refl , e)

-- ----------------------------------------------------------------------
-- * Cancellation, for matrix variables only
--
-- These are the only places where the associativity and unit laws of
-- Kopt.Descent are used. Every statement here is about variables, so
-- the conversion checker never looks inside a matrix.

module _ where

  cancel-left : (X Y A : Op) -> X * Y ≡ 1# -> X * (Y * A) ≡ A
  cancel-left X Y A h =
    trans (sym (mat-*-assoc X Y A))
          (trans (cong (λ m -> m * A) h) (mat-*-identityˡ A))

  cancel-right : (X Y A : Op) -> X * Y ≡ 1# -> (A * X) * Y ≡ A
  cancel-right X Y A h =
    trans (mat-*-assoc A X Y)
          (trans (cong (λ m -> A * m) h) (mat-*-identityʳ A))

  cancel-left3 : (X Y Z A : Op) -> X * (Y * Z) ≡ 1# -> X * (Y * (Z * A)) ≡ A
  cancel-left3 X Y Z A h =
    trans (cong (λ m -> X * m) (sym (mat-*-assoc Y Z A)))
    (trans (sym (mat-*-assoc X (Y * Z) A))
    (trans (cong (λ m -> m * A) h) (mat-*-identityˡ A)))

  cancel-right3 : (X Y Z A : Op) -> (X * Y) * Z ≡ 1# -> ((A * X) * Y) * Z ≡ A
  cancel-right3 X Y Z A h =
    trans (cong (λ m -> m * Z) (mat-*-assoc A X Y))
    (trans (mat-*-assoc A (X * Y) Z)
    (trans (cong (λ m -> A * m) h) (mat-*-identityʳ A)))

  -- Lemma II.8 with the lde of the left (resp. right) factor named.
  lde-mul-up : (M A : Op) (k : ℕ) -> lde M ≡ k -> lde (M * A) Nat.≤ k Nat.+ lde A
  lde-mul-up M A k h = subst (λ n -> lde (M * A) Nat.≤ n Nat.+ lde A) h (lde-*-≤ M A)

  lde-mul-up-r : (A M : Op) (k : ℕ) -> lde M ≡ k -> lde (A * M) Nat.≤ lde A Nat.+ k
  lde-mul-up-r A M k h = subst (λ n -> lde (A * M) Nat.≤ lde A Nat.+ n) h (lde-*-≤ A M)

  -- Remark II.10, the direction that needs the inverse: if a
  -- generalized permutation and a factor M of lde k undo the passage
  -- from B to A, then lde A ≤ k + lde B.
  lde-undo-left : (G : GP) (M A B : Op) (k : ℕ) ->
                  gp-mat G * (M * B) ≡ A -> lde M ≡ k -> lde A Nat.≤ k Nat.+ lde B
  lde-undo-left G M A B k e hM =
    subst (λ z -> lde z Nat.≤ k Nat.+ lde B) e
          (subst (λ n -> n Nat.≤ k Nat.+ lde B) (sym (lde-gp-left G (M * B)))
                 (lde-mul-up M B k hM))

  lde-undo-right : (G : GP) (M A B : Op) (k : ℕ) ->
                   (B * M) * gp-mat G ≡ A -> lde M ≡ k -> lde A Nat.≤ lde B Nat.+ k
  lde-undo-right G M A B k e hM =
    subst (λ z -> lde z Nat.≤ lde B Nat.+ k) e
          (subst (λ n -> n Nat.≤ lde B Nat.+ k) (sym (lde-gp-right (B * M) G))
                 (lde-mul-up-r B M k hM))

-- ----------------------------------------------------------------------
-- * Remark II.10 for a single K gate
--
-- K₁·K₁ = -i, so K₁⁻¹ = i·K₁: a K gate can be undone by another K gate
-- and a generalized permutation. Together with lde(K₁) = 1 and the
-- subadditivity of the lde (Lemma II.8) this gives both halves of
-- Remark II.10: one K gate changes the lde by at most one.

i-gp minus-i-gp : GP
i-gp = gperm id4p (ph1 , ph1 , ph1 , ph1) refl
minus-i-gp = gperm id4p (ph3 , ph3 , ph3 , ph3) refl

-- The three closed facts about concrete matrices.
private
  i-k1-k1 : gp-mat i-gp * (⟦ K₁ ⟧g * ⟦ K₁ ⟧g) ≡ 1#
  i-k1-k1 = ==⇒≡ refl

  k1-k1-i : (⟦ K₁ ⟧g * ⟦ K₁ ⟧g) * gp-mat i-gp ≡ 1#
  k1-k1-i = ==⇒≡ refl

  lde-K₁ : lde ⟦ K₁ ⟧g ≡ 1
  lde-K₁ = refl

-- Undoing a K gate, on the left and on the right.
K-undo-left : (A : Op) -> gp-mat i-gp * (⟦ K₁ ⟧g * (⟦ K₁ ⟧g * A)) ≡ A
K-undo-left A = cancel-left3 (gp-mat i-gp) ⟦ K₁ ⟧g ⟦ K₁ ⟧g A i-k1-k1

K-undo-right : (A : Op) -> ((A * ⟦ K₁ ⟧g) * ⟦ K₁ ⟧g) * gp-mat i-gp ≡ A
K-undo-right A = cancel-right3 ⟦ K₁ ⟧g ⟦ K₁ ⟧g (gp-mat i-gp) A k1-k1-i

lde-K-up : (A : Op) -> lde (⟦ K₁ ⟧g * A) Nat.≤ suc (lde A)
lde-K-up A = lde-mul-up ⟦ K₁ ⟧g A 1 lde-K₁

lde-K-down : (A : Op) -> lde A Nat.≤ suc (lde (⟦ K₁ ⟧g * A))
lde-K-down A = lde-undo-left i-gp ⟦ K₁ ⟧g A (⟦ K₁ ⟧g * A) 1 (K-undo-left A) lde-K₁

lde-K-up-r : (A : Op) -> lde (A * ⟦ K₁ ⟧g) Nat.≤ suc (lde A)
lde-K-up-r A = subst (λ n -> lde (A * ⟦ K₁ ⟧g) Nat.≤ n) (NatP.+-comm (lde A) 1)
                     (lde-mul-up-r A ⟦ K₁ ⟧g 1 lde-K₁)

lde-K-down-r : (A : Op) -> lde A Nat.≤ suc (lde (A * ⟦ K₁ ⟧g))
lde-K-down-r A = subst (λ n -> lde A Nat.≤ n) (NatP.+-comm (lde (A * ⟦ K₁ ⟧g)) 1)
                       (lde-undo-right i-gp ⟦ K₁ ⟧g A (A * ⟦ K₁ ⟧g) 1 (K-undo-right A) lde-K₁)

-- ----------------------------------------------------------------------
-- ** The lde along a list of steps

lde-step-up : (s : Step) (A : Op) -> lde (step-of s A) Nat.≤ step-kc s Nat.+ lde A
lde-step-up (gp-left G) A = NatP.≤-reflexive (lde-gp-left G A)
lde-step-up (gp-right G) A = NatP.≤-reflexive (lde-gp-right A G)
lde-step-up K-left A = lde-K-up A
lde-step-up K-right A = lde-K-up-r A

lde-step-down : (s : Step) (A : Op) -> lde A Nat.≤ step-kc s Nat.+ lde (step-of s A)
lde-step-down (gp-left G) A = NatP.≤-reflexive (sym (lde-gp-left G A))
lde-step-down (gp-right G) A = NatP.≤-reflexive (sym (lde-gp-right A G))
lde-step-down K-left A = lde-K-down A
lde-step-down K-right A = lde-K-down-r A

private
  shuffle : (a b c : ℕ) -> a Nat.+ (b Nat.+ c) ≡ (b Nat.+ a) Nat.+ c
  shuffle a b c = trans (sym (NatP.+-assoc a b c)) (cong (λ n -> n Nat.+ c) (NatP.+-comm a b))

lde-run-up : (ss : List Step) (A : Op) -> lde (run ss A) Nat.≤ steps-kc ss Nat.+ lde A
lde-run-up [] A = NatP.≤-refl
lde-run-up (s ∷ ss) A =
  NatP.≤-trans (NatP.≤-trans (lde-run-up ss (step-of s A))
                             (NatP.+-monoʳ-≤ (steps-kc ss) (lde-step-up s A)))
               (NatP.≤-reflexive (shuffle (steps-kc ss) (step-kc s) (lde A)))

lde-run-down : (ss : List Step) (A : Op) -> lde A Nat.≤ steps-kc ss Nat.+ lde (run ss A)
lde-run-down [] A = NatP.≤-refl
lde-run-down (s ∷ ss) A =
  NatP.≤-trans (NatP.≤-trans (lde-step-down s A)
                             (NatP.+-monoʳ-≤ (step-kc s) (lde-run-down ss (step-of s A))))
               (NatP.≤-reflexive
                 (sym (NatP.+-assoc (step-kc s) (steps-kc ss) (lde (run ss (step-of s A))))))

-- ----------------------------------------------------------------------
-- * Descents are invertible
--
-- Every step can be undone by a list of steps with the same K-count,
-- so a K-count-n descent from A to B gives a K-count-n descent from B
-- to A. This is what turns Lemma V.6 ("a K-count-1 0-descent from
-- pattern (vi) cannot reach (ii) or (v)") into the statement the
-- induction needs ("a K-count-1 0-descent from (ii) or (v) cannot
-- reach (vi)").

step-inv : Step -> List Step
step-inv (gp-left G) = gp-left (gp-inverse G) ∷ []
step-inv (gp-right G) = gp-right (gp-inverse G) ∷ []
step-inv K-left = K-left ∷ gp-left i-gp ∷ []
step-inv K-right = K-right ∷ gp-right i-gp ∷ []

steps-inv : List Step -> List Step
steps-inv [] = []
steps-inv (s ∷ ss) = steps-inv ss ++ step-inv s

private
  step-inv-run : (s : Step) (A : Op) -> run (step-inv s) (step-of s A) ≡ A
  step-inv-run (gp-left G) A =
    cancel-left (gp-mat (gp-inverse G)) (gp-mat G) A (gp-inverse-left G)
  step-inv-run (gp-right G) A =
    cancel-right (gp-mat G) (gp-mat (gp-inverse G)) A (gp-inverse-right G)
  step-inv-run K-left A = K-undo-left A
  step-inv-run K-right A = K-undo-right A

  step-inv-kc : (s : Step) -> steps-kc (step-inv s) ≡ step-kc s
  step-inv-kc (gp-left G) = refl
  step-inv-kc (gp-right G) = refl
  step-inv-kc K-left = refl
  step-inv-kc K-right = refl

steps-inv-run : (ss : List Step) (A : Op) -> run (steps-inv ss) (run ss A) ≡ A
steps-inv-run [] A = refl
steps-inv-run (s ∷ ss) A = begin
  run (steps-inv ss ++ step-inv s) (run ss (step-of s A))
    ≡⟨ run-++ (steps-inv ss) (step-inv s) (run ss (step-of s A)) ⟩
  run (step-inv s) (run (steps-inv ss) (run ss (step-of s A)))
    ≡⟨ cong (run (step-inv s)) (steps-inv-run ss (step-of s A)) ⟩
  run (step-inv s) (step-of s A)
    ≡⟨ step-inv-run s A ⟩
  A ∎
  where open ≡-Reasoning

steps-inv-kc : (ss : List Step) -> steps-kc (steps-inv ss) ≡ steps-kc ss
steps-inv-kc [] = refl
steps-inv-kc (s ∷ ss) =
  trans (steps-kc-++ (steps-inv ss) (step-inv s))
        (trans (cong₂ Nat._+_ (steps-inv-kc ss) (step-inv-kc s))
               (NatP.+-comm (steps-kc ss) (step-kc s)))

-- ----------------------------------------------------------------------
-- * Lemma IV.1: pattern (i) and lde 0
--
-- "A has pattern (i) if and only if lde(A) = 0" (Lemma IV.1). This is
-- the one fact about the *function* patof that the induction needs and
-- that cannot be established here: patof is defined in Kopt.Patterns
-- by a `with` on a private helper, so even its definitional half ("at
-- lde 0 the search of lemma-six either finds pattern (i) or fails")
-- cannot be proved outside that module. It is therefore a hypothesis,
-- threaded through everything below.
Lemma-IV-1-I : Set
Lemma-IV-1-I = (A : Op) -> (lde A ≡ 0 -> patof A ≡ just I) × (patof A ≡ just I -> lde A ≡ 0)
