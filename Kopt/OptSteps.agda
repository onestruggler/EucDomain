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
-- Split off from Kopt.OptInduction so that each module stays inside
-- the twenty minute limit of agda-check.sh.

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
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Patterns using (SixCases ; I ; II ; III ; IV ; IVt ; V ; VI ; patof ; DecEqSixCases)
open import Kopt.Synth using (prkc)
open import Kopt.Descent
open import Kopt.Optimality

-- ----------------------------------------------------------------------
-- * Small helpers

false-true : false ≡ true -> ⊥
false-true ()

just-inj : {A : Set} {x y : A} -> _≡_ {A = Maybe A} (just x) (just y) -> x ≡ y
just-inj refl = refl

-- Case analysis on a boolean test that guards an if.
if-true : (b : Bool) {x y : Bool} -> (if b then x else y) ≡ true ->
          ((b ≡ true) × (x ≡ true)) ⊎ ((b ≡ false) × (y ≡ true))
if-true true e = inj₁ (refl , e)
if-true false e = inj₂ (refl , e)

-- ----------------------------------------------------------------------
-- * Remark II.10 for a single K gate
--
-- K₁·K₁ = -i, so K₁⁻¹ = i·K₁ and a K gate can be undone by another K
-- gate and a generalized permutation. Together with lde(K₁) = 1 and
-- the subadditivity of the lde (Lemma II.8) this gives both halves of
-- Remark II.10: one K gate changes the lde by at most one.

i-gp minus-i-gp : GP
i-gp = gperm id4p (ph1 , ph1 , ph1 , ph1) refl
minus-i-gp = gperm id4p (ph3 , ph3 , ph3 , ph3) refl

private
  k1k1 : ⟦ K₁ ⟧g * ⟦ K₁ ⟧g ≡ gp-mat minus-i-gp
  k1k1 = ==⇒≡ refl

  -- i·(-i) = 1 and (-i)·i = 1, through the group law of the
  -- generalized permutations rather than by multiplying the matrices.
  i·-i : gp-mat i-gp * gp-mat minus-i-gp ≡ 1#
  i·-i = trans (gp-mat-comp i-gp minus-i-gp) gp-one-mat

  -i·i : gp-mat minus-i-gp * gp-mat i-gp ≡ 1#
  -i·i = trans (gp-mat-comp minus-i-gp i-gp) gp-one-mat

  lde-K₁ : lde ⟦ K₁ ⟧g ≡ 1
  lde-K₁ = refl

-- Undoing a K gate, on the left and on the right.
K-undo-left : (A : Op) -> gp-mat i-gp * (⟦ K₁ ⟧g * (⟦ K₁ ⟧g * A)) ≡ A
K-undo-left A =
  trans (cong (λ m -> gp-mat i-gp * m) (sym (mat-*-assoc ⟦ K₁ ⟧g ⟦ K₁ ⟧g A)))
  (trans (cong (λ m -> gp-mat i-gp * (m * A)) k1k1)
  (trans (sym (mat-*-assoc (gp-mat i-gp) (gp-mat minus-i-gp) A))
  (trans (cong (λ m -> m * A) i·-i) (mat-*-identityˡ A))))

K-undo-right : (A : Op) -> ((A * ⟦ K₁ ⟧g) * ⟦ K₁ ⟧g) * gp-mat i-gp ≡ A
K-undo-right A =
  trans (cong (λ m -> m * gp-mat i-gp) (mat-*-assoc A ⟦ K₁ ⟧g ⟦ K₁ ⟧g))
  (trans (cong (λ m -> (A * m) * gp-mat i-gp) k1k1)
  (trans (mat-*-assoc A (gp-mat minus-i-gp) (gp-mat i-gp))
  (trans (cong (λ m -> A * m) -i·i) (mat-*-identityʳ A))))

lde-K-up : (A : Op) -> lde (⟦ K₁ ⟧g * A) Nat.≤ suc (lde A)
lde-K-up A = subst (λ n -> lde (⟦ K₁ ⟧g * A) Nat.≤ n Nat.+ lde A) lde-K₁ (lde-*-≤ ⟦ K₁ ⟧g A)

lde-K-down : (A : Op) -> lde A Nat.≤ suc (lde (⟦ K₁ ⟧g * A))
lde-K-down A = subst (λ z -> lde z Nat.≤ suc (lde (⟦ K₁ ⟧g * A))) (K-undo-left A) step
  where
    step : lde (gp-mat i-gp * (⟦ K₁ ⟧g * (⟦ K₁ ⟧g * A))) Nat.≤ suc (lde (⟦ K₁ ⟧g * A))
    step = subst (λ n -> n Nat.≤ suc (lde (⟦ K₁ ⟧g * A)))
                 (sym (lde-gp-left i-gp (⟦ K₁ ⟧g * (⟦ K₁ ⟧g * A))))
                 (lde-K-up (⟦ K₁ ⟧g * A))

lde-K-up-r : (A : Op) -> lde (A * ⟦ K₁ ⟧g) Nat.≤ suc (lde A)
lde-K-up-r A =
  subst (λ n -> lde (A * ⟦ K₁ ⟧g) Nat.≤ n) (NatP.+-comm (lde A) 1)
        (subst (λ n -> lde (A * ⟦ K₁ ⟧g) Nat.≤ lde A Nat.+ n) lde-K₁ (lde-*-≤ A ⟦ K₁ ⟧g))

lde-K-down-r : (A : Op) -> lde A Nat.≤ suc (lde (A * ⟦ K₁ ⟧g))
lde-K-down-r A = subst (λ z -> lde z Nat.≤ suc (lde (A * ⟦ K₁ ⟧g))) (K-undo-right A) step
  where
    step : lde (((A * ⟦ K₁ ⟧g) * ⟦ K₁ ⟧g) * gp-mat i-gp) Nat.≤ suc (lde (A * ⟦ K₁ ⟧g))
    step = subst (λ n -> n Nat.≤ suc (lde (A * ⟦ K₁ ⟧g)))
                 (sym (lde-gp-right ((A * ⟦ K₁ ⟧g) * ⟦ K₁ ⟧g) i-gp))
                 (lde-K-up-r (A * ⟦ K₁ ⟧g))

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
               (NatP.≤-reflexive (sym (NatP.+-assoc (step-kc s) (steps-kc ss) (lde (run ss (step-of s A))))))

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
    trans (sym (mat-*-assoc (gp-mat (gp-inverse G)) (gp-mat G) A))
          (trans (cong (λ m -> m * A) (gp-inverse-left G)) (mat-*-identityˡ A))
  step-inv-run (gp-right G) A =
    trans (mat-*-assoc A (gp-mat G) (gp-mat (gp-inverse G)))
          (trans (cong (λ m -> A * m) (gp-inverse-right G)) (mat-*-identityʳ A))
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
