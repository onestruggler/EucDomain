-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- Lemma V.7 (the complete path descent is K-optimal) and, with it, the
-- K-optimality half of Corollary V.8.
--
-- This is the induction of the paper, carried out in full. It proves
--
--   Lemma V.4  ∧  Lemma V.6  ∧  Lemma IV.1 (pattern (i) ⟺ lde 0)
--       ⟹  Lemma V.7,
--
-- so that Corollary V.8 no longer depends on Lemma V.7 itself.
-- Everything else it uses is proved: Remark II.10 in both directions
-- and the invertibility of a descent (Kopt.OptSteps), and the
-- arithmetic of Table II (Kopt.OptPotential).
--
-- The proof has two halves, run on the potential
-- pot(A) = 2·lde(A) - rank(pat(A)) of Kopt.OptPotential.
--
--  * Every descent of A that reaches lde 0 uses at least pot(A) K
--    gates (LowerBound.descent-lower-bound). Induction on the number
--    of K gates: split off the first K gate together with the
--    generalized permutations before it. That is a K-count-1 step, so
--    Lemma V.4 (if it decreases the lde), Lemma V.6 (if it preserves
--    it) or nothing at all (if it increases it) bounds the rank of the
--    target, and the potential drops by at most one.
--  * The complete path descent of A uses at most pot(A) K gates
--    (UpperBound.path-descent-upper-bound): every edge of Figure 1 is
--    exact.

{-# OPTIONS --without-K --safe #-}

module Kopt.OptInduction where

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
open import Kopt.OptSteps
open import Kopt.OptPotential

-- ----------------------------------------------------------------------
-- * Lemma V.6, reversed
--
-- A K-count-1 0-descent from pattern (ii) or (v) cannot reach pattern
-- (vi): invert the descent and apply Lemma V.6.

lemma-V-6-rev : Lemma-V-6 -> (A : Op) (ss : List Step) -> steps-kc ss ≡ 1 ->
                lde (run ss A) ≡ lde A -> patof (run ss A) ≡ just VI ->
                ¬ (patof A ≡ just II) × ¬ (patof A ≡ just V)
lemma-V-6-rev v6 A ss k1 ldeeq pVI = back (v6 (run ss A) (steps-inv ss) k1' ldeeq' pVI)
  where
    k1' : steps-kc (steps-inv ss) ≡ 1
    k1' = trans (steps-inv-kc ss) k1
    ldeeq' : lde (run (steps-inv ss) (run ss A)) ≡ lde (run ss A)
    ldeeq' = trans (cong lde (steps-inv-run ss A)) (sym ldeeq)
    back : ¬ (patof (run (steps-inv ss) (run ss A)) ≡ just II)
           × ¬ (patof (run (steps-inv ss) (run ss A)) ≡ just V) ->
           ¬ (patof A ≡ just II) × ¬ (patof A ≡ just V)
    back (h1 , h2) =
      subst (λ M -> ¬ (patof M ≡ just II)) (steps-inv-run ss A) h1 ,
      subst (λ M -> ¬ (patof M ≡ just V)) (steps-inv-run ss A) h2

-- ----------------------------------------------------------------------
-- * Splitting a descent at its first K gate

data FirstK : List Step -> Set where
  no-K : (ts : List Step) -> steps-kc ts ≡ 0 -> FirstK ts
  yes-K : (pre : List Step) (s : Step) (post : List Step) ->
          steps-kc pre ≡ 0 -> step-kc s ≡ 1 -> FirstK (pre ++ s ∷ post)

private
  cons-firstK : (g : Step) -> step-kc g ≡ 0 -> (ts : List Step) -> FirstK ts -> FirstK (g ∷ ts)
  cons-firstK g hg ts (no-K .ts e) =
    no-K (g ∷ ts) (trans (cong (λ n -> n Nat.+ steps-kc ts) hg) e)
  cons-firstK g hg _ (yes-K pre s post e1 e2) =
    yes-K (g ∷ pre) s post (trans (cong (λ n -> n Nat.+ steps-kc pre) hg) e1) e2

first-K : (ts : List Step) -> FirstK ts
first-K [] = no-K [] refl
first-K (gp-left G ∷ ts) = cons-firstK (gp-left G) refl ts (first-K ts)
first-K (gp-right G ∷ ts) = cons-firstK (gp-right G) refl ts (first-K ts)
first-K (K-left ∷ ts) = yes-K [] K-left ts refl refl
first-K (K-right ∷ ts) = yes-K [] K-right ts refl refl

-- ----------------------------------------------------------------------
-- * The lower bound: every descent to lde 0 costs at least pot(A)

module LowerBound (v4 : Lemma-V-4) (v6 : Lemma-V-6) (iv1 : Lemma-IV-1-I) where

  private
    -- The 0-descent case.
    zero-case : (A : Op) (ss : List Step) -> steps-kc ss ≡ 1 -> lde (run ss A) ≡ lde A ->
                pot (patof A) (lde A) Nat.≤ suc (pot (patof (run ss A)) (lde (run ss A)))
    zero-case A ss k1 e = body (patof A) refl
      where
        C : Op
        C = run ss A
        generic : (p : Maybe SixCases) -> pat-rank (patof C) Nat.≤ suc (pat-rank p) ->
                  pot p (lde A) Nat.≤ suc (pot (patof C) (lde C))
        generic p h = subst (λ n -> pot p (lde A) Nat.≤ suc (pot (patof C) n)) (sym e)
                            (pot-keep p (patof C) (lde A) h)
        big : (p : Maybe SixCases) -> 1 Nat.≤ pat-rank p ->
              pot p (lde A) Nat.≤ suc (pot (patof C) (lde C))
        big p h = generic p (NatP.≤-trans (rank≤2 (patof C)) (s≤s h))
        notVI : (p : Maybe SixCases) -> ¬ (patof C ≡ just VI) ->
                pot p (lde A) Nat.≤ suc (pot (patof C) (lde C))
        notVI p h = generic p (NatP.≤-trans (rank-not-VI (patof C) h) (s≤s z≤n))
        body : (p : Maybe SixCases) -> patof A ≡ p ->
               pot p (lde A) Nat.≤ suc (pot (patof C) (lde C))
        body nothing eA = big nothing NatP.≤-refl
        body (just III) eA = big (just III) NatP.≤-refl
        body (just IV) eA = big (just IV) NatP.≤-refl
        body (just IVt) eA = big (just IVt) NatP.≤-refl
        body (just VI) eA = big (just VI) (s≤s z≤n)
        body (just II) eA = notVI (just II) (λ hVI -> proj₁ (lemma-V-6-rev v6 A ss k1 e hVI) eA)
        body (just V) eA = notVI (just V) (λ hVI -> proj₂ (lemma-V-6-rev v6 A ss k1 e hVI) eA)
        body (just I) eA =
          subst (λ n -> pot (just I) n Nat.≤ suc (pot (patof C) (lde C))) (sym (proj₂ (iv1 A) eA))
                (subst (λ n -> n Nat.≤ suc (pot (patof C) (lde C))) (sym (pot-at-0 (just I))) z≤n)

  -- A K-count-1 step lowers the potential by at most one.
  step-pot : (A : Op) (ss : List Step) -> steps-kc ss ≡ 1 ->
             pot (patof A) (lde A) Nat.≤ suc (pot (patof (run ss A)) (lde (run ss A)))
  step-pot A ss k1 with NatP.<-cmp (lde (run ss A)) (lde A)
  -- a 1-descent: Lemma V.4 forces an undashed edge of Figure 1
  ... | tri< lt _ _ =
        subst (λ n -> pot (patof A) n Nat.≤ suc (pot (patof (run ss A)) (lde (run ss A))))
              (sym down)
              (pot-drop (patof A) (patof (run ss A)) (lde (run ss A))
                        (rank-drop-of (patof A) (patof (run ss A)) (v4 A ss k1 down)))
    where
      up : lde A Nat.≤ suc (lde (run ss A))
      up = subst (λ n -> lde A Nat.≤ n Nat.+ lde (run ss A)) k1 (lde-run-down ss A)
      down : suc (lde (run ss A)) ≡ lde A
      down = NatP.≤-antisym lt up
  -- a 0-descent
  ... | tri≈ _ eq _ = zero-case A ss k1 eq
  -- a 1-ascent
  ... | tri> _ _ gt =
        subst (λ n -> pot (patof A) (lde A) Nat.≤ suc (pot (patof (run ss A)) n))
              (sym up') (pot-ascent (patof A) (patof (run ss A)) (lde A))
    where
      down' : lde (run ss A) Nat.≤ suc (lde A)
      down' = subst (λ n -> lde (run ss A) Nat.≤ n Nat.+ lde A) k1 (lde-run-up ss A)
      up' : lde (run ss A) ≡ suc (lde A)
      up' = NatP.≤-antisym down' gt

  private
    no-K-lde : (ts : List Step) -> steps-kc ts ≡ 0 -> (A : Op) ->
               lde (run ts A) ≡ 0 -> lde A ≡ 0
    no-K-lde ts z A h = NatP.n≤0⇒n≡0
      (subst (λ n -> lde A Nat.≤ n) (trans (cong (λ n -> n Nat.+ lde (run ts A)) z) h)
             (lde-run-down ts A))

    kc-split : (pre : List Step) (s : Step) (post : List Step) ->
               steps-kc pre ≡ 0 -> step-kc s ≡ 1 ->
               steps-kc (pre ++ s ∷ post) ≡ suc (steps-kc post)
    kc-split pre s post z1 z2 =
      trans (steps-kc-++ pre (s ∷ post))
            (trans (cong (λ n -> n Nat.+ (step-kc s Nat.+ steps-kc post)) z1)
                   (cong (λ n -> n Nat.+ steps-kc post) z2))

    -- The first argument is fuel: any bound on the number of K gates.
    descent-lb : (k : ℕ) (A : Op) (ts : List Step) -> FirstK ts -> steps-kc ts Nat.≤ k ->
                 lde (run ts A) ≡ 0 -> pot (patof A) (lde A) Nat.≤ steps-kc ts
    descent-lb k A ts (no-K .ts z) le h =
      subst (λ n -> n Nat.≤ steps-kc ts)
            (sym (trans (cong (pot (patof A)) (no-K-lde ts z A h)) (pot-at-0 (patof A)))) z≤n
    descent-lb zero A _ (yes-K pre s post z1 z2) le h =
      ⊥-elim (absurd (subst (λ n -> n Nat.≤ 0) (kc-split pre s post z1 z2) le))
      where
        absurd : suc (steps-kc post) Nat.≤ 0 -> ⊥
        absurd ()
    descent-lb (suc k) A _ (yes-K pre s post z1 z2) le h =
      NatP.≤-trans (NatP.≤-trans (step-pot A ss1 kc1) (s≤s ih))
                   (NatP.≤-reflexive (sym (kc-split pre s post z1 z2)))
      where
        ss1 : List Step
        ss1 = pre ++ s ∷ []
        C : Op
        C = run ss1 A
        kc1 : steps-kc ss1 ≡ 1
        kc1 = trans (steps-kc-++ pre (s ∷ []))
                    (trans (cong (λ n -> n Nat.+ (step-kc s Nat.+ 0)) z1)
                           (trans (NatP.+-identityʳ (step-kc s)) z2))
        inner : run ss1 A ≡ step-of s (run pre A)
        inner = run-++ pre (s ∷ []) A
        split : run (pre ++ s ∷ post) A ≡ run post C
        split = trans (run-++ pre (s ∷ post) A)
                      (cong (λ M -> run post M) (sym inner))
        h' : lde (run post C) ≡ 0
        h' = trans (cong lde (sym split)) h
        le' : steps-kc post Nat.≤ k
        le' = NatP.≤-pred (subst (λ n -> n Nat.≤ suc k) (kc-split pre s post z1 z2) le)
        ih : pot (patof C) (lde C) Nat.≤ steps-kc post
        ih = descent-lb k C post (first-K post) le' h'

  descent-lower-bound : (A : Op) (ts : List Step) -> lde (run ts A) ≡ 0 ->
                        potA A Nat.≤ steps-kc ts
  descent-lower-bound A ts h = descent-lb (steps-kc ts) A ts (first-K ts) NatP.≤-refl h

-- ----------------------------------------------------------------------
-- * The upper bound: the complete path descent costs at most pot(A)
--
-- Every edge of Figure 1 is exact: it costs exactly the drop in the
-- potential (fig1-step-pot of Kopt.OptPotential).

module UpperBound (iv1 : Lemma-IV-1-I) where

  private
    rank-le-2l : (C : Op) -> pat-rank (patof C) Nat.≤ 2 Nat.* lde C
    rank-le-2l C with lde C in e
    ... | zero = subst (λ p -> pat-rank p Nat.≤ 0) (sym (proj₁ (iv1 C) e)) z≤n
    ... | suc n = NatP.≤-trans (rank≤2 (patof C)) two≤
      where
        two≤ : 2 Nat.≤ 2 Nat.* suc n
        two≤ = subst (λ m -> 2 Nat.≤ m) (sym (two*suc n)) (s≤s (s≤s z≤n))

  path-step-pot : (A : Op) (ss : List Step) -> IsPathStep A ss ->
                  steps-kc ss Nat.+ potA (run ss A) Nat.≤ potA A
  path-step-pot A ss hstep =
    fig1-step-pot (patof A) (patof (run ss A)) (lde A) (lde (run ss A)) (steps-kc ss)
                  (λ z -> proj₁ (iv1 A) z) (rank-le-2l (run ss A)) hstep

  path-descent-pot : (A : Op) (ss : List Step) -> IsPathDescent A ss ->
                     steps-kc ss Nat.+ potA (run ss A) Nat.≤ potA A
  path-descent-pot A [] (path-nil .A) = NatP.≤-refl
  path-descent-pot A _ (path-cons .A ss ts hstep hrest) =
    subst (λ n -> n Nat.≤ potA A) (sym lhs)
          (NatP.≤-trans (NatP.+-monoʳ-≤ (steps-kc ss) (path-descent-pot (run ss A) ts hrest))
                        (path-step-pot A ss hstep))
    where
      lhs : steps-kc (ss ++ ts) Nat.+ potA (run (ss ++ ts) A)
              ≡ steps-kc ss Nat.+ (steps-kc ts Nat.+ potA (run ts (run ss A)))
      lhs = trans (cong₂ Nat._+_ (steps-kc-++ ss ts) (cong potA (run-++ ss ts A)))
                  (NatP.+-assoc (steps-kc ss) (steps-kc ts) (potA (run ts (run ss A))))

  path-descent-upper-bound : (A : Op) (ss : List Step) -> IsCompletePathDescent A ss ->
                             steps-kc ss Nat.≤ potA A
  path-descent-upper-bound A ss (hpath , hlde) =
    subst (λ n -> n Nat.≤ potA A) fix (path-descent-pot A ss hpath)
    where
      fix : steps-kc ss Nat.+ potA (run ss A) ≡ steps-kc ss
      fix = trans (cong (λ n -> steps-kc ss Nat.+ n)
                        (trans (cong (pot (patof (run ss A))) hlde) (pot-at-0 (patof (run ss A)))))
                  (NatP.+-identityʳ (steps-kc ss))

-- ----------------------------------------------------------------------
-- * Lemma V.7

-- The complete path descent is K-optimal.
lemma-V-7 : Lemma-V-4 -> Lemma-V-6 -> Lemma-IV-1-I -> Lemma-V-7
lemma-V-7 v4 v6 iv1 A ss cpd = (ss , NatP.≤-refl , refl) , least
  where
    open LowerBound v4 v6 iv1
    open UpperBound iv1
    upper : steps-kc ss Nat.≤ potA A
    upper = path-descent-upper-bound A ss cpd
    least : (m : ℕ) -> HasDescentKCount A (lde (run ss A)) m -> steps-kc ss Nat.≤ m
    least m (ts , hts , kts) = NatP.≤-trans upper (NatP.≤-trans lower (NatP.≤-reflexive kts))
      where
        zero-lde : lde (run ts A) ≡ 0
        zero-lde = NatP.n≤0⇒n≡0 (subst (λ n -> lde (run ts A) Nat.≤ n) (proj₂ cpd) hts)
        lower : potA A Nat.≤ steps-kc ts
        lower = descent-lower-bound A ts zero-lde

-- ----------------------------------------------------------------------
-- * Corollary V.8, K-optimality, no longer assuming Lemma V.7
--
-- What remains are Lemma V.4 and Lemma V.6 -- the two finite,
-- residue-level statements of Section V -- the pattern-(i)
-- characterisation of Lemma IV.1, and the three algorithmic facts
-- about synth (that the descent it realises is a complete path descent
-- with K-count prkc(A), and that its output is a circuit for A with
-- that many K gates).
cor-V-8-K-optimal′ : Lemma-V-4 -> Lemma-V-6 -> Lemma-IV-1-I ->
                     (A : Op) (ss : List Step) ->
                     IsCompletePathDescent A ss -> steps-kc ss ≡ prkc A ->
                     HasKCount A (prkc A) -> IsMinimalKCount A (prkc A)
cor-V-8-K-optimal′ v4 v6 iv1 = cor-V-8-K-optimal (lemma-V-7 v4 v6 iv1)
