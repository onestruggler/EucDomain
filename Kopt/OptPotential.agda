-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the potential of Table II and its behaviour along the edges of
-- Figure 1. Table II (Lemma IV.7) gives the K-count of the complete
-- path descent of an operator of lde l as a function of its pattern:
--
--   (i) 0, (ii) 2l, (iii) 2l-1, (iv) 2l-1, (iv)ᵀ 2l-1, (v) 2l, (vi) 2l-2,
--
-- that is, 2l - rank(p) for a rank in {0,1,2}. The induction of
-- Kopt.OptInduction runs on pot(A) = 2·lde(A) - rank(pat(A)); the two
-- results proved here are that one K gate lowers the potential by at
-- most one (pot-drop, pot-keep, pot-ascent, together with the ranks
-- along the edges of Figure 1) and that a step of a path descent
-- lowers it by exactly its K-count (fig1-step-pot).
--
-- Two conventions are forced by the induction and are harmless:
--
--  * rank (i) = 0, i.e. the potential of pattern (i) is 2l and not 0.
--    Only l = 0 ever occurs (Lemma IV.1), where the two agree; the
--    value 2l is what makes the edge (iii) → (i) of Figure 1 exact.
--  * rank(nothing) = 1, for matrices that have no pattern at all (the
--    ones that are not two-qubit Clifford+CS operators). No hypothesis
--    is needed about them: 1 is exactly the rank that makes every
--    transition into and out of them harmless.
--
-- Split off from Kopt.OptInduction so that each module stays inside
-- the twenty minute limit of agda-check.sh.

{-# OPTIONS --without-K --safe #-}

module Kopt.OptPotential where

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

-- ----------------------------------------------------------------------
-- * The potential (Table II)

-- The rank of a pattern: an operator of lde l and pattern p has
-- potential 2l - rank(p).
pat-rank : Maybe SixCases -> ℕ
pat-rank nothing = 1
pat-rank (just I) = 0
pat-rank (just II) = 0
pat-rank (just III) = 1
pat-rank (just IV) = 1
pat-rank (just IVt) = 1
pat-rank (just V) = 0
pat-rank (just VI) = 2

pot : Maybe SixCases -> ℕ -> ℕ
pot p l = 2 Nat.* l ∸ pat-rank p

potA : Op -> ℕ
potA A = pot (patof A) (lde A)

rank≤2 : (p : Maybe SixCases) -> pat-rank p Nat.≤ 2
rank≤2 nothing = s≤s z≤n
rank≤2 (just I) = z≤n
rank≤2 (just II) = z≤n
rank≤2 (just III) = s≤s z≤n
rank≤2 (just IV) = s≤s z≤n
rank≤2 (just IVt) = s≤s z≤n
rank≤2 (just V) = z≤n
rank≤2 (just VI) = NatP.≤-refl

rank-not-VI : (q : Maybe SixCases) -> ¬ (q ≡ just VI) -> pat-rank q Nat.≤ 1
rank-not-VI nothing _ = NatP.≤-refl
rank-not-VI (just I) _ = z≤n
rank-not-VI (just II) _ = z≤n
rank-not-VI (just III) _ = NatP.≤-refl
rank-not-VI (just IV) _ = NatP.≤-refl
rank-not-VI (just IVt) _ = NatP.≤-refl
rank-not-VI (just V) _ = z≤n
rank-not-VI (just VI) h = ⊥-elim (h refl)

-- The potential at lde 0 is 0, whatever the pattern.
pot-at-0 : (p : Maybe SixCases) -> pot p 0 ≡ 0
pot-at-0 p = NatP.0∸n≡0 (pat-rank p)

private
  n≤suc-pred : (n : ℕ) -> n Nat.≤ suc (n ∸ 1)
  n≤suc-pred n = NatP.m≤n+m∸n n 1

  pred≡ : (n b : ℕ) -> (n ∸ b) ∸ 1 ≡ n ∸ suc b
  pred≡ n b = trans (NatP.∸-+-assoc n b 1) (cong (λ m -> n ∸ m) (NatP.+-comm b 1))

  -- n - a ≤ suc (n - suc a).
  ∸-suc-step : (n a : ℕ) -> n ∸ a Nat.≤ suc (n ∸ suc a)
  ∸-suc-step n a = subst (λ z -> n ∸ a Nat.≤ suc z) (pred≡ n a) (n≤suc-pred (n ∸ a))

  -- suc n - b ≤ suc (n - b).
  suc∸ : (n b : ℕ) -> suc n ∸ b Nat.≤ suc (n ∸ b)
  suc∸ n zero = NatP.≤-refl
  suc∸ n (suc b) = ∸-suc-step n b

two*suc : (l : ℕ) -> 2 Nat.* suc l ≡ suc (suc (2 Nat.* l))
two*suc l = NatP.*-suc 2 l

-- ----------------------------------------------------------------------
-- ** One K gate lowers the potential by at most one
--
-- The three cases: a 1-descent (the pat-rank drops by one, along an
-- undashed edge of Figure 1), a 0-descent (the pat-rank of the target is
-- at most one more than that of the source) and a 1-ascent (nothing is
-- needed).

pot-drop : (p q : Maybe SixCases) (l' : ℕ) -> pat-rank p ≡ suc (pat-rank q) ->
           pot p (suc l') Nat.≤ suc (pot q l')
pot-drop p q l' e =
  subst (λ n -> n ∸ pat-rank p Nat.≤ suc (2 Nat.* l' ∸ pat-rank q)) (sym (two*suc l'))
        (subst (λ r -> suc (suc (2 Nat.* l')) ∸ r Nat.≤ suc (2 Nat.* l' ∸ pat-rank q))
               (sym e) (suc∸ (2 Nat.* l') (pat-rank q)))

pot-keep : (p q : Maybe SixCases) (l : ℕ) -> pat-rank q Nat.≤ suc (pat-rank p) ->
           pot p l Nat.≤ suc (pot q l)
pot-keep p q l h =
  NatP.≤-trans (∸-suc-step (2 Nat.* l) (pat-rank p))
               (s≤s (NatP.∸-monoʳ-≤ (2 Nat.* l) h))

pot-ascent : (p q : Maybe SixCases) (l : ℕ) -> pot p l Nat.≤ suc (pot q (suc l))
pot-ascent p q l =
  NatP.≤-trans (NatP.m∸n≤m (2 Nat.* l) (pat-rank p))
               (NatP.≤-trans (NatP.n≤1+n (2 Nat.* l)) (s≤s lower))
  where
    lower : 2 Nat.* l Nat.≤ 2 Nat.* suc l ∸ pat-rank q
    lower = subst (λ n -> 2 Nat.* l Nat.≤ n ∸ pat-rank q) (sym (two*suc l))
                  (NatP.∸-monoʳ-≤ (suc (suc (2 Nat.* l))) (rank≤2 q))

-- ----------------------------------------------------------------------
-- ** The ranks along the edges of Figure 1

rank-drop : (s t : SixCases) -> fig1-drop s t ≡ true -> pat-rank (just s) ≡ suc (pat-rank (just t))
rank-drop I t ()
rank-drop II t ()
rank-drop III I _ = refl
rank-drop III II ()
rank-drop III III ()
rank-drop III IV ()
rank-drop III IVt ()
rank-drop III V ()
rank-drop III VI ()
rank-drop IV I ()
rank-drop IV II _ = refl
rank-drop IV III ()
rank-drop IV IV ()
rank-drop IV IVt ()
rank-drop IV V _ = refl
rank-drop IV VI ()
rank-drop IVt I ()
rank-drop IVt II _ = refl
rank-drop IVt III ()
rank-drop IVt IV ()
rank-drop IVt IVt ()
rank-drop IVt V _ = refl
rank-drop IVt VI ()
rank-drop V t ()
rank-drop VI I ()
rank-drop VI II ()
rank-drop VI III _ = refl
rank-drop VI IV _ = refl
rank-drop VI IVt _ = refl
rank-drop VI V ()
rank-drop VI VI ()

rank-drop-of : (p q : Maybe SixCases) -> fig1-drop-of p q ≡ true -> pat-rank p ≡ suc (pat-rank q)
rank-drop-of nothing q ()
rank-drop-of (just s) nothing ()
rank-drop-of (just s) (just t) e = rank-drop s t e

-- Along a dashed edge the pat-rank increases by one instead.
rank-keep : (s t : SixCases) -> fig1-keep s t ≡ true -> pat-rank (just t) ≡ suc (pat-rank (just s))
rank-keep I t ()
rank-keep II I ()
rank-keep II II ()
rank-keep II III ()
rank-keep II IV _ = refl
rank-keep II IVt _ = refl
rank-keep II V ()
rank-keep II VI ()
rank-keep III I ()
rank-keep III II ()
rank-keep III III ()
rank-keep III IV ()
rank-keep III IVt ()
rank-keep III V ()
rank-keep III VI _ = refl
rank-keep IV t ()
rank-keep IVt t ()
rank-keep V I ()
rank-keep V II ()
rank-keep V III ()
rank-keep V IV _ = refl
rank-keep V IVt _ = refl
rank-keep V V ()
rank-keep V VI ()
rank-keep VI t ()

rank-keep-src : (s t : SixCases) -> fig1-keep s t ≡ true -> pat-rank (just s) Nat.≤ 1
rank-keep-src I t ()
rank-keep-src II t _ = z≤n
rank-keep-src III t _ = NatP.≤-refl
rank-keep-src IV t ()
rank-keep-src IVt t ()
rank-keep-src V t _ = z≤n
rank-keep-src VI t ()

-- Pattern (i) is not the source of any edge of Figure 1.
keep-not-I : (t : SixCases) -> fig1-keep I t ≡ true -> ⊥
keep-not-I t ()

-- ----------------------------------------------------------------------
-- * One step of a path descent costs exactly the drop in the potential

private
  -- A dashed edge of Figure 1: the source cannot have lde 0, and the
  -- pat-rank increases by one.
  keep-pot : (s t : SixCases) (l : ℕ) -> (l ≡ 0 -> s ≡ I) -> fig1-keep s t ≡ true ->
             1 Nat.+ pot (just t) l Nat.≤ pot (just s) l
  keep-pot s t zero hI hkeep =
    ⊥-elim (keep-not-I t (subst (λ u -> fig1-keep u t ≡ true) (hI refl) hkeep))
  keep-pot s t (suc l0) hI hkeep =
    subst (λ n -> 1 Nat.+ (n ∸ pat-rank (just t)) Nat.≤ n ∸ pat-rank (just s)) (sym (two*suc l0))
          (subst (λ r -> 1 Nat.+ (suc (suc (2 Nat.* l0)) ∸ r) Nat.≤ suc (suc (2 Nat.* l0)) ∸ pat-rank (just s))
                 (sym (rank-keep s t hkeep))
                 (arith (2 Nat.* l0) (pat-rank (just s)) (rank-keep-src s t hkeep)))
    where
      arith : (M r : ℕ) -> r Nat.≤ 1 ->
              1 Nat.+ (suc (suc M) ∸ suc r) Nat.≤ suc (suc M) ∸ r
      arith M zero _ = NatP.≤-refl
      arith M (suc zero) _ = NatP.≤-refl
      arith M (suc (suc r)) (s≤s ())

  -- An undashed edge of Figure 1: the pat-rank drops by one.
  drop-pot : (s t : SixCases) (l' : ℕ) -> pat-rank (just t) Nat.≤ 2 Nat.* l' ->
             fig1-drop s t ≡ true ->
             1 Nat.+ pot (just t) l' Nat.≤ pot (just s) (suc l')
  drop-pot s t l' hr hdrop =
    subst (λ n -> 1 Nat.+ (2 Nat.* l' ∸ pat-rank (just t)) Nat.≤ n ∸ pat-rank (just s)) (sym (two*suc l'))
          (subst (λ r -> 1 Nat.+ (2 Nat.* l' ∸ pat-rank (just t)) Nat.≤ suc (suc (2 Nat.* l')) ∸ r)
                 (sym (rank-drop s t hdrop))
                 (NatP.≤-reflexive (sym (NatP.+-∸-assoc 1 hr))))

  -- The exceptional (ii) → (i) step at lde 1, which uses a CK gate.
  two-pot : 2 Nat.+ pot (just I) 0 Nat.≤ pot (just II) 1
  two-pot = NatP.≤-refl

  -- The two branches of the K-count-1 case, with the equality of the
  -- ldes as an explicit argument of known type: ≡ᵇ⇒≡ and subst both
  -- have implicit arguments that nothing else would determine.
  case-k1-keep : (s t : SixCases) (l l' : ℕ) -> (l ≡ 0 -> s ≡ I) -> l' ≡ l ->
                 fig1-keep s t ≡ true -> 1 Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  case-k1-keep s t l l' hI el hkeep =
    subst (λ m -> 1 Nat.+ pot (just t) m Nat.≤ pot (just s) l) (sym el)
          (keep-pot s t l hI hkeep)

  case-k1-drop : (s t : SixCases) (l l' : ℕ) -> pat-rank (just t) Nat.≤ 2 Nat.* l' ->
                 suc l' ≡ l -> fig1-drop s t ≡ true ->
                 1 Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  case-k1-drop s t l l' hr el2 hdrop =
    subst (λ m -> 1 Nat.+ pot (just t) l' Nat.≤ pot (just s) m) el2
          (drop-pot s t l' hr hdrop)

  case-k1 : (s t : SixCases) (l l' : ℕ) -> (l ≡ 0 -> s ≡ I) -> pat-rank (just t) Nat.≤ 2 Nat.* l' ->
            (if (l' Nat.≡ᵇ l) then fig1-keep s t
             else (if suc l' Nat.≡ᵇ l then fig1-drop s t else false)) ≡ true ->
            1 Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  case-k1 s t l l' hI hr h
    with if-true (l' Nat.≡ᵇ l) (fig1-keep s t)
                 (if suc l' Nat.≡ᵇ l then fig1-drop s t else false) h
  ... | inj₁ (el , hkeep) = case-k1-keep s t l l' hI (≡ᵇ⇒≡ el) hkeep
  ... | inj₂ (_ , h2) with if-true (suc l' Nat.≡ᵇ l) (fig1-drop s t) false h2
  ...   | inj₁ (el2 , hdrop) = case-k1-drop s t l l' hr (≡ᵇ⇒≡ el2) hdrop
  ...   | inj₂ (_ , hf) = ⊥-elim (false-true hf)

  ∧-true₄ : {a b c d : Bool} -> a ∧ b ∧ c ∧ d ≡ true ->
            (a ≡ true) × (b ≡ true) × (c ≡ true) × (d ≡ true)
  ∧-true₄ {true} {true} {true} {true} _ = refl , refl , refl , refl

  case-k2 : (s t : SixCases) (l l' : ℕ) ->
            ((s == II) ∧ (t == I) ∧ (l Nat.≡ᵇ 1) ∧ (l' Nat.≡ᵇ 0)) ≡ true ->
            2 Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  case-k2 s t l l' h = subst₄ (==⇒≡ e1) (==⇒≡ e2) (≡ᵇ⇒≡ e3) (≡ᵇ⇒≡ e4) two-pot
    where
      parts : ((s == II) ≡ true) × ((t == I) ≡ true) × ((l Nat.≡ᵇ 1) ≡ true) × ((l' Nat.≡ᵇ 0) ≡ true)
      parts = ∧-true₄ h
      e1 = proj₁ parts
      e2 = proj₁ (proj₂ parts)
      e3 = proj₁ (proj₂ (proj₂ parts))
      e4 = proj₂ (proj₂ (proj₂ parts))
      subst₄ : s ≡ II -> t ≡ I -> l ≡ 1 -> l' ≡ 0 ->
               2 Nat.+ pot (just I) 0 Nat.≤ pot (just II) 1 ->
               2 Nat.+ pot (just t) l' Nat.≤ pot (just s) l
      subst₄ refl refl refl refl p = p

  -- The body of fig1-step-of when both patterns are present. Spelling
  -- it out is what lets the case analysis below see the guards.
  fig1-body : SixCases -> ℕ -> SixCases -> ℕ -> ℕ -> Bool
  fig1-body s l t l' k =
    if (k Nat.≡ᵇ 1)
    then (if l' Nat.≡ᵇ l then fig1-keep s t
          else (if suc l' Nat.≡ᵇ l then fig1-drop s t else false))
    else (if k Nat.≡ᵇ 2
          then ((s == II) ∧ (t == I) ∧ (l Nat.≡ᵇ 1) ∧ (l' Nat.≡ᵇ 0))
          else false)

  fig1-body-≡ : (s : SixCases) (l : ℕ) (t : SixCases) (l' k : ℕ) ->
                fig1-step-of (just s) l (just t) l' k ≡ fig1-body s l t l' k
  fig1-body-≡ s l t l' k = refl

  -- Replacing the K-count by the value the guard fixed it to.
  kc-subst : (s t : SixCases) (l l' k n : ℕ) -> k ≡ n ->
             n Nat.+ pot (just t) l' Nat.≤ pot (just s) l ->
             k Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  kc-subst s t l l' k n e p =
    subst (λ m -> m Nat.+ pot (just t) l' Nat.≤ pot (just s) l) (sym e) p

  fig1-body-pot : (s t : SixCases) (l l' k : ℕ) ->
                  (l ≡ 0 -> s ≡ I) -> pat-rank (just t) Nat.≤ 2 Nat.* l' ->
                  fig1-body s l t l' k ≡ true ->
                  k Nat.+ pot (just t) l' Nat.≤ pot (just s) l
  fig1-body-pot s t l l' k hI hr h
    with if-true (k Nat.≡ᵇ 1)
                 (if l' Nat.≡ᵇ l then fig1-keep s t
                  else (if suc l' Nat.≡ᵇ l then fig1-drop s t else false))
                 (if k Nat.≡ᵇ 2
                  then ((s == II) ∧ (t == I) ∧ (l Nat.≡ᵇ 1) ∧ (l' Nat.≡ᵇ 0))
                  else false) h
  ... | inj₁ (ek , h1) = kc-subst s t l l' k 1 (≡ᵇ⇒≡ ek) (case-k1 s t l l' hI hr h1)
  ... | inj₂ (_ , h1)
        with if-true (k Nat.≡ᵇ 2)
                     ((s == II) ∧ (t == I) ∧ (l Nat.≡ᵇ 1) ∧ (l' Nat.≡ᵇ 0)) false h1
  ...   | inj₁ (ek2 , h2) = kc-subst s t l l' k 2 (≡ᵇ⇒≡ ek2) (case-k2 s t l l' h2)
  ...   | inj₂ (_ , hf) = ⊥-elim (false-true hf)

-- One step of a path descent (Figure 1) costs exactly the drop in the
-- potential.
fig1-step-pot : (p q : Maybe SixCases) (l l' k : ℕ) ->
                (l ≡ 0 -> p ≡ just I) -> pat-rank q Nat.≤ 2 Nat.* l' ->
                fig1-step-of p l q l' k ≡ true ->
                k Nat.+ pot q l' Nat.≤ pot p l
fig1-step-pot nothing q l l' k hI hr ()
fig1-step-pot (just s) nothing l l' k hI hr ()
fig1-step-pot (just s) (just t) l l' k hI hr hstep =
  fig1-body-pot s t l l' k (λ z -> just-inj (hI z)) hr hstep
