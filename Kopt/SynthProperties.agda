-- Properties of the synthesis algorithm of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026),
--
-- as implemented in Kopt.Synth. This module proves, about the
-- algorithm itself rather than about the operators it is run on:
--
--  * inverses: ⟦inv-circuit c⟧·⟦c⟧ = ⟦c⟧·⟦inv-circuit c⟧ = 1 for
--    every circuit c, and ⟦desugar-ck c⟧ = ⟦c⟧ (Equation (1));
--
--  * the peephole optimization optimize-gp preserves the operator,
--    keeps the K-count, and produces a circuit over the gate set 𝒢
--    with at most rkc+1 CS gates and at most 10·rkc+9 gates
--    (optimize-gp-sem, optimize-gp-kc, optimize-gp-cs,
--    optimize-gp-len). These hold for EVERY input circuit, with no
--    hypothesis: the K-free blocks of the output are canonical
--    generalized-permutation circuits (Section III C);
--
--  * hence the counting half of Corollary V.8 for the output of
--    synth itself (synth-𝒢, synth-cs, synth-len), again
--    unconditionally;
--
--  * correctness, ⟦synth A⟧ = A, under the explicit hypothesis that
--    the descent of A reaches lde 0 within the fuel that synth uses
--    (Descends / Terminates). That hypothesis is the part of the
--    paper that is not formalized here -- Lemma IV.1 (every
--    Clifford+CS operator has one of the six patterns), Lemma IV.4
--    with Lemma IV.7 (the descent decreases the lde within 2·lde(A)+1
--    steps) and Section III C (an operator of lde 0 is a generalized
--    permutation). It is DECIDABLE: descends? runs the same recursion
--    and returns a boolean, descends?-sound turns a successful run
--    into the hypothesis, and so synth-correct-check proves
--    ⟦synth A⟧ = A from a computation for any concrete A.
--
-- Everything here is proved; there are no postulates and no
-- unchecked termination. What is NOT proved is listed above and in
-- the report of Kopt/README.md.

{-# OPTIONS --without-K --safe #-}

module Kopt.SynthProperties where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
import Data.List.Properties as ListP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂ ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations using (gperm-of)
open import Kopt.Patterns using (LevelData ; level-at)
open import Kopt.Synth
open import Kopt.Descent
open import Kopt.Optimality using (==⇒≡ ; ≤ᵇ⇒≤ ; ≡ᵇ⇒≡ ; kc-++ ; csc-++ ; rlen-++ ;
                                   over-𝒢-++ ; kfree-gp ; gp-circuit? ; gate-gp?)

private
  false≢true : false ≡ true -> ⊥
  false≢true ()

-- ----------------------------------------------------------------------
-- * Rearranging products of four and five matrices

private
  assoc-shuffle : (a b c d e : Op) -> ((a * b) * c) * (d * e) ≡ (a * ((b * c) * d)) * e
  assoc-shuffle a b c d e = begin
    ((a * b) * c) * (d * e)  ≡⟨ cong (λ m -> m * (d * e)) (mat-*-assoc a b c) ⟩
    (a * (b * c)) * (d * e)  ≡⟨ sym (mat-*-assoc (a * (b * c)) d e) ⟩
    ((a * (b * c)) * d) * e  ≡⟨ cong (λ m -> m * e) (mat-*-assoc a (b * c) d) ⟩
    (a * ((b * c) * d)) * e  ∎
    where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * Inverses of gates and of circuits
--
-- Each of the sixteen gates is checked by evaluating the 4×4 product;
-- the equality of matrices is stated as a boolean test (==⇒≡ refl),
-- which is much cheaper for the conversion checker.

inv-gate-left : (g : Gate) -> ⟦ inv-gate g ⟧ * ⟦ g ⟧g ≡ 1#
inv-gate-left X₀ = ==⇒≡ refl
inv-gate-left X₁ = ==⇒≡ refl
inv-gate-left Z₀ = ==⇒≡ refl
inv-gate-left Z₁ = ==⇒≡ refl
inv-gate-left S₀ = ==⇒≡ refl
inv-gate-left S₁ = ==⇒≡ refl
inv-gate-left K₀ = ==⇒≡ refl
inv-gate-left K₁ = ==⇒≡ refl
inv-gate-left CZ = ==⇒≡ refl
inv-gate-left CS = ==⇒≡ refl
inv-gate-left CX = ==⇒≡ refl
inv-gate-left XC = ==⇒≡ refl
inv-gate-left Ex = ==⇒≡ refl
inv-gate-left Ii = ==⇒≡ refl
inv-gate-left CK = ==⇒≡ refl
inv-gate-left KC = ==⇒≡ refl

inv-gate-right : (g : Gate) -> ⟦ g ⟧g * ⟦ inv-gate g ⟧ ≡ 1#
inv-gate-right X₀ = ==⇒≡ refl
inv-gate-right X₁ = ==⇒≡ refl
inv-gate-right Z₀ = ==⇒≡ refl
inv-gate-right Z₁ = ==⇒≡ refl
inv-gate-right S₀ = ==⇒≡ refl
inv-gate-right S₁ = ==⇒≡ refl
inv-gate-right K₀ = ==⇒≡ refl
inv-gate-right K₁ = ==⇒≡ refl
inv-gate-right CZ = ==⇒≡ refl
inv-gate-right CS = ==⇒≡ refl
inv-gate-right CX = ==⇒≡ refl
inv-gate-right XC = ==⇒≡ refl
inv-gate-right Ex = ==⇒≡ refl
inv-gate-right Ii = ==⇒≡ refl
inv-gate-right CK = ==⇒≡ refl
inv-gate-right KC = ==⇒≡ refl

-- inv-circuit reverses, so a gate added at the front of a circuit
-- adds its inverse at the back of the inverse circuit.
inv-circuit-cons : (g : Gate) (c : Circuit) -> inv-circuit (g ∷ c) ≡ inv-circuit c ++ inv-gate g
inv-circuit-cons g c = begin
  List.concatMap inv-gate (List.reverse (g ∷ c))
    ≡⟨ cong (List.concatMap inv-gate) (ListP.unfold-reverse g c) ⟩
  List.concatMap inv-gate (List.reverse c ++ (g ∷ []))
    ≡⟨ ListP.concatMap-++ inv-gate (List.reverse c) (g ∷ []) ⟩
  inv-circuit c ++ (inv-gate g ++ [])
    ≡⟨ cong (λ d -> inv-circuit c ++ d) (ListP.++-identityʳ (inv-gate g)) ⟩
  inv-circuit c ++ inv-gate g ∎
  where open ≡-Reasoning

inv-circuit-app : (c d : Circuit) -> inv-circuit (c ++ d) ≡ inv-circuit d ++ inv-circuit c
inv-circuit-app c d = begin
  List.concatMap inv-gate (List.reverse (c ++ d))
    ≡⟨ cong (List.concatMap inv-gate) (ListP.reverse-++ c d) ⟩
  List.concatMap inv-gate (List.reverse d ++ List.reverse c)
    ≡⟨ ListP.concatMap-++ inv-gate (List.reverse d) (List.reverse c) ⟩
  inv-circuit d ++ inv-circuit c ∎
  where open ≡-Reasoning

-- ⟦C⁻¹⟧·⟦C⟧ = 1 and ⟦C⟧·⟦C⁻¹⟧ = 1.
inv-circuit-left : (c : Circuit) -> ⟦ inv-circuit c ⟧ * ⟦ c ⟧ ≡ 1#
inv-circuit-left [] = mat-*-identityʳ 1#
inv-circuit-left (g ∷ c) = begin
  ⟦ inv-circuit (g ∷ c) ⟧ * ⟦ g ∷ c ⟧
    ≡⟨ cong (λ d -> ⟦ d ⟧ * ⟦ g ∷ c ⟧) (inv-circuit-cons g c) ⟩
  ⟦ inv-circuit c ++ inv-gate g ⟧ * (⟦ g ⟧g * ⟦ c ⟧)
    ≡⟨ cong (λ m -> m * (⟦ g ⟧g * ⟦ c ⟧)) (⟦⟧-++ (inv-circuit c) (inv-gate g)) ⟩
  (⟦ inv-circuit c ⟧ * ⟦ inv-gate g ⟧) * (⟦ g ⟧g * ⟦ c ⟧)
    ≡⟨ mat-*-assoc ⟦ inv-circuit c ⟧ ⟦ inv-gate g ⟧ (⟦ g ⟧g * ⟦ c ⟧) ⟩
  ⟦ inv-circuit c ⟧ * (⟦ inv-gate g ⟧ * (⟦ g ⟧g * ⟦ c ⟧))
    ≡⟨ cong (λ m -> ⟦ inv-circuit c ⟧ * m) (sym (mat-*-assoc ⟦ inv-gate g ⟧ ⟦ g ⟧g ⟦ c ⟧)) ⟩
  ⟦ inv-circuit c ⟧ * ((⟦ inv-gate g ⟧ * ⟦ g ⟧g) * ⟦ c ⟧)
    ≡⟨ cong (λ m -> ⟦ inv-circuit c ⟧ * (m * ⟦ c ⟧)) (inv-gate-left g) ⟩
  ⟦ inv-circuit c ⟧ * (1# * ⟦ c ⟧)
    ≡⟨ cong (λ m -> ⟦ inv-circuit c ⟧ * m) (mat-*-identityˡ ⟦ c ⟧) ⟩
  ⟦ inv-circuit c ⟧ * ⟦ c ⟧
    ≡⟨ inv-circuit-left c ⟩
  1# ∎
  where open ≡-Reasoning

inv-circuit-right : (c : Circuit) -> ⟦ c ⟧ * ⟦ inv-circuit c ⟧ ≡ 1#
inv-circuit-right [] = mat-*-identityʳ 1#
inv-circuit-right (g ∷ c) = begin
  ⟦ g ∷ c ⟧ * ⟦ inv-circuit (g ∷ c) ⟧
    ≡⟨ cong (λ d -> ⟦ g ∷ c ⟧ * ⟦ d ⟧) (inv-circuit-cons g c) ⟩
  (⟦ g ⟧g * ⟦ c ⟧) * ⟦ inv-circuit c ++ inv-gate g ⟧
    ≡⟨ cong (λ m -> (⟦ g ⟧g * ⟦ c ⟧) * m) (⟦⟧-++ (inv-circuit c) (inv-gate g)) ⟩
  (⟦ g ⟧g * ⟦ c ⟧) * (⟦ inv-circuit c ⟧ * ⟦ inv-gate g ⟧)
    ≡⟨ mat-*-assoc ⟦ g ⟧g ⟦ c ⟧ (⟦ inv-circuit c ⟧ * ⟦ inv-gate g ⟧) ⟩
  ⟦ g ⟧g * (⟦ c ⟧ * (⟦ inv-circuit c ⟧ * ⟦ inv-gate g ⟧))
    ≡⟨ cong (λ m -> ⟦ g ⟧g * m) (sym (mat-*-assoc ⟦ c ⟧ ⟦ inv-circuit c ⟧ ⟦ inv-gate g ⟧)) ⟩
  ⟦ g ⟧g * ((⟦ c ⟧ * ⟦ inv-circuit c ⟧) * ⟦ inv-gate g ⟧)
    ≡⟨ cong (λ m -> ⟦ g ⟧g * (m * ⟦ inv-gate g ⟧)) (inv-circuit-right c) ⟩
  ⟦ g ⟧g * (1# * ⟦ inv-gate g ⟧)
    ≡⟨ cong (λ m -> ⟦ g ⟧g * m) (mat-*-identityˡ ⟦ inv-gate g ⟧) ⟩
  ⟦ g ⟧g * ⟦ inv-gate g ⟧
    ≡⟨ inv-gate-right g ⟩
  1# ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * Equation (1): desugaring the controlled-K gates
--
-- CK = CZ·Z₀S₀Z₁S₁K₁CSK₁S₁·i and its mirror image KC.

decompose-ck-ok : (g : Gate) -> ⟦ decompose-ck g ⟧ ≡ ⟦ g ⟧g
decompose-ck-ok X₀ = mat-*-identityʳ ⟦ X₀ ⟧g
decompose-ck-ok X₁ = mat-*-identityʳ ⟦ X₁ ⟧g
decompose-ck-ok Z₀ = mat-*-identityʳ ⟦ Z₀ ⟧g
decompose-ck-ok Z₁ = mat-*-identityʳ ⟦ Z₁ ⟧g
decompose-ck-ok S₀ = mat-*-identityʳ ⟦ S₀ ⟧g
decompose-ck-ok S₁ = mat-*-identityʳ ⟦ S₁ ⟧g
decompose-ck-ok K₀ = mat-*-identityʳ ⟦ K₀ ⟧g
decompose-ck-ok K₁ = mat-*-identityʳ ⟦ K₁ ⟧g
decompose-ck-ok CZ = mat-*-identityʳ ⟦ CZ ⟧g
decompose-ck-ok CS = mat-*-identityʳ ⟦ CS ⟧g
decompose-ck-ok CX = mat-*-identityʳ ⟦ CX ⟧g
decompose-ck-ok XC = mat-*-identityʳ ⟦ XC ⟧g
decompose-ck-ok Ex = mat-*-identityʳ ⟦ Ex ⟧g
decompose-ck-ok Ii = mat-*-identityʳ ⟦ Ii ⟧g
decompose-ck-ok CK = ==⇒≡ refl
decompose-ck-ok KC = ==⇒≡ refl

desugar-ck-ok : (c : Circuit) -> ⟦ desugar-ck c ⟧ ≡ ⟦ c ⟧
desugar-ck-ok [] = refl
desugar-ck-ok (g ∷ c) =
  trans (⟦⟧-++ (decompose-ck g) (desugar-ck c))
        (cong₂ _*_ (decompose-ck-ok g) (desugar-ck-ok c))

private
  over-𝒢-decompose : (g : Gate) -> Over𝒢 (decompose-ck g)
  over-𝒢-decompose X₀ = refl
  over-𝒢-decompose X₁ = refl
  over-𝒢-decompose Z₀ = refl
  over-𝒢-decompose Z₁ = refl
  over-𝒢-decompose S₀ = refl
  over-𝒢-decompose S₁ = refl
  over-𝒢-decompose K₀ = refl
  over-𝒢-decompose K₁ = refl
  over-𝒢-decompose CZ = refl
  over-𝒢-decompose CS = refl
  over-𝒢-decompose CX = refl
  over-𝒢-decompose XC = refl
  over-𝒢-decompose Ex = refl
  over-𝒢-decompose Ii = refl
  over-𝒢-decompose CK = refl
  over-𝒢-decompose KC = refl

-- Every desugared circuit is over 𝒢, whatever its input was.
over-𝒢-desugar : (c : Circuit) -> Over𝒢 (desugar-ck c)
over-𝒢-desugar [] = refl
over-𝒢-desugar (g ∷ c) =
  over-𝒢-++ (decompose-ck g) (desugar-ck c) (over-𝒢-decompose g) (over-𝒢-desugar c)

-- ----------------------------------------------------------------------
-- * Gates: K gates, non-K gates
--
-- Sixteen-way case analyses used below; the impossible cases are
-- ruled out by absurd patterns.

private
  k-gate-in-𝒢 : (g : Gate) -> is-k-gate g ≡ true -> in-𝒢 g ≡ true
  k-gate-in-𝒢 K₀ _ = refl
  k-gate-in-𝒢 K₁ _ = refl
  k-gate-in-𝒢 X₀ ()
  k-gate-in-𝒢 X₁ ()
  k-gate-in-𝒢 Z₀ ()
  k-gate-in-𝒢 Z₁ ()
  k-gate-in-𝒢 S₀ ()
  k-gate-in-𝒢 S₁ ()
  k-gate-in-𝒢 CZ ()
  k-gate-in-𝒢 CS ()
  k-gate-in-𝒢 CX ()
  k-gate-in-𝒢 XC ()
  k-gate-in-𝒢 Ex ()
  k-gate-in-𝒢 Ii ()
  k-gate-in-𝒢 CK ()
  k-gate-in-𝒢 KC ()

  k-gate-kc : (g : Gate) -> is-k-gate g ≡ true -> (c : Circuit) -> kc (g ∷ c) ≡ suc (kc c)
  k-gate-kc K₀ _ c = refl
  k-gate-kc K₁ _ c = refl
  k-gate-kc X₀ () c
  k-gate-kc X₁ () c
  k-gate-kc Z₀ () c
  k-gate-kc Z₁ () c
  k-gate-kc S₀ () c
  k-gate-kc S₁ () c
  k-gate-kc CZ () c
  k-gate-kc CS () c
  k-gate-kc CX () c
  k-gate-kc XC () c
  k-gate-kc Ex () c
  k-gate-kc Ii () c
  k-gate-kc CK () c
  k-gate-kc KC () c

  k-gate-csc : (g : Gate) -> is-k-gate g ≡ true -> (c : Circuit) -> csc (g ∷ c) ≡ csc c
  k-gate-csc K₀ _ c = refl
  k-gate-csc K₁ _ c = refl
  k-gate-csc X₀ () c
  k-gate-csc X₁ () c
  k-gate-csc Z₀ () c
  k-gate-csc Z₁ () c
  k-gate-csc S₀ () c
  k-gate-csc S₁ () c
  k-gate-csc CZ () c
  k-gate-csc CS () c
  k-gate-csc CX () c
  k-gate-csc XC () c
  k-gate-csc Ex () c
  k-gate-csc Ii () c
  k-gate-csc CK () c
  k-gate-csc KC () c

  -- A gate of 𝒢 that is not a K gate is a generalized permutation.
  nonk-gp : (g : Gate) -> in-𝒢 g ≡ true -> is-k-gate g ≡ false -> gate-gp? g ≡ true
  nonk-gp X₀ _ _ = refl
  nonk-gp X₁ _ _ = refl
  nonk-gp Z₀ _ _ = refl
  nonk-gp Z₁ _ _ = refl
  nonk-gp S₀ _ _ = refl
  nonk-gp S₁ _ _ = refl
  nonk-gp CZ _ _ = refl
  nonk-gp CS _ _ = refl
  nonk-gp CX _ _ = refl
  nonk-gp XC _ _ = refl
  nonk-gp Ex _ _ = refl
  nonk-gp Ii _ _ = refl
  nonk-gp K₀ _ ()
  nonk-gp K₁ _ ()
  nonk-gp CK () _
  nonk-gp KC () _

  -- A K-free circuit has K-count 0.
  gp-cons-kc : (g : Gate) -> gate-gp? g ≡ true -> (c : Circuit) -> kc (g ∷ c) ≡ kc c
  gp-cons-kc X₀ _ c = refl
  gp-cons-kc X₁ _ c = refl
  gp-cons-kc Z₀ _ c = refl
  gp-cons-kc Z₁ _ c = refl
  gp-cons-kc S₀ _ c = refl
  gp-cons-kc S₁ _ c = refl
  gp-cons-kc CZ _ c = refl
  gp-cons-kc CS _ c = refl
  gp-cons-kc CX _ c = refl
  gp-cons-kc XC _ c = refl
  gp-cons-kc Ex _ c = refl
  gp-cons-kc Ii _ c = refl
  gp-cons-kc K₀ () c
  gp-cons-kc K₁ () c
  gp-cons-kc CK () c
  gp-cons-kc KC () c

gp-circuit-kc : (c : Circuit) -> gp-circuit? c ≡ true -> kc c ≡ 0
gp-circuit-kc [] _ = refl
gp-circuit-kc (g ∷ c) h =
  trans (gp-cons-kc g (proj₁ (∧-true h)) c) (gp-circuit-kc c (proj₂ (∧-true h)))

-- Splitting a circuit over 𝒢 gives two circuits over 𝒢.
over-𝒢-split : (c d : Circuit) -> Over𝒢 (c ++ d) -> Over𝒢 c × Over𝒢 d
over-𝒢-split [] d h = refl , h
over-𝒢-split (g ∷ c) d h = cong₂ _∧_ (proj₁ (∧-true h)) (proj₁ rec) , proj₂ rec
  where
    rec : Over𝒢 c × Over𝒢 d
    rec = over-𝒢-split c d (proj₂ (∧-true h))

-- ----------------------------------------------------------------------
-- * Canonical circuits for generalized permutations
--
-- Section III C: a generalized permutation is implemented by a
-- circuit of at most 9 gates of 𝒢, with no K gate and at most one CS
-- gate, and Kopt.Permutations.gperm-of computes one. The exhaustive
-- check over the explicit list of the 24·256 = 6144 generalized
-- permutations verifies all of that at once, and also that gperm-of
-- does return a circuit for them (which Kopt.Optimality's
-- gp-circuit-ok does not record, since it replaces "nothing" by the
-- empty circuit).

record GPCircuit (m : Op) (c : Circuit) : Set where
  constructor gp-props
  field
    gpc-sem : ⟦ c ⟧ ≡ m
    gpc-len : rlen c Nat.≤ 9
    gpc-kc : kc c ≡ 0
    gpc-cs : csc c Nat.≤ 1
    gpc-𝒢 : Over𝒢 c
open GPCircuit public

private
  gp-ok? : Op -> Circuit -> Bool
  gp-ok? m c = (⟦ c ⟧ == m) ∧ (rlen c Nat.≤ᵇ 9) ∧ (kc c Nat.≡ᵇ 0) ∧ (csc c Nat.≤ᵇ 1) ∧ over-𝒢ᵇ c

  gp-go? : Op -> Maybe Circuit -> Bool
  gp-go? m nothing = false
  gp-go? m (just c) = gp-ok? m c

  -- The matrix is passed as an argument so that it is computed once
  -- (the type checker does not share let/where-bound values).
  gp-check1 : Op -> Bool
  gp-check1 m = gp-go? m (gperm-of m)

  gp-check-phases : Pos4 -> Phase4 -> Bool
  gp-check-phases t e = gp-check1 (gp-mat-of t e)

  -- The 256 phase vectors for one permutation, and then the 24
  -- permutations: 24 blocks of 256 rather than one enumeration of
  -- 6144 pairs, which keeps the type checker's heap smaller.
  gp-check-perm : Pos4 -> Bool
  gp-check-perm t = all-of (gp-check-phases t) all-phase4

  -- One conversion problem per permutation (24 blocks of 256 instead
  -- of one of 6144), so that the type checker can reclaim each
  -- block before starting the next one. The 232 tuples that are not
  -- permutations are ruled out by absurd patterns.
  gp-check-perm-ok : (a b c d : Pos) -> distinct4p (a , b , c , d) ≡ true ->
                     gp-check-perm (a , b , c , d) ≡ true
  gp-check-perm-ok p0 p0 p0 p0 ()
  gp-check-perm-ok p0 p0 p0 p1 ()
  gp-check-perm-ok p0 p0 p0 p2 ()
  gp-check-perm-ok p0 p0 p0 p3 ()
  gp-check-perm-ok p0 p0 p1 p0 ()
  gp-check-perm-ok p0 p0 p1 p1 ()
  gp-check-perm-ok p0 p0 p1 p2 ()
  gp-check-perm-ok p0 p0 p1 p3 ()
  gp-check-perm-ok p0 p0 p2 p0 ()
  gp-check-perm-ok p0 p0 p2 p1 ()
  gp-check-perm-ok p0 p0 p2 p2 ()
  gp-check-perm-ok p0 p0 p2 p3 ()
  gp-check-perm-ok p0 p0 p3 p0 ()
  gp-check-perm-ok p0 p0 p3 p1 ()
  gp-check-perm-ok p0 p0 p3 p2 ()
  gp-check-perm-ok p0 p0 p3 p3 ()
  gp-check-perm-ok p0 p1 p0 p0 ()
  gp-check-perm-ok p0 p1 p0 p1 ()
  gp-check-perm-ok p0 p1 p0 p2 ()
  gp-check-perm-ok p0 p1 p0 p3 ()
  gp-check-perm-ok p0 p1 p1 p0 ()
  gp-check-perm-ok p0 p1 p1 p1 ()
  gp-check-perm-ok p0 p1 p1 p2 ()
  gp-check-perm-ok p0 p1 p1 p3 ()
  gp-check-perm-ok p0 p1 p2 p0 ()
  gp-check-perm-ok p0 p1 p2 p1 ()
  gp-check-perm-ok p0 p1 p2 p2 ()
  gp-check-perm-ok p0 p1 p2 p3 _ = refl
  gp-check-perm-ok p0 p1 p3 p0 ()
  gp-check-perm-ok p0 p1 p3 p1 ()
  gp-check-perm-ok p0 p1 p3 p2 _ = refl
  gp-check-perm-ok p0 p1 p3 p3 ()
  gp-check-perm-ok p0 p2 p0 p0 ()
  gp-check-perm-ok p0 p2 p0 p1 ()
  gp-check-perm-ok p0 p2 p0 p2 ()
  gp-check-perm-ok p0 p2 p0 p3 ()
  gp-check-perm-ok p0 p2 p1 p0 ()
  gp-check-perm-ok p0 p2 p1 p1 ()
  gp-check-perm-ok p0 p2 p1 p2 ()
  gp-check-perm-ok p0 p2 p1 p3 _ = refl
  gp-check-perm-ok p0 p2 p2 p0 ()
  gp-check-perm-ok p0 p2 p2 p1 ()
  gp-check-perm-ok p0 p2 p2 p2 ()
  gp-check-perm-ok p0 p2 p2 p3 ()
  gp-check-perm-ok p0 p2 p3 p0 ()
  gp-check-perm-ok p0 p2 p3 p1 _ = refl
  gp-check-perm-ok p0 p2 p3 p2 ()
  gp-check-perm-ok p0 p2 p3 p3 ()
  gp-check-perm-ok p0 p3 p0 p0 ()
  gp-check-perm-ok p0 p3 p0 p1 ()
  gp-check-perm-ok p0 p3 p0 p2 ()
  gp-check-perm-ok p0 p3 p0 p3 ()
  gp-check-perm-ok p0 p3 p1 p0 ()
  gp-check-perm-ok p0 p3 p1 p1 ()
  gp-check-perm-ok p0 p3 p1 p2 _ = refl
  gp-check-perm-ok p0 p3 p1 p3 ()
  gp-check-perm-ok p0 p3 p2 p0 ()
  gp-check-perm-ok p0 p3 p2 p1 _ = refl
  gp-check-perm-ok p0 p3 p2 p2 ()
  gp-check-perm-ok p0 p3 p2 p3 ()
  gp-check-perm-ok p0 p3 p3 p0 ()
  gp-check-perm-ok p0 p3 p3 p1 ()
  gp-check-perm-ok p0 p3 p3 p2 ()
  gp-check-perm-ok p0 p3 p3 p3 ()
  gp-check-perm-ok p1 p0 p0 p0 ()
  gp-check-perm-ok p1 p0 p0 p1 ()
  gp-check-perm-ok p1 p0 p0 p2 ()
  gp-check-perm-ok p1 p0 p0 p3 ()
  gp-check-perm-ok p1 p0 p1 p0 ()
  gp-check-perm-ok p1 p0 p1 p1 ()
  gp-check-perm-ok p1 p0 p1 p2 ()
  gp-check-perm-ok p1 p0 p1 p3 ()
  gp-check-perm-ok p1 p0 p2 p0 ()
  gp-check-perm-ok p1 p0 p2 p1 ()
  gp-check-perm-ok p1 p0 p2 p2 ()
  gp-check-perm-ok p1 p0 p2 p3 _ = refl
  gp-check-perm-ok p1 p0 p3 p0 ()
  gp-check-perm-ok p1 p0 p3 p1 ()
  gp-check-perm-ok p1 p0 p3 p2 _ = refl
  gp-check-perm-ok p1 p0 p3 p3 ()
  gp-check-perm-ok p1 p1 p0 p0 ()
  gp-check-perm-ok p1 p1 p0 p1 ()
  gp-check-perm-ok p1 p1 p0 p2 ()
  gp-check-perm-ok p1 p1 p0 p3 ()
  gp-check-perm-ok p1 p1 p1 p0 ()
  gp-check-perm-ok p1 p1 p1 p1 ()
  gp-check-perm-ok p1 p1 p1 p2 ()
  gp-check-perm-ok p1 p1 p1 p3 ()
  gp-check-perm-ok p1 p1 p2 p0 ()
  gp-check-perm-ok p1 p1 p2 p1 ()
  gp-check-perm-ok p1 p1 p2 p2 ()
  gp-check-perm-ok p1 p1 p2 p3 ()
  gp-check-perm-ok p1 p1 p3 p0 ()
  gp-check-perm-ok p1 p1 p3 p1 ()
  gp-check-perm-ok p1 p1 p3 p2 ()
  gp-check-perm-ok p1 p1 p3 p3 ()
  gp-check-perm-ok p1 p2 p0 p0 ()
  gp-check-perm-ok p1 p2 p0 p1 ()
  gp-check-perm-ok p1 p2 p0 p2 ()
  gp-check-perm-ok p1 p2 p0 p3 _ = refl
  gp-check-perm-ok p1 p2 p1 p0 ()
  gp-check-perm-ok p1 p2 p1 p1 ()
  gp-check-perm-ok p1 p2 p1 p2 ()
  gp-check-perm-ok p1 p2 p1 p3 ()
  gp-check-perm-ok p1 p2 p2 p0 ()
  gp-check-perm-ok p1 p2 p2 p1 ()
  gp-check-perm-ok p1 p2 p2 p2 ()
  gp-check-perm-ok p1 p2 p2 p3 ()
  gp-check-perm-ok p1 p2 p3 p0 _ = refl
  gp-check-perm-ok p1 p2 p3 p1 ()
  gp-check-perm-ok p1 p2 p3 p2 ()
  gp-check-perm-ok p1 p2 p3 p3 ()
  gp-check-perm-ok p1 p3 p0 p0 ()
  gp-check-perm-ok p1 p3 p0 p1 ()
  gp-check-perm-ok p1 p3 p0 p2 _ = refl
  gp-check-perm-ok p1 p3 p0 p3 ()
  gp-check-perm-ok p1 p3 p1 p0 ()
  gp-check-perm-ok p1 p3 p1 p1 ()
  gp-check-perm-ok p1 p3 p1 p2 ()
  gp-check-perm-ok p1 p3 p1 p3 ()
  gp-check-perm-ok p1 p3 p2 p0 _ = refl
  gp-check-perm-ok p1 p3 p2 p1 ()
  gp-check-perm-ok p1 p3 p2 p2 ()
  gp-check-perm-ok p1 p3 p2 p3 ()
  gp-check-perm-ok p1 p3 p3 p0 ()
  gp-check-perm-ok p1 p3 p3 p1 ()
  gp-check-perm-ok p1 p3 p3 p2 ()
  gp-check-perm-ok p1 p3 p3 p3 ()
  gp-check-perm-ok p2 p0 p0 p0 ()
  gp-check-perm-ok p2 p0 p0 p1 ()
  gp-check-perm-ok p2 p0 p0 p2 ()
  gp-check-perm-ok p2 p0 p0 p3 ()
  gp-check-perm-ok p2 p0 p1 p0 ()
  gp-check-perm-ok p2 p0 p1 p1 ()
  gp-check-perm-ok p2 p0 p1 p2 ()
  gp-check-perm-ok p2 p0 p1 p3 _ = refl
  gp-check-perm-ok p2 p0 p2 p0 ()
  gp-check-perm-ok p2 p0 p2 p1 ()
  gp-check-perm-ok p2 p0 p2 p2 ()
  gp-check-perm-ok p2 p0 p2 p3 ()
  gp-check-perm-ok p2 p0 p3 p0 ()
  gp-check-perm-ok p2 p0 p3 p1 _ = refl
  gp-check-perm-ok p2 p0 p3 p2 ()
  gp-check-perm-ok p2 p0 p3 p3 ()
  gp-check-perm-ok p2 p1 p0 p0 ()
  gp-check-perm-ok p2 p1 p0 p1 ()
  gp-check-perm-ok p2 p1 p0 p2 ()
  gp-check-perm-ok p2 p1 p0 p3 _ = refl
  gp-check-perm-ok p2 p1 p1 p0 ()
  gp-check-perm-ok p2 p1 p1 p1 ()
  gp-check-perm-ok p2 p1 p1 p2 ()
  gp-check-perm-ok p2 p1 p1 p3 ()
  gp-check-perm-ok p2 p1 p2 p0 ()
  gp-check-perm-ok p2 p1 p2 p1 ()
  gp-check-perm-ok p2 p1 p2 p2 ()
  gp-check-perm-ok p2 p1 p2 p3 ()
  gp-check-perm-ok p2 p1 p3 p0 _ = refl
  gp-check-perm-ok p2 p1 p3 p1 ()
  gp-check-perm-ok p2 p1 p3 p2 ()
  gp-check-perm-ok p2 p1 p3 p3 ()
  gp-check-perm-ok p2 p2 p0 p0 ()
  gp-check-perm-ok p2 p2 p0 p1 ()
  gp-check-perm-ok p2 p2 p0 p2 ()
  gp-check-perm-ok p2 p2 p0 p3 ()
  gp-check-perm-ok p2 p2 p1 p0 ()
  gp-check-perm-ok p2 p2 p1 p1 ()
  gp-check-perm-ok p2 p2 p1 p2 ()
  gp-check-perm-ok p2 p2 p1 p3 ()
  gp-check-perm-ok p2 p2 p2 p0 ()
  gp-check-perm-ok p2 p2 p2 p1 ()
  gp-check-perm-ok p2 p2 p2 p2 ()
  gp-check-perm-ok p2 p2 p2 p3 ()
  gp-check-perm-ok p2 p2 p3 p0 ()
  gp-check-perm-ok p2 p2 p3 p1 ()
  gp-check-perm-ok p2 p2 p3 p2 ()
  gp-check-perm-ok p2 p2 p3 p3 ()
  gp-check-perm-ok p2 p3 p0 p0 ()
  gp-check-perm-ok p2 p3 p0 p1 _ = refl
  gp-check-perm-ok p2 p3 p0 p2 ()
  gp-check-perm-ok p2 p3 p0 p3 ()
  gp-check-perm-ok p2 p3 p1 p0 _ = refl
  gp-check-perm-ok p2 p3 p1 p1 ()
  gp-check-perm-ok p2 p3 p1 p2 ()
  gp-check-perm-ok p2 p3 p1 p3 ()
  gp-check-perm-ok p2 p3 p2 p0 ()
  gp-check-perm-ok p2 p3 p2 p1 ()
  gp-check-perm-ok p2 p3 p2 p2 ()
  gp-check-perm-ok p2 p3 p2 p3 ()
  gp-check-perm-ok p2 p3 p3 p0 ()
  gp-check-perm-ok p2 p3 p3 p1 ()
  gp-check-perm-ok p2 p3 p3 p2 ()
  gp-check-perm-ok p2 p3 p3 p3 ()
  gp-check-perm-ok p3 p0 p0 p0 ()
  gp-check-perm-ok p3 p0 p0 p1 ()
  gp-check-perm-ok p3 p0 p0 p2 ()
  gp-check-perm-ok p3 p0 p0 p3 ()
  gp-check-perm-ok p3 p0 p1 p0 ()
  gp-check-perm-ok p3 p0 p1 p1 ()
  gp-check-perm-ok p3 p0 p1 p2 _ = refl
  gp-check-perm-ok p3 p0 p1 p3 ()
  gp-check-perm-ok p3 p0 p2 p0 ()
  gp-check-perm-ok p3 p0 p2 p1 _ = refl
  gp-check-perm-ok p3 p0 p2 p2 ()
  gp-check-perm-ok p3 p0 p2 p3 ()
  gp-check-perm-ok p3 p0 p3 p0 ()
  gp-check-perm-ok p3 p0 p3 p1 ()
  gp-check-perm-ok p3 p0 p3 p2 ()
  gp-check-perm-ok p3 p0 p3 p3 ()
  gp-check-perm-ok p3 p1 p0 p0 ()
  gp-check-perm-ok p3 p1 p0 p1 ()
  gp-check-perm-ok p3 p1 p0 p2 _ = refl
  gp-check-perm-ok p3 p1 p0 p3 ()
  gp-check-perm-ok p3 p1 p1 p0 ()
  gp-check-perm-ok p3 p1 p1 p1 ()
  gp-check-perm-ok p3 p1 p1 p2 ()
  gp-check-perm-ok p3 p1 p1 p3 ()
  gp-check-perm-ok p3 p1 p2 p0 _ = refl
  gp-check-perm-ok p3 p1 p2 p1 ()
  gp-check-perm-ok p3 p1 p2 p2 ()
  gp-check-perm-ok p3 p1 p2 p3 ()
  gp-check-perm-ok p3 p1 p3 p0 ()
  gp-check-perm-ok p3 p1 p3 p1 ()
  gp-check-perm-ok p3 p1 p3 p2 ()
  gp-check-perm-ok p3 p1 p3 p3 ()
  gp-check-perm-ok p3 p2 p0 p0 ()
  gp-check-perm-ok p3 p2 p0 p1 _ = refl
  gp-check-perm-ok p3 p2 p0 p2 ()
  gp-check-perm-ok p3 p2 p0 p3 ()
  gp-check-perm-ok p3 p2 p1 p0 _ = refl
  gp-check-perm-ok p3 p2 p1 p1 ()
  gp-check-perm-ok p3 p2 p1 p2 ()
  gp-check-perm-ok p3 p2 p1 p3 ()
  gp-check-perm-ok p3 p2 p2 p0 ()
  gp-check-perm-ok p3 p2 p2 p1 ()
  gp-check-perm-ok p3 p2 p2 p2 ()
  gp-check-perm-ok p3 p2 p2 p3 ()
  gp-check-perm-ok p3 p2 p3 p0 ()
  gp-check-perm-ok p3 p2 p3 p1 ()
  gp-check-perm-ok p3 p2 p3 p2 ()
  gp-check-perm-ok p3 p2 p3 p3 ()
  gp-check-perm-ok p3 p3 p0 p0 ()
  gp-check-perm-ok p3 p3 p0 p1 ()
  gp-check-perm-ok p3 p3 p0 p2 ()
  gp-check-perm-ok p3 p3 p0 p3 ()
  gp-check-perm-ok p3 p3 p1 p0 ()
  gp-check-perm-ok p3 p3 p1 p1 ()
  gp-check-perm-ok p3 p3 p1 p2 ()
  gp-check-perm-ok p3 p3 p1 p3 ()
  gp-check-perm-ok p3 p3 p2 p0 ()
  gp-check-perm-ok p3 p3 p2 p1 ()
  gp-check-perm-ok p3 p3 p2 p2 ()
  gp-check-perm-ok p3 p3 p2 p3 ()
  gp-check-perm-ok p3 p3 p3 p0 ()
  gp-check-perm-ok p3 p3 p3 p1 ()
  gp-check-perm-ok p3 p3 p3 p2 ()
  gp-check-perm-ok p3 p3 p3 p3 ()

  gp-check-at : (t : Pos4) -> distinct4p t ≡ true -> gp-check-perm t ≡ true
  gp-check-at (a , b , c , d) h = gp-check-perm-ok a b c d h

  gp-extract : (m : Op) (x : Maybe Circuit) -> gp-go? m x ≡ true ->
               Σ[ c ∈ Circuit ] ((x ≡ just c) × GPCircuit m c)
  gp-extract m (just c) h with ∧-true₅ h
  ... | (p₁ , p₂ , p₃ , p₄ , p₅) =
        c , refl , gp-props (==⇒≡ p₁) (≤ᵇ⇒≤ p₂) (≡ᵇ⇒≡ p₃) (≤ᵇ⇒≤ p₄) p₅
  gp-extract m nothing ()

-- gperm-of returns a circuit for every generalized permutation, and
-- that circuit implements it exactly with at most 9 gates, no K gate
-- and at most one CS gate.
gperm-of-gp : (G : GP) ->
              Σ[ c ∈ Circuit ] ((gperm-of (gp-mat G) ≡ just c) × GPCircuit (gp-mat G) c)
gperm-of-gp G = gp-extract (gp-mat G) (gperm-of (gp-mat G)) chk
  where
    chk : gp-go? (gp-mat G) (gperm-of (gp-mat G)) ≡ true
    chk = all-of-∈ (gp-check-phases (gp-pos G)) all-phase4
            (gp-check-at (gp-pos G) (gp-distinct G))
            (∈-all-phase4 (gp-ph G))

private
  canonical-gp-aux : (c : Circuit) (G : GP) -> ⟦ c ⟧ ≡ gp-mat G ->
                     Σ[ c' ∈ Circuit ] ((gperm-of (gp-mat G) ≡ just c') × GPCircuit (gp-mat G) c') ->
                     GPCircuit ⟦ c ⟧ (canonical-gp c)
  canonical-gp-aux c G eqm (c' , eqj , props) =
    subst (GPCircuit ⟦ c ⟧) (sym eqc) (subst (λ m -> GPCircuit m c') (sym eqm) props)
    where
      eqc : canonical-gp c ≡ c'
      eqc = cong (canonical-gp-of c) (trans (cong gperm-of eqm) eqj)

-- The canonical circuit of a K-free block: it implements the same
-- operator, with at most 9 gates of 𝒢, no K gate and at most one CS
-- gate. (A K-free circuit over 𝒢 implements a generalized
-- permutation, by Kopt.Optimality's kfree-gp.)
canonical-gp-ok : (c : Circuit) -> gp-circuit? c ≡ true -> GPCircuit ⟦ c ⟧ (canonical-gp c)
canonical-gp-ok c h =
  canonical-gp-aux c (proj₁ (kfree-gp c h)) (proj₂ (kfree-gp c h))
                   (gperm-of-gp (proj₁ (kfree-gp c h)))

private
  gperm-circuit-aux : (M : Op) (G : GP) -> M ≡ gp-mat G ->
                      Σ[ c ∈ Circuit ] ((gperm-of (gp-mat G) ≡ just c) × GPCircuit (gp-mat G) c) ->
                      GPCircuit M (gperm-circuit M)
  gperm-circuit-aux M G eqm (c , eqj , props) =
    subst (GPCircuit M) (sym eqc) (subst (λ m -> GPCircuit m c) (sym eqm) props)
    where
      eqc : gperm-circuit M ≡ c
      eqc = cong gperm-circuit-of (trans (cong gperm-of eqm) eqj)

-- The circuit that the lde-0 step of synth uses for a generalized
-- permutation: it implements it exactly, with at most 9 gates of 𝒢,
-- no K gate and at most one CS gate.
gperm-circuit-props : (M : Op) -> IsGPerm M -> GPCircuit M (gperm-circuit M)
gperm-circuit-props M (G , eqm) = gperm-circuit-aux M G eqm (gperm-of-gp G)

gperm-circuit-ok : (M : Op) -> IsGPerm M -> ⟦ gperm-circuit M ⟧ ≡ M
gperm-circuit-ok M h = gpc-sem (gperm-circuit-props M h)

-- ----------------------------------------------------------------------
-- * The maximal K-free prefix

-- Is the circuit empty or does it start with a K gate?
k-head : Circuit -> Bool
k-head [] = true
k-head (g ∷ _) = is-k-gate g

-- span-k is Data.List.Base.spanᵇ not-k, which is what optimize-go
-- used before it was written out in Kopt.Synth: the behaviour of
-- optimize-gp is unchanged by that rewriting.
span-k-≡ : (c : Circuit) -> span-k c ≡ List.spanᵇ not-k c
span-k-≡ [] = refl
span-k-≡ (K₀ ∷ c) = refl
span-k-≡ (K₁ ∷ c) = refl
span-k-≡ (X₀ ∷ c) = cong (span-k-cons X₀) (span-k-≡ c)
span-k-≡ (X₁ ∷ c) = cong (span-k-cons X₁) (span-k-≡ c)
span-k-≡ (Z₀ ∷ c) = cong (span-k-cons Z₀) (span-k-≡ c)
span-k-≡ (Z₁ ∷ c) = cong (span-k-cons Z₁) (span-k-≡ c)
span-k-≡ (S₀ ∷ c) = cong (span-k-cons S₀) (span-k-≡ c)
span-k-≡ (S₁ ∷ c) = cong (span-k-cons S₁) (span-k-≡ c)
span-k-≡ (CZ ∷ c) = cong (span-k-cons CZ) (span-k-≡ c)
span-k-≡ (CS ∷ c) = cong (span-k-cons CS) (span-k-≡ c)
span-k-≡ (CX ∷ c) = cong (span-k-cons CX) (span-k-≡ c)
span-k-≡ (XC ∷ c) = cong (span-k-cons XC) (span-k-≡ c)
span-k-≡ (Ex ∷ c) = cong (span-k-cons Ex) (span-k-≡ c)
span-k-≡ (Ii ∷ c) = cong (span-k-cons Ii) (span-k-≡ c)
span-k-≡ (CK ∷ c) = cong (span-k-cons CK) (span-k-≡ c)
span-k-≡ (KC ∷ c) = cong (span-k-cons KC) (span-k-≡ c)

span-k-++ : (c : Circuit) -> proj₁ (span-k c) ++ proj₂ (span-k c) ≡ c
span-k-++ [] = refl
span-k-++ (g ∷ c) = go (is-k-gate g)
  where
    go : (b : Bool) -> proj₁ (span-k-go g c b) ++ proj₂ (span-k-go g c b) ≡ g ∷ c
    go true = refl
    go false = cong (g ∷_) (span-k-++ c)

span-k-free : (c : Circuit) -> Over𝒢 c -> gp-circuit? (proj₁ (span-k c)) ≡ true
span-k-free [] _ = refl
span-k-free (g ∷ c) ov = go (is-k-gate g) refl
  where
    go : (b : Bool) -> is-k-gate g ≡ b -> gp-circuit? (proj₁ (span-k-go g c b)) ≡ true
    go true _ = refl
    go false e = cong₂ _∧_ (nonk-gp g (proj₁ (∧-true ov)) e) (span-k-free c (proj₂ (∧-true ov)))

span-k-rest-head : (c : Circuit) -> k-head (proj₂ (span-k c)) ≡ true
span-k-rest-head [] = refl
span-k-rest-head (g ∷ c) = go (is-k-gate g) refl
  where
    go : (b : Bool) -> is-k-gate g ≡ b -> k-head (proj₂ (span-k-go g c b)) ≡ true
    go true e = e
    go false _ = span-k-rest-head c

span-k-rest-len : (c : Circuit) -> rlen (proj₂ (span-k c)) Nat.≤ rlen c
span-k-rest-len [] = z≤n
span-k-rest-len (g ∷ c) = go (is-k-gate g)
  where
    go : (b : Bool) -> rlen (proj₂ (span-k-go g c b)) Nat.≤ suc (rlen c)
    go true = NatP.≤-refl
    go false = NatP.≤-trans (span-k-rest-len c) (NatP.n≤1+n (rlen c))

-- ----------------------------------------------------------------------
-- * What optimize-go achieves
--
-- The output implements the same operator, is over 𝒢, has the same
-- K-count, and satisfies the bounds of Corollary V.8. The last two
-- fields are the sharper bounds that hold when the input starts with
-- a K gate (or is empty); they are what makes the induction go
-- through, since the output is an alternating sequence of canonical
-- generalized permutations (≤ 9 gates, ≤ 1 CS gate) and K gates.

record Opt (c d : Circuit) : Set where
  constructor opt
  field
    opt-sem : ⟦ d ⟧ ≡ ⟦ c ⟧
    opt-𝒢 : Over𝒢 d
    opt-kc : kc d ≡ kc c
    opt-cs : csc d Nat.≤ suc (kc d)
    opt-len : rlen d Nat.≤ 10 Nat.* kc d Nat.+ 9
    opt-cs0 : k-head c ≡ true -> csc d Nat.≤ kc d
    opt-len0 : k-head c ≡ true -> rlen d Nat.≤ 10 Nat.* kc d
open Opt public

private
  opt-nil : Opt [] []
  opt-nil = opt refl refl refl z≤n z≤n (λ _ -> z≤n) (λ _ -> z≤n)

  eq10 : (k : ℕ) -> suc (10 Nat.* k Nat.+ 9) ≡ 10 Nat.* suc k
  eq10 k = trans (sym (NatP.+-suc (10 Nat.* k) 9))
                 (trans (NatP.+-comm (10 Nat.* k) 10) (sym (NatP.*-suc 10 k)))

  -- The step for a leading K gate: it is copied, and the sharper
  -- bounds hold for the result.
  opt-k-step : (n : ℕ) (g : Gate) (t : Circuit) -> is-k-gate g ≡ true ->
               Opt t (optimize-go n t) -> Opt (g ∷ t) (g ∷ optimize-go n t)
  opt-k-step n g t hk ih = opt sem g𝒢 kck css lens (λ _ -> cs0) (λ _ -> len0)
    where
      d' : Circuit
      d' = optimize-go n t
      sem : ⟦ g ∷ d' ⟧ ≡ ⟦ g ∷ t ⟧
      sem = cong (λ m -> ⟦ g ⟧g * m) (opt-sem ih)
      g𝒢 : Over𝒢 (g ∷ d')
      g𝒢 = cong₂ _∧_ (k-gate-in-𝒢 g hk) (opt-𝒢 ih)
      kck : kc (g ∷ d') ≡ kc (g ∷ t)
      kck = trans (k-gate-kc g hk d') (trans (cong suc (opt-kc ih)) (sym (k-gate-kc g hk t)))
      cs0 : csc (g ∷ d') Nat.≤ kc (g ∷ d')
      cs0 = subst₂ Nat._≤_ (sym (k-gate-csc g hk d')) (sym (k-gate-kc g hk d')) (opt-cs ih)
      css : csc (g ∷ d') Nat.≤ suc (kc (g ∷ d'))
      css = NatP.≤-trans cs0 (NatP.n≤1+n (kc (g ∷ d')))
      len0 : rlen (g ∷ d') Nat.≤ 10 Nat.* kc (g ∷ d')
      len0 = subst (λ m -> suc (rlen d') Nat.≤ 10 Nat.* m) (sym (k-gate-kc g hk d'))
                   (subst (λ m -> suc (rlen d') Nat.≤ m) (eq10 (kc d')) (s≤s (opt-len ih)))
      lens : rlen (g ∷ d') Nat.≤ 10 Nat.* kc (g ∷ d') Nat.+ 9
      lens = NatP.≤-trans len0 (NatP.m≤m+n (10 Nat.* kc (g ∷ d')) 9)

  -- The step for a leading K-free block: it is replaced by its
  -- canonical circuit, and the sharper bounds for the rest (which
  -- starts with a K gate) give the plain bounds for the result.
  opt-block-step : (n : ℕ) (c gp rest : Circuit) -> gp ++ rest ≡ c ->
                   gp-circuit? gp ≡ true -> k-head rest ≡ true -> (k-head c ≡ true -> ⊥) ->
                   Opt rest (optimize-go n rest) ->
                   Opt c (canonical-gp gp ++ optimize-go n rest)
  opt-block-step n c gp rest hsplit hfree hrest hnotk ih =
    opt sem g𝒢 kck css lens (λ h -> ⊥-elim (hnotk h)) (λ h -> ⊥-elim (hnotk h))
    where
      b : Circuit
      b = canonical-gp gp
      d' : Circuit
      d' = optimize-go n rest
      bp : GPCircuit ⟦ gp ⟧ b
      bp = canonical-gp-ok gp hfree
      kcd : kc (b ++ d') ≡ kc d'
      kcd = trans (kc-++ b d') (cong (λ x -> x Nat.+ kc d') (gpc-kc bp))
      kc-c : kc c ≡ kc rest
      kc-c = trans (cong kc (sym hsplit))
                   (trans (kc-++ gp rest)
                          (cong (λ x -> x Nat.+ kc rest) (gp-circuit-kc gp hfree)))
      sem : ⟦ b ++ d' ⟧ ≡ ⟦ c ⟧
      sem = trans (⟦⟧-++ b d')
              (trans (cong₂ _*_ (gpc-sem bp) (opt-sem ih))
                     (trans (sym (⟦⟧-++ gp rest)) (cong ⟦_⟧ hsplit)))
      g𝒢 : Over𝒢 (b ++ d')
      g𝒢 = over-𝒢-++ b d' (gpc-𝒢 bp) (opt-𝒢 ih)
      kck : kc (b ++ d') ≡ kc c
      kck = trans kcd (trans (opt-kc ih) (sym kc-c))
      css : csc (b ++ d') Nat.≤ suc (kc (b ++ d'))
      css = subst (λ x -> csc (b ++ d') Nat.≤ suc x) (sym kcd)
              (subst (λ x -> x Nat.≤ suc (kc d')) (sym (csc-++ b d'))
                     (NatP.+-mono-≤ (gpc-cs bp) (opt-cs0 ih hrest)))
      lens : rlen (b ++ d') Nat.≤ 10 Nat.* kc (b ++ d') Nat.+ 9
      lens = subst (λ x -> rlen (b ++ d') Nat.≤ 10 Nat.* x Nat.+ 9) (sym kcd)
               (subst (λ x -> x Nat.≤ 10 Nat.* kc d' Nat.+ 9) (sym (rlen-++ b d'))
                 (subst (λ x -> rlen b Nat.+ rlen d' Nat.≤ x) (NatP.+-comm 9 (10 Nat.* kc d'))
                        (NatP.+-mono-≤ (gpc-len bp) (opt-len0 ih hrest))))

-- The main induction: with enough fuel, optimize-go rewrites any
-- circuit over 𝒢 into an equivalent circuit over 𝒢 with the same
-- K-count and the counts of Corollary V.8.
optimize-go-ok : (n : ℕ) (c : Circuit) -> rlen c Nat.≤ n -> Over𝒢 c -> Opt c (optimize-go n c)
optimize-go-ok zero [] _ _ = opt-nil
optimize-go-ok zero (g ∷ t) () _
optimize-go-ok (suc n) [] _ _ = opt-nil
optimize-go-ok (suc n) (g ∷ t) (s≤s le) ov = dispatch (is-k-gate g) refl
  where
    ovg : in-𝒢 g ≡ true
    ovg = proj₁ (∧-true ov)
    ovt : Over𝒢 t
    ovt = proj₂ (∧-true ov)

    dispatch : (b : Bool) -> is-k-gate g ≡ b -> Opt (g ∷ t) (optimize-cons n g t b)
    dispatch true e = opt-k-step n g t e (optimize-go-ok n t le ovt)
    dispatch false e =
      subst (Opt (g ∷ t)) (sym spa)
            (opt-block-step n (g ∷ t) gp rest hsplit hfree hrest hnotk
                            (optimize-go-ok n rest rest-le rest-ov))
      where
        gp : Circuit
        gp = g ∷ proj₁ (span-k t)
        rest : Circuit
        rest = proj₂ (span-k t)
        spa : optimize-cons n g t false ≡ canonical-gp gp ++ optimize-go n rest
        spa = cong (optimize-span n) (cong (span-k-go g t) e)
        hsplit : gp ++ rest ≡ g ∷ t
        hsplit = cong (g ∷_) (span-k-++ t)
        hfree : gp-circuit? gp ≡ true
        hfree = cong₂ _∧_ (nonk-gp g ovg e) (span-k-free t ovt)
        hrest : k-head rest ≡ true
        hrest = span-k-rest-head t
        hnotk : k-head (g ∷ t) ≡ true -> ⊥
        hnotk h = false≢true (trans (sym e) h)
        rest-le : rlen rest Nat.≤ n
        rest-le = NatP.≤-trans (span-k-rest-len t) le
        rest-ov : Over𝒢 rest
        rest-ov = proj₂ (over-𝒢-split (proj₁ (span-k t)) rest
                                      (subst Over𝒢 (sym (span-k-++ t)) ovt))

-- ----------------------------------------------------------------------
-- * optimize-gp
--
-- Corollary V.8, the counting half, for the peephole optimization:
-- no hypothesis at all, for every input circuit.

optimize-gp′-ok : (c : Circuit) -> Over𝒢 c -> Opt c (optimize-gp′ c)
optimize-gp′-ok c ov = optimize-go-ok (rlen c) c NatP.≤-refl ov

optimize-gp-ok : (c : Circuit) -> Opt (desugar-ck c) (optimize-gp c)
optimize-gp-ok c = optimize-gp′-ok (desugar-ck c) (over-𝒢-desugar c)

-- optimize-gp preserves the operator exactly (part B of the task).
optimize-gp-sem : (c : Circuit) -> ⟦ optimize-gp c ⟧ ≡ ⟦ c ⟧
optimize-gp-sem c = trans (opt-sem (optimize-gp-ok c)) (desugar-ck-ok c)

optimize-gp-𝒢 : (c : Circuit) -> Over𝒢 (optimize-gp c)
optimize-gp-𝒢 c = opt-𝒢 (optimize-gp-ok c)

optimize-gp-kc : (c : Circuit) -> kc (optimize-gp c) ≡ kc (desugar-ck c)
optimize-gp-kc c = opt-kc (optimize-gp-ok c)

optimize-gp-cs : (c : Circuit) -> csc (optimize-gp c) Nat.≤ suc (kc (optimize-gp c))
optimize-gp-cs c = opt-cs (optimize-gp-ok c)

optimize-gp-len : (c : Circuit) -> rlen (optimize-gp c) Nat.≤ 10 Nat.* kc (optimize-gp c) Nat.+ 9
optimize-gp-len c = opt-len (optimize-gp-ok c)

-- ----------------------------------------------------------------------
-- * Corollary V.8 for the output of synth
--
-- These hold for every 4×4 matrix over 𝔻[i], whether or not it is a
-- Clifford+CS operator: whatever synth produces, it is a circuit over
-- the gate set 𝒢 of Definition I.1 with at most rkc+1 CS gates and at
-- most 10·rkc+9 gates.

synth-𝒢 : (A : Op) -> Over𝒢 (synth A)
synth-𝒢 A = go (synth-aux (suc (2 Nat.* lde A)) A)
  where
    go : (p : Circuit × Circuit) -> Over𝒢 (synth-of p)
    go (l , r) = optimize-gp-𝒢 (inv-circuit (r ++ l))

synth-cs : (A : Op) -> csc (synth A) Nat.≤ suc (kc (synth A))
synth-cs A = go (synth-aux (suc (2 Nat.* lde A)) A)
  where
    go : (p : Circuit × Circuit) -> csc (synth-of p) Nat.≤ suc (kc (synth-of p))
    go (l , r) = optimize-gp-cs (inv-circuit (r ++ l))

synth-len : (A : Op) -> rlen (synth A) Nat.≤ 10 Nat.* kc (synth A) Nat.+ 9
synth-len A = go (synth-aux (suc (2 Nat.* lde A)) A)
  where
    go : (p : Circuit × Circuit) -> rlen (synth-of p) Nat.≤ 10 Nat.* kc (synth-of p) Nat.+ 9
    go (l , r) = optimize-gp-len (inv-circuit (r ++ l))

-- ----------------------------------------------------------------------
-- * The descent hypothesis
--
-- Descends n A says that the recursion of synth-aux, started on A
-- with n units of fuel, gets to an operator of lde 0 whose canonical
-- generalized-permutation circuit implements it, passing only through
-- operators that have a pattern. This is what the paper's Lemma IV.1
-- (every Clifford+CS operator has a pattern), Lemma IV.4 with
-- Lemma IV.7 (the K-count prkc(A) ≤ 2·lde(A) of the complete path
-- descent) and Section III C (an operator of lde 0 is a generalized
-- permutation) together give for every two-qubit Clifford+CS
-- operator. Those three are NOT proved here; everything else is.

data Descends : ℕ -> Op -> Set where
  descends-gp : {n : ℕ} {A : Op} -> lde A ≡ 0 -> ⟦ gperm-circuit A ⟧ ≡ A -> Descends (suc n) A
  descends-step : {n : ℕ} {A : Op} {k : ℕ} {ld : LevelData} ->
                  lde A ≡ suc k -> level-at (suc k) A ≡ just ld ->
                  Descends n (⟦ proj₁ (decrease1-at ld A) ⟧ * A * ⟦ proj₂ (decrease1-at ld A) ⟧) ->
                  Descends (suc n) A

-- The lde-0 step, in the form in which the paper states it: the
-- operator is a generalized permutation (Section III C). The
-- constructor asks only for the weaker, decidable consequence that
-- gperm-circuit does implement it.
descends-gperm : {n : ℕ} {A : Op} -> lde A ≡ 0 -> IsGPerm A -> Descends (suc n) A
descends-gperm {A = A} hl hg = descends-gp hl (gperm-circuit-ok A hg)

-- The hypothesis for the fuel that synth actually uses.
Terminates : Op -> Set
Terminates A = Descends (suc (2 Nat.* lde A)) A

-- The invariant of synth-aux: ⟦L⟧·A·⟦R⟧ = 1.
Inverts : Circuit × Circuit -> Op -> Set
Inverts p A = ⟦ proj₁ p ⟧ * A * ⟦ proj₂ p ⟧ ≡ 1#

synth-aux-inverts : (n : ℕ) (A : Op) -> Descends n A -> Inverts (synth-aux n A) A
synth-aux-inverts (suc n) A (descends-gp hl hgp) =
  subst (λ p -> Inverts p A) (sym (cong (synth-step n A) hl)) base
  where
    gc : Circuit
    gc = gperm-circuit A
    base : (⟦ inv-circuit gc ⟧ * A) * ⟦ [] ⟧ ≡ 1#
    base = trans (mat-*-identityʳ (⟦ inv-circuit gc ⟧ * A))
                 (trans (cong (λ m -> ⟦ inv-circuit gc ⟧ * m) (sym hgp)) (inv-circuit-left gc))
synth-aux-inverts (suc n) A (descends-step {k = k} {ld = ld} hl hlev rec) =
  subst (λ p -> Inverts p A) (sym eqp) (go (synth-aux n B) (synth-aux-inverts n B rec))
  where
    l₁ : Circuit
    l₁ = proj₁ (decrease1-at ld A)
    r₁ : Circuit
    r₁ = proj₂ (decrease1-at ld A)
    B : Op
    B = (⟦ l₁ ⟧ * A) * ⟦ r₁ ⟧
    eqp : synth-aux (suc n) A ≡ synth-recurse n A (decrease1-at ld A)
    eqp = trans (cong (synth-step n A) hl) (cong (synth-level n A) hlev)
    go : (q : Circuit × Circuit) -> Inverts q B ->
         (⟦ proj₁ q ++ l₁ ⟧ * A) * ⟦ r₁ ++ proj₂ q ⟧ ≡ 1#
    go (lᵢ , rᵢ) h = begin
      (⟦ lᵢ ++ l₁ ⟧ * A) * ⟦ r₁ ++ rᵢ ⟧
        ≡⟨ cong₂ (λ x y -> (x * A) * y) (⟦⟧-++ lᵢ l₁) (⟦⟧-++ r₁ rᵢ) ⟩
      ((⟦ lᵢ ⟧ * ⟦ l₁ ⟧) * A) * (⟦ r₁ ⟧ * ⟦ rᵢ ⟧)
        ≡⟨ assoc-shuffle ⟦ lᵢ ⟧ ⟦ l₁ ⟧ A ⟦ r₁ ⟧ ⟦ rᵢ ⟧ ⟩
      (⟦ lᵢ ⟧ * B) * ⟦ rᵢ ⟧
        ≡⟨ h ⟩
      1# ∎
      where open ≡-Reasoning

-- From ⟦L⟧·A·⟦R⟧ = 1 to A = ⟦(R·L)⁻¹⟧.
private
  inv-lemma : (l r : Circuit) (A : Op) -> (⟦ l ⟧ * A) * ⟦ r ⟧ ≡ 1# ->
              ⟦ inv-circuit (r ++ l) ⟧ ≡ A
  inv-lemma l r A h = begin
    ⟦ inv-circuit (r ++ l) ⟧
      ≡⟨ cong ⟦_⟧ (inv-circuit-app r l) ⟩
    ⟦ inv-circuit l ++ inv-circuit r ⟧
      ≡⟨ ⟦⟧-++ (inv-circuit l) (inv-circuit r) ⟩
    ⟦ inv-circuit l ⟧ * ⟦ inv-circuit r ⟧
      ≡⟨ cong (λ m -> ⟦ inv-circuit l ⟧ * m) (sym (mat-*-identityˡ ⟦ inv-circuit r ⟧)) ⟩
    ⟦ inv-circuit l ⟧ * (1# * ⟦ inv-circuit r ⟧)
      ≡⟨ cong (λ m -> ⟦ inv-circuit l ⟧ * (m * ⟦ inv-circuit r ⟧)) (sym h) ⟩
    ⟦ inv-circuit l ⟧ * (((⟦ l ⟧ * A) * ⟦ r ⟧) * ⟦ inv-circuit r ⟧)
      ≡⟨ cong (λ m -> ⟦ inv-circuit l ⟧ * m) (mat-*-assoc (⟦ l ⟧ * A) ⟦ r ⟧ ⟦ inv-circuit r ⟧) ⟩
    ⟦ inv-circuit l ⟧ * ((⟦ l ⟧ * A) * (⟦ r ⟧ * ⟦ inv-circuit r ⟧))
      ≡⟨ cong (λ m -> ⟦ inv-circuit l ⟧ * ((⟦ l ⟧ * A) * m)) (inv-circuit-right r) ⟩
    ⟦ inv-circuit l ⟧ * ((⟦ l ⟧ * A) * 1#)
      ≡⟨ cong (λ m -> ⟦ inv-circuit l ⟧ * m) (mat-*-identityʳ (⟦ l ⟧ * A)) ⟩
    ⟦ inv-circuit l ⟧ * (⟦ l ⟧ * A)
      ≡⟨ sym (mat-*-assoc ⟦ inv-circuit l ⟧ ⟦ l ⟧ A) ⟩
    (⟦ inv-circuit l ⟧ * ⟦ l ⟧) * A
      ≡⟨ cong (λ m -> m * A) (inv-circuit-left l) ⟩
    1# * A
      ≡⟨ mat-*-identityˡ A ⟩
    A ∎
    where open ≡-Reasoning

-- Correctness of synth, given that the descent terminates within the
-- fuel: the circuit implements A exactly, global phase included.
synth-correct : (A : Op) -> Terminates A -> ⟦ synth A ⟧ ≡ A
synth-correct A d = go (synth-aux (suc (2 Nat.* lde A)) A) (synth-aux-inverts _ A d)
  where
    go : (p : Circuit × Circuit) -> Inverts p A -> ⟦ synth-of p ⟧ ≡ A
    go (l , r) h = trans (optimize-gp-sem (inv-circuit (r ++ l))) (inv-lemma l r A h)

-- ----------------------------------------------------------------------
-- * The descent hypothesis is decidable
--
-- descends? runs exactly the recursion of synth-aux and reports
-- whether it ends at an operator of lde 0 that the canonical
-- generalized-permutation circuit implements. So Terminates A can be
-- established for any concrete A by evaluation (refl), and
-- synth-correct-check then gives ⟦synth A⟧ = A.

descends? : ℕ -> Op -> Bool
descends-step? : ℕ -> Op -> ℕ -> Bool
descends-level? : ℕ -> Op -> Maybe LevelData -> Bool

descends? zero A = false
descends? (suc n) A = descends-step? n A (lde A)

descends-step? n A zero = ⟦ gperm-circuit A ⟧ == A
descends-step? n A (suc k) = descends-level? n A (level-at (suc k) A)

descends-level? n A nothing = false
descends-level? n A (just ld) =
  descends? n (⟦ proj₁ (decrease1-at ld A) ⟧ * A * ⟦ proj₂ (decrease1-at ld A) ⟧)

descends?-sound : (n : ℕ) (A : Op) -> descends? n A ≡ true -> Descends n A
descends-step?-sound : (n : ℕ) (A : Op) (l : ℕ) -> lde A ≡ l ->
                       descends-step? n A l ≡ true -> Descends (suc n) A
descends-level?-sound : (n : ℕ) (A : Op) (k : ℕ) -> lde A ≡ suc k -> (x : Maybe LevelData) ->
                        level-at (suc k) A ≡ x -> descends-level? n A x ≡ true -> Descends (suc n) A

descends?-sound zero A ()
descends?-sound (suc n) A h = descends-step?-sound n A (lde A) refl h

descends-step?-sound n A zero hl h = descends-gp hl (==⇒≡ h)
descends-step?-sound n A (suc k) hl h =
  descends-level?-sound n A k hl (level-at (suc k) A) refl h

descends-level?-sound n A k hl nothing _ ()
descends-level?-sound n A k hl (just ld) hlev h =
  descends-step hl hlev (descends?-sound n _ h)

-- Is the fuel of synth enough for A?
terminates? : Op -> Bool
terminates? A = descends? (suc (2 Nat.* lde A)) A

terminates?-sound : (A : Op) -> terminates? A ≡ true -> Terminates A
terminates?-sound A h = descends?-sound (suc (2 Nat.* lde A)) A h

-- Correctness of synth from a computation.
synth-correct-check : (A : Op) -> terminates? A ≡ true -> ⟦ synth A ⟧ ≡ A
synth-correct-check A h = synth-correct A (terminates?-sound A h)

-- ----------------------------------------------------------------------
-- * Consequences in the language of Section V

-- synth A is a circuit over 𝒢 implementing A: its raw K-count is a
-- K-count of A in the sense of Definition V.1.
synth-implements : (A : Op) -> terminates? A ≡ true -> Implements A (synth A)
synth-implements = synth-correct-check

synth-has-kcount : (A : Op) -> terminates? A ≡ true -> HasKCount A (kc (synth A))
synth-has-kcount A h = synth A , synth-𝒢 A , synth-correct-check A h , refl

-- With Table II (kc (synth A) = prkc A, checked on the authors' data
-- set in Test.KoptSynthRun but not proved), this is the hypothesis of
-- Kopt.Optimality's lemma-IV-9 and cor-V-8-K-optimal.
synth-has-prkc : (A : Op) -> terminates? A ≡ true -> kc (synth A) ≡ prkc A ->
                 HasKCount A (prkc A)
synth-has-prkc A h e = synth A , synth-𝒢 A , synth-correct-check A h , e

-- Note. terminates? A is decidable, so for a concrete A the
-- hypothesis of synth-correct-check is discharged by "refl". Such
-- sample evaluations are deliberately not done in this module: its
-- exhaustive check over the 6144 generalized permutations already
-- uses most of the type checker's heap.
