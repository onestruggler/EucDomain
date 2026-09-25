-- Sections IV B and IV C of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the transition of Lemma IV.4 (decrease1-lde, one step of Figure 1),
-- the synthesis algorithm itself (synth), the peephole optimization
-- that makes every K-free block of the output a canonical generalized
-- permutation (optimize-gp), and the K-count prkc of Lemma IV.7
-- (Table II) with its inverse of Corollary IV.8.
--
-- This is a port of the authors' Haskell module Kopt.hs
-- (decrease1_lde, synth', synth, optimize_gp', optimize_gp, kc, csc).
--
-- Totality. The authors' decrease1_lde raises an error on pattern
-- (i), and synth' and optimize_gp' are not structurally recursive.
-- Here:
--
--  * every partial case returns a documented default (usually the
--    pair of empty circuits), and
--  * synth-aux and optimize-gp take fuel. The fuel of synth is
--    2·lde(A) + 1, which is what the authors use and which is never
--    exhausted: the algorithm needs one step per K gate and the
--    K-count prkc(A) is at most 2·lde(A) (Lemma IV.7). The fuel of
--    optimize-gp is the length of its input, and each step of
--    optimize-gp consumes at least one gate.

{-# OPTIONS --without-K --safe #-}

module Kopt.Synth where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; not)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; _∸_ ; ⌈_/2⌉)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Patterns

-- The gate counts of Definition V.1 are defined in Kopt.Gates; they
-- are re-exported here because they belong to the interface of the
-- synthesis algorithm.
open import Kopt.Gates public using (kc ; csc ; rlen)

-- ----------------------------------------------------------------------
-- * One K gate of the descent (Lemma IV.4, Figure 1)

-- The authors' decrease1_lde. Despite the name, the resulting
-- operator ⟦L⟧·A·⟦R⟧ has lde l or l-1: the transitions of Figure 1
-- alternate between lde-preserving steps (ii → iv, iii → vi, v → iv)
-- and lde-decreasing ones (iv → ii or v, vi → iii or iv). Each step
-- uses exactly one K gate, except the step (ii) → (i) at lde 1, which
-- uses a CK gate, i.e. two K gates after desugaring.
decrease1-at : LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit
decrease1-at ld m with lev-pat ld
-- Pattern (i) means lde 0; the authors' code raises an error here.
... | I = [] , []
... | II with refine-at ld m
...   | (lref , rref) = if lev-lde ld Nat.≡ᵇ 1
                        then ((X₀ ∷ CK ∷ X₀ ∷ []) ++ lref , rref)
                        else ((K₁ ∷ S₁ ∷ []) ++ lref , rref)
decrease1-at ld m | III with refine-at ld m
...   | (lref , rref) = if lev-lde ld Nat.≡ᵇ 1
                        then ((K₁ ∷ []) ++ lref , rref)
                        else ((K₁ ∷ S₁ ∷ []) ++ lref , rref)
decrease1-at ld m | IV with refine-at ld m
...   | (lref , rref) = lref , rref ++ (K₁ ∷ [])
-- The authors compute decrease1_lde of the adjoint, which has pattern
-- (iv), and invert: (inv_cir (rref ++ [K1]), inv_cir lref), which is
-- ([K1,i] ++ L, R) for the (L,R) that refine-ivt returns.
decrease1-at ld m | IVt with refine-at ld m
...   | (lref , rref) = (K₁ ∷ Ii ∷ []) ++ lref , rref
decrease1-at ld m | V with refine-at ld m
...   | (lref , rref) = (K₁ ∷ []) ++ lref , rref
decrease1-at ld m | VI with refine-at ld m
...   | (lref , rref) = (K₁ ∷ []) ++ lref , rref

private
  -- Note: the case analyses on Maybe LevelData below are made by
  -- pattern matching in a helper function rather than by "with". A
  -- "with" makes the type checker evaluate its scrutinee, and the
  -- scrutinee level-at (suc k) m unfolds into the 24·24·7 search of
  -- lemma-six on a symbolic matrix, which exhausts the heap.
  decrease1-step : Maybe LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit
  decrease1-step nothing m = [] , []
  decrease1-step (just ld) m = decrease1-at ld m

-- The same, as a function of the operator (the authors'
-- decrease1_lde). For lde 0 the pattern is (i) and the result is the
-- pair of empty circuits.
decrease1-lde : Matrix 4 4 DComplex -> Circuit × Circuit
decrease1-lde m = decrease1-step (level-of m) m

-- ----------------------------------------------------------------------
-- * The synthesis algorithm (Section IV C)

-- A circuit for a generalized permutation; the empty circuit if the
-- matrix is not one (the authors' gperm_of raises an error). The
-- case analysis is in the auxiliary function gperm-circuit-of rather
-- than in a "with", so that Kopt.SynthProperties can compute with it
-- once gperm-of is known.
gperm-circuit-of : Maybe Circuit -> Circuit
gperm-circuit-of (just c) = c
gperm-circuit-of nothing = []

gperm-circuit : Matrix 4 4 DComplex -> Circuit
gperm-circuit m = gperm-circuit-of (gperm-of m)

-- The authors' synth': peel off one K gate at a time, until the
-- operator is a generalized permutation. Returns circuits L, R with
-- ⟦L⟧·A·⟦R⟧ = 1, so that A = ⟦L⟧⁻¹·⟦R⟧⁻¹. The first argument is
-- fuel: one unit per K gate, so 2·lde(A) + 1 always suffices.
--
-- The four steps are separate (public) functions rather than nested
-- "with"s and "where"s so that they can be reasoned about: see
-- Kopt.SynthProperties, where the induction is on the fuel.
synth-aux : ℕ -> Matrix 4 4 DComplex -> Circuit × Circuit
synth-step : ℕ -> Matrix 4 4 DComplex -> ℕ -> Circuit × Circuit
synth-level : ℕ -> Matrix 4 4 DComplex -> Maybe LevelData -> Circuit × Circuit
synth-recurse : ℕ -> Matrix 4 4 DComplex -> Circuit × Circuit -> Circuit × Circuit
synth-join : Circuit -> Circuit -> Circuit × Circuit -> Circuit × Circuit

synth-aux zero m = [] , []
synth-aux (suc n) m = synth-step n m (lde m)

-- lde 0: the operator is a generalized permutation, and the descent
-- is over.
synth-step n m zero = inv-circuit (gperm-circuit m) , []
synth-step n m l@(suc _) = synth-level n m (level-at l m)

-- A matrix without a pattern is not a Clifford+CS operator; the
-- authors' code raises an error.
synth-level n m nothing = [] , []
synth-level n m (just ld) = synth-recurse n m (decrease1-at ld m)

synth-recurse n m (l₁ , r₁) = synth-join l₁ r₁ (synth-aux n (⟦ l₁ ⟧ * m * ⟦ r₁ ⟧))

synth-join l₁ r₁ (lᵢ , rᵢ) = lᵢ ++ l₁ , r₁ ++ rᵢ

-- ----------------------------------------------------------------------
-- * Optimizing the generalized permutations (the authors' optimize_gp)

not-k : Gate -> Bool
not-k g = not (is-k-gate g)

-- The maximal K-free prefix of a circuit, and the rest. This is
-- Data.List.Base.spanᵇ not-k, written out (and with the case
-- analysis on is-k-gate in an auxiliary function) so that
-- Kopt.SynthProperties can reason about it.
span-k : Circuit -> Circuit × Circuit
span-k-go : Gate -> Circuit -> Bool -> Circuit × Circuit
span-k-cons : Gate -> Circuit × Circuit -> Circuit × Circuit

span-k [] = [] , []
span-k (g ∷ c) = span-k-go g c (is-k-gate g)

span-k-go g c true = [] , g ∷ c
span-k-go g c false = span-k-cons g (span-k c)

span-k-cons g (gp , rest) = (g ∷ gp) , rest

-- Replace a K-free circuit by the canonical circuit of the
-- generalized permutation it implements (at most 9 gates, at most
-- one CS gate). If the operator is not a generalized permutation --
-- which cannot happen for a K-free circuit over 𝒢 -- the block is
-- kept.
canonical-gp-of : Circuit -> Maybe Circuit -> Circuit
canonical-gp-of c (just c') = c'
canonical-gp-of c nothing = c

canonical-gp : Circuit -> Circuit
canonical-gp c = canonical-gp-of c (gperm-of ⟦ c ⟧)

-- The fuel is the number of gates; each step consumes at least one.
optimize-go : ℕ -> Circuit -> Circuit
optimize-cons : ℕ -> Gate -> Circuit -> Bool -> Circuit
optimize-span : ℕ -> Circuit × Circuit -> Circuit

optimize-go zero c = c
optimize-go (suc n) [] = []
optimize-go (suc n) (g ∷ t) = optimize-cons n g t (is-k-gate g)

optimize-cons n g t true = g ∷ optimize-go n t
optimize-cons n g t false = optimize-span n (span-k (g ∷ t))

optimize-span n (gp , rest) = canonical-gp gp ++ optimize-go n rest

-- Rewrite a circuit so that every maximal K-free block is the
-- canonical circuit of the generalized permutation it implements.
-- This does not change the operator, nor the number of K gates, and
-- it makes the CS-count of each block minimal.
optimize-gp′ : Circuit -> Circuit
optimize-gp′ c = optimize-go (rlen c) c

-- The authors' optimize_gp: desugar the controlled-K gates first.
optimize-gp : Circuit -> Circuit
optimize-gp c = optimize-gp′ (desugar-ck c)

-- ----------------------------------------------------------------------
-- * synth

-- Put the two halves of synth-aux together: from ⟦L⟧·A·⟦R⟧ = 1 we
-- get A = ⟦(R·L)⁻¹⟧, and then the K-free blocks are canonicalized.
synth-of : Circuit × Circuit -> Circuit
synth-of (l , r) = optimize-gp (inv-circuit (r ++ l))

-- The synthesis algorithm of Section IV C: given a two-qubit
-- Clifford+CS operator A, return a circuit implementing it exactly
-- (including the global phase, which the scalar gate i takes care
-- of). By Corollary V.8 the circuit has exactly prkc(A) = kc(A) K
-- gates, at most kc(A)+1 CS gates, and at most 10·kc(A)+9 gates.
synth : Matrix 4 4 DComplex -> Circuit
synth m = synth-of (synth-aux (suc (2 Nat.* lde m)) m)

-- ----------------------------------------------------------------------
-- * The K-count of the descent (Lemma IV.7, Table II)

-- Table II: the number of K gates on the complete path descent is
-- determined by the lde and the pattern.
prkc-of : SixCases -> ℕ -> ℕ
prkc-of I l = 0
prkc-of II l = 2 Nat.* l
prkc-of III l = 2 Nat.* l ∸ 1
prkc-of IV l = 2 Nat.* l ∸ 1
prkc-of IVt l = 2 Nat.* l ∸ 1
prkc-of V l = 2 Nat.* l
prkc-of VI l = 2 Nat.* l ∸ 2

private
  prkc-at : ℕ -> Matrix 4 4 DComplex -> ℕ
  prkc-at l m with level-at l m
  ... | nothing = 0
  ... | just ld = prkc-of (lev-pat ld) l

-- The K-count prkc(A) of the complete path descent of A, which by
-- Corollary V.8 is the optimal K-count kc(A).
prkc : Matrix 4 4 DComplex -> ℕ
prkc m = prkc-at (lde m) m

-- Corollary IV.8, read backwards: the lde is determined by prkc and
-- the pattern. If p is odd then lde = (p+1)/2; if p is even then
-- lde = p/2, except for pattern (vi), where lde = p/2 + 1.
lde-of-prkc : SixCases -> ℕ -> ℕ
lde-of-prkc VI p = suc ⌈ p /2⌉
lde-of-prkc I p = ⌈ p /2⌉
lde-of-prkc II p = ⌈ p /2⌉
lde-of-prkc III p = ⌈ p /2⌉
lde-of-prkc IV p = ⌈ p /2⌉
lde-of-prkc IVt p = ⌈ p /2⌉
lde-of-prkc V p = ⌈ p /2⌉

-- Corollary IV.8 for an operator: this recomputes lde A from its
-- pattern and its prkc, and so should be equal to lde A.
lde-from-prkc : Matrix 4 4 DComplex -> ℕ
lde-from-prkc m with level-of m
... | nothing = 0
... | just ld = lde-of-prkc (lev-pat ld) (prkc-of (lev-pat ld) (lev-lde ld))
