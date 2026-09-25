-- Checks of Kopt.Descent, Kopt.Optimality, Kopt.NormalForms and
-- Kopt.OptInduction (Section V of Bian & Feng) that the type checker
-- can do.
--
-- The big exhaustive checks are not here: they are part of the modules
-- themselves, where the type checker runs them and where they are used
-- to prove the corresponding statements.
--
--   * gp-check-all (Kopt.Optimality): each of the 24·256 = 6144
--     generalized permutations is implementable by at most 9 gates, at
--     most one CS gate and no K gate.
--   * inv-perm-ok, v3-ok, v4-ok, v6-ok (Kopt.NormalForms): the
--     residue-level enumerations of Lemmas V.3, V.4 and V.6.
--
-- What this module checks is the *sizes* of the search spaces those
-- enumerations run over -- which is what makes them exhaustive -- the
-- gate/generalized-permutation table, the edges of Figure 1, the
-- potential of Table II, and the arithmetic of Corollary V.10 and
-- Remark V.11.
--
-- As in the other Kopt tests, equalities of 4×4 matrices are stated as
-- boolean tests "m == m'" and proved by refl, which is much cheaper for
-- the conversion checker than a propositional equality.

{-# OPTIONS --without-K --safe #-}

module Test.KoptOptimality where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; not)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_ ; length)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; _∸_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Patterns
open import Kopt.Synth
open import Kopt.Descent
open import Kopt.Optimality
open import Kopt.NormalForms
open import Kopt.OptInduction

-- ----------------------------------------------------------------------
-- * The enumerations of Kopt.Descent
--
-- These are what makes the exhaustive checks proofs: the search space
-- really is the whole of it.

_ : length all-pos ≡ 4
_ = refl

_ : length all-phase ≡ 4
_ = refl

_ : length all-pos4 ≡ 256
_ = refl

_ : length all-phase4 ≡ 256
_ = refl

-- The 24 permutations of the four coordinates.
_ : length all-perm4 ≡ 24
_ = refl

-- The 6144 generalized permutations.
_ : length (pairs all-perm4 all-phase4) ≡ 6144
_ = refl

-- Every tuple of the enumeration is a permutation, and the identity
-- is one of them.
_ : all-of distinct4p all-perm4 ≡ true
_ = refl

_ : distinct4p id4p ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * The gates that are generalized permutations

-- The table gp-of-gate, spelled out: each gate of 𝒢 other than K₀,
-- K₁ is the generalized permutation with the given permutation and
-- phases.
gate-ok : Gate -> Bool
gate-ok g = ⟦ g ⟧g == gp-mat (gp-of-gate g)

_ : all-of gate-ok (X₀ ∷ X₁ ∷ Z₀ ∷ Z₁ ∷ S₀ ∷ S₁ ∷ CZ ∷ CS ∷ CX ∷ XC ∷ Ex ∷ Ii ∷ []) ≡ true
_ = refl

-- K₀, K₁, CK and KC are not generalized permutations.
_ : all-of (λ g -> not (is-gperm ⟦ g ⟧g)) (K₀ ∷ K₁ ∷ CK ∷ KC ∷ []) ≡ true
_ = refl

-- K₀ = Ex·K₁·Ex (used for Equation (3)).
_ : (⟦ K₀ ⟧g == ⟦ Ex ∷ K₁ ∷ Ex ∷ [] ⟧) ≡ true
_ = refl

-- K₁·K₁ = -i·(I⊗I), so K₁⁻¹ = i·K₁ (used to invert a descent).
_ : (⟦ K₁ ∷ K₁ ∷ [] ⟧ == gp-mat minus-i-gp) ≡ true
_ = refl

_ : (gp-mat i-gp * gp-mat minus-i-gp == 1#) ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Remark II.10: only K changes the lde

-- A sample operator of lde 1.
sample : Op
sample = ⟦ K₁ ⟧g

_ : lde sample ≡ 1
_ = refl

-- Every gate that is a generalized permutation preserves the lde,
-- on the left and on the right.
lde-stable : Gate -> Bool
lde-stable g = (lde (⟦ g ⟧g * sample) Nat.≡ᵇ 1) ∧ (lde (sample * ⟦ g ⟧g) Nat.≡ᵇ 1)

_ : all-of lde-stable (X₀ ∷ X₁ ∷ Z₀ ∷ Z₁ ∷ S₀ ∷ S₁ ∷ CZ ∷ CS ∷ CX ∷ XC ∷ Ex ∷ Ii ∷ []) ≡ true
_ = refl

-- K does change it.
_ : lde (⟦ K₁ ⟧g * sample) ≡ 0
_ = refl

-- ----------------------------------------------------------------------
-- * Figure 1
--
-- The undashed (lde-decreasing) edges are iii→i, iv→ii, iv→v,
-- vi→iii, vi→iv; the dashed (lde-preserving) ones are ii→iv, iii→vi,
-- v→iv.

_ : fig1-drop III I ≡ true
_ = refl
_ : fig1-drop IV II ≡ true
_ = refl
_ : fig1-drop IV V ≡ true
_ = refl
_ : fig1-drop VI III ≡ true
_ = refl
_ : fig1-drop VI IV ≡ true
_ = refl
_ : fig1-keep II IV ≡ true
_ = refl
_ : fig1-keep III VI ≡ true
_ = refl
_ : fig1-keep V IV ≡ true
_ = refl

-- There is no K-count-1 edge out of (i), and none into (vi) that
-- decreases the lde.
_ : all-of (λ p -> not (fig1-drop I p) ∧ not (fig1-keep I p))
           (I ∷ II ∷ III ∷ IV ∷ IVt ∷ V ∷ VI ∷ []) ≡ true
_ = refl

_ : all-of (λ p -> not (fig1-drop p VI)) (I ∷ II ∷ III ∷ IV ∷ IVt ∷ V ∷ VI ∷ []) ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * The potential of Kopt.OptInduction and Table II
--
-- pot p l = 2l - rank p reproduces Table II (prkc-of of Kopt.Synth)
-- for every pattern other than (i), where the two differ (pot is 2l
-- and prkc-of is 0) but where only l = 0 occurs, by Lemma IV.1.

_ : List.map (λ p -> pat-rank (just p)) six-cases ≡ (0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ [])
_ = refl

_ : all-of (λ p -> all-of (λ l -> pot (just p) l Nat.≡ᵇ prkc-of p l) (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []))
           (II ∷ III ∷ IV ∷ IVt ∷ V ∷ VI ∷ []) ≡ true
_ = refl

-- The potential at lde 0 is 0, whatever the pattern.
_ : all-of (λ p -> pot (just p) 0 Nat.≡ᵇ 0) six-cases ≡ true
_ = refl

_ : pot nothing 0 ≡ 0
_ = refl

-- ----------------------------------------------------------------------
-- * Corollary V.10 and Remark V.11, numerically
--
-- The corrected bound (k+1)/cs ≤ 2 + 6/(k-2) holds at k = 4, cs = 1
-- with equality, while the bound 2 + 4/(k-2) printed in the paper
-- fails there: 5 > 4.

ratio-ok ratio-paper : ℕ -> ℕ -> Bool
ratio-ok k s = (suc k Nat.* (k ∸ 2)) Nat.≤ᵇ ((2 Nat.* (k ∸ 2) Nat.+ 6) Nat.* s)
ratio-paper k s = (suc k Nat.* (k ∸ 2)) Nat.≤ᵇ ((2 Nat.* (k ∸ 2) Nat.+ 4) Nat.* s)

-- The three extremal pairs (k, cs) that occur in the authors' data
-- set: (4,1), (6,2) and (8,3).
_ : all-of (λ ks -> ratio-ok (proj₁ ks) (proj₂ ks)) ((4 , 1) ∷ (6 , 2) ∷ (8 , 3) ∷ []) ≡ true
_ = refl

_ : all-of (λ ks -> not (ratio-paper (proj₁ ks) (proj₂ ks)))
           ((4 , 1) ∷ (6 , 2) ∷ (8 , 3) ∷ []) ≡ true
_ = refl

-- They do satisfy the hypothesis k ≤ 2·cs + 2 of Theorem V.9.
_ : all-of (λ ks -> proj₁ ks Nat.≤ᵇ (2 Nat.* proj₂ ks Nat.+ 2))
           ((4 , 1) ∷ (6 , 2) ∷ (8 , 3) ∷ []) ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * The residue-level enumerations of Kopt.NormalForms
--
-- The checks are run by the type checker inside that module; here we
-- record the sizes of the finite sets they range over.

-- The seven cases of Lemma IV.1 and the 576 pairs of permutations.
_ : length six-cases ≡ 7
_ = refl

_ : length (pairs all-perms all-perms) ≡ 576
_ = refl

-- The permutation invariant of the seven pattern matrices: the sum of
-- the squares of the row weights, and the same for the columns.
_ : List.map (λ p -> inv (pattern-matrix p)) six-cases
      ≡ ((4 , 4) ∷ (8 , 8) ∷ (16 , 16) ∷ (32 , 16) ∷ (40 , 40) ∷ (64 , 64) ∷ (16 , 32) ∷ [])
_ = refl

-- Lemma V.4: an lde-raising K gate doubles the odd entries. With the
-- pairing {0,1},{2,3} only pattern (i) has a 1-ascent, and it goes to
-- pattern (iii) (invariant (16,16)); the other six patterns have their
-- rows already paired, so the doubled matrix is zero.
_ : inv (double-rows (pattern-matrix I)) ≡ (16 , 16)
_ = refl

_ : all-of (λ p -> double-rows (pattern-matrix p) == z2-zero)
           (II ∷ III ∷ IV ∷ IVt ∷ V ∷ VI ∷ []) ≡ true
_ = refl

-- With the pairing {0,2},{1,3} the ascent out of pattern (iii) reaches
-- pattern (vi) (invariant (64,64)), which is the edge (vi) → (iii) of
-- Figure 1 read backwards.
_ : inv (double-rows (permute-matrix (0 , 2 , 1 , 3) (0 , 1 , 2 , 3) (pattern-matrix III)))
      ≡ (64 , 64)
_ = refl

-- Pattern (vi) has no 1-ascent at all, on either side: this is why no
-- undashed edge of Figure 1 ends in (vi).
_ : all-of (λ xy -> (double-rows (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix VI))
                       == z2-zero)
                  ∧ (double-cols (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix VI))
                       == z2-zero))
           (pairs all-perms all-perms) ≡ true
_ = refl

-- Lemma V.6: the 4 pattern-(vi) normal forms (with their transposes)
-- and the 24·16 = 384 residue classes of a left generalized
-- permutation.
_ : length r2-units ≡ 2
_ = refl

_ : length unit4s ≡ 16
_ = refl

_ : length left-classes ≡ 384
_ = refl

_ : length vi-forms ≡ 4
_ = refl

-- Lemma V.3: the six normal forms for which the path descent spends
-- two K gates on one step of the lde -- the two unitary pattern-(ii)
-- forms at lde 1, the two at lde > 1, pattern (v) and pattern (iii) at
-- lde > 1.
_ : length lemma-V-3-forms ≡ 6
_ = refl

-- Unitarity cuts the 16 forms of normal-forms II 1 down to two.
_ : length (normal-forms II 1) ≡ 16
_ = refl

_ : length pii2k1-forms ≡ 2
_ = refl

_ : (pii2k1-unitary? Odd Even Even Odd ∧ pii2k1-unitary? Even Odd Odd Even) ≡ true
_ = refl

-- and exactly two: the other fourteen fail the test.
z2s : List Z2
z2s = Even ∷ Odd ∷ []

unitary-bits? : Z2 × Z2 × Z2 × Z2 -> Bool
unitary-bits? dg = pii2k1-unitary? (proj₁ dg) (proj₁ (proj₂ dg))
                                   (proj₁ (proj₂ (proj₂ dg))) (proj₂ (proj₂ (proj₂ dg)))

_ : length (pairs z2s (pairs z2s (pairs z2s z2s))) ≡ 16
_ = refl

_ : length (List.filterᵇ unitary-bits? (pairs z2s (pairs z2s (pairs z2s z2s)))) ≡ 2
_ = refl
