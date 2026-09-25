-- Checks of Kopt.Patterns and Kopt.Synth (Section IV of the paper)
-- that the type checker can do: the six pattern matrices, the
-- arithmetic of ℤ[i]/(γ²), Lemma IV.1 and the refinements on small
-- operators, and synth on operators of lde 0, 1 and 2.
--
-- The exhaustive checks are done by execution instead, in
-- Test.KoptSynthRun (12000 operators of lde up to 152, from the
-- authors' data file).
--
-- As in Test.KoptGates, equalities of 4×4 matrices are stated as
-- boolean tests "m == m'" and proved by refl, which is much cheaper
-- for the conversion checker than a propositional equality.

{-# OPTIONS --without-K --safe #-}

module Test.KoptSynth where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Bool.ListAction using (all ; any ; and)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Patterns
open import Kopt.Synth

-- ----------------------------------------------------------------------
-- * The six patterns (Lemma IV.1)

-- There are seven cases and they are pairwise distinct.
_ : Data.List.Base.length six-cases ≡ 7
_ = refl

_ : and (map (λ p -> p == p) six-cases) ≡ true
_ = refl

-- Pattern (iv)ᵀ really is the transpose of (iv), and the other
-- patterns are symmetric.
_ : (pattern-matrix IVt == matrix-transpose (pattern-matrix IV)) ≡ true
_ = refl
_ : (pattern-matrix I == matrix-transpose (pattern-matrix I)) ≡ true
_ = refl
_ : (pattern-matrix II == matrix-transpose (pattern-matrix II)) ≡ true
_ = refl
_ : (pattern-matrix III == matrix-transpose (pattern-matrix III)) ≡ true
_ = refl
_ : (pattern-matrix VI == matrix-transpose (pattern-matrix VI)) ≡ true
_ = refl

-- Pattern (v) is the transpose of (v) up to a permutation of rows and
-- columns: transposing is the same as exchanging the two halves.
_ : (matrix-transpose (pattern-matrix V) == permute-matrix (2 , 3 , 0 , 1) (2 , 3 , 0 , 1) (pattern-matrix V)) ≡ true
_ = refl

-- The numbers of 1s in the patterns: 4, 4, 8, 8, 8, 12, 16.
_ : map (λ p -> Data.List.Base.length (Data.List.Base.filterᵇ (λ b -> b == Odd) (matrix-entries (pattern-matrix p)))) six-cases
      ≡ 4 ∷ 4 ∷ 8 ∷ 8 ∷ 12 ∷ 16 ∷ 8 ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- * Arithmetic in ℤ[i]/(γ²) (Section II B)

-- 10 is the unit, 00 is zero, every element is its own additive
-- inverse, and multiplication by 01 is a right shift.
all-r2 : List R2
all-r2 = r2-zero ∷ r2-one ∷ r2-shift ∷ r2-i ∷ []

_ : all (λ x -> (r2-one r2* x) == x) all-r2 ≡ true
_ = refl
_ : all (λ x -> (r2-zero r2* x) == r2-zero) all-r2 ≡ true
_ = refl
_ : all (λ x -> (x r2+ x) == r2-zero) all-r2 ≡ true
_ = refl
_ : ((r2-shift r2* r2-one) == r2-shift) ≡ true
_ = refl
_ : ((r2-shift r2* r2-shift) == r2-zero) ≡ true
_ = refl
_ : ((r2-i r2* r2-i) == (Odd ∷ Even ∷ [])) ≡ true   -- i² = -1 and ρ₂(-1) = 10
_ = refl

-- ρ₂ is the residue of Kopt.Base, and ρ₂(i) = 11 (Section II B).
_ : ρ 2 i ≡ r2-i
_ = refl
_ : ρ 2 (- i) ≡ r2-i
_ = refl
_ : ρ 2 1 ≡ r2-one
_ = refl
_ : ρ 2 (- 1) ≡ r2-one
_ = refl
_ : ρ 2 γ ≡ r2-shift
_ = refl
_ : ρ 2 0 ≡ r2-zero
_ = refl

-- ----------------------------------------------------------------------
-- * Sample operators

-- A generalized permutation (lde 0), and operators of lde 1 and 2.
gp1 : Matrix 4 4 DComplex
gp1 = gperm-matrix 1 0 3 2 0 1 2 3

k1-op ck-op kc-op : Matrix 4 4 DComplex
k1-op = ⟦ K₁ ∷ [] ⟧
ck-op = ⟦ CK ∷ [] ⟧
kc-op = ⟦ KC ∷ [] ⟧

k0k1-op cscirc-op cxcirc-op : Matrix 4 4 DComplex
k0k1-op = ⟦ K₀ ∷ K₁ ∷ [] ⟧
cscirc-op = ⟦ K₁ ∷ CS ∷ K₁ ∷ [] ⟧
cxcirc-op = ⟦ K₀ ∷ CX ∷ K₀ ∷ [] ⟧

-- Their ldes.
_ : lde gp1 ≡ 0
_ = refl
_ : lde k1-op ≡ 1
_ = refl
_ : lde ck-op ≡ 1
_ = refl
_ : lde k0k1-op ≡ 2
_ = refl
_ : lde cscirc-op ≡ 1
_ = refl
_ : lde cxcirc-op ≡ 2
_ = refl

-- Their patterns. K₁ acts on two disjoint pairs of rows, so it has
-- two diagonal 2×2 blocks: pattern (iii). CK leaves the first two
-- rows integral, so only one 2×2 block is odd: pattern (ii).
_ : patof gp1 ≡ just I
_ = refl
_ : patof k1-op ≡ just III
_ = refl
_ : patof ck-op ≡ just II
_ = refl
_ : patof kc-op ≡ just II
_ = refl

-- Every generalized permutation has pattern (i) and lde 0
-- (Lemma IV.1).
_ : patof 1 ≡ just I
_ = refl
_ : patof ⟦ CS ∷ [] ⟧ ≡ just I
_ = refl
_ : patof ⟦ Ex ∷ S₀ ∷ CS ∷ [] ⟧ ≡ just I
_ = refl

-- ----------------------------------------------------------------------
-- * Lemma IV.1 holds for the circuits that lemma-six returns
--
-- This also checks the optimization of Kopt.Patterns: lemma-six
-- permutes the residue matrix instead of multiplying by permutation
-- matrices over 𝔻[i].

lemma-six-ok : Matrix 4 4 DComplex -> Bool
lemma-six-ok m with lemma-six m
... | nothing = false
... | just (p , l , r) =
      (residue1-matrix (lde m) (⟦ l ⟧ * m * ⟦ r ⟧) == pattern-matrix p)
        ∧ (kc l == 0) ∧ (kc r == 0) ∧ (csc l == 0) ∧ (csc r == 0)

_ : lemma-six-ok k1-op ≡ true
_ = refl
_ : lemma-six-ok ck-op ≡ true
_ = refl
_ : lemma-six-ok kc-op ≡ true
_ = refl
_ : lemma-six-ok k0k1-op ≡ true
_ = refl
_ : lemma-six-ok cscirc-op ≡ true
_ = refl
_ : lemma-six-ok cxcirc-op ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * The refinements put ρ₂ in the documented normal form

-- Kopt.Patterns.refine-normal-form? checks that the ρˡ₂ residue of
-- ⟦L⟧·A·⟦R⟧ is one of the normal forms documented in the authors'
-- code (their test_refine_ii, ..., test_refine_vi).
refine-ok : Matrix 4 4 DComplex -> Bool
refine-ok = refine-normal-form?

-- ρ₂ is invariant under conjugation (Section II B), but ρˡ₂ is not
-- invariant under adjoints: γ† = -iγ, so (γˡA)† = (-i)ˡγˡA† and
-- hence ρˡ₂(A†) = ρ₂(iˡ)·ρˡ₂(A)ᵀ, with ρ₂(iˡ) = 11 for odd l. This
-- is why the normal form of case (iv)ᵀ -- which is obtained by
-- refining the adjoint -- carries an extra factor of i at odd lde,
-- a factor that the authors' comment for refine_ivt omits.
even-nat : ℕ -> Bool
even-nat zero = true
even-nat (suc zero) = false
even-nat (suc (suc n)) = even-nat n

i-phase : ℕ -> R2
i-phase l = if even-nat l then r2-one else r2-i

adjoint-res-ok : ℕ -> Matrix 4 4 DComplex -> Bool
adjoint-res-ok l m =
  residue-matrix l 2 (adjoint m)
    == matrix-map (i-phase l r2*_) (matrix-transpose (residue-matrix l 2 m))

_ : adjoint-res-ok 1 k1-op ≡ true
_ = refl
_ : adjoint-res-ok 2 k1-op ≡ true
_ = refl
_ : adjoint-res-ok 3 k1-op ≡ true
_ = refl
_ : adjoint-res-ok 2 cxcirc-op ≡ true
_ = refl
_ : adjoint-res-ok 3 cxcirc-op ≡ true
_ = refl

_ : refine-ok k1-op ≡ true
_ = refl
_ : refine-ok ck-op ≡ true
_ = refl
_ : refine-ok kc-op ≡ true
_ = refl
_ : refine-ok k0k1-op ≡ true
_ = refl
_ : refine-ok cscirc-op ≡ true
_ = refl
_ : refine-ok cxcirc-op ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- ** The unitarity-restricted normal forms
--
-- normal-forms II 1 leaves the bottom right 2×2 block of ρ¹₂ free and
-- so lists 16 matrices; only two of them can occur for a unitary
-- operator (Kopt.Patterns.normal-forms-unitary). The restricted list
-- is a sublist of the unrestricted one, so it is a sharper check; the
-- two operators of pattern (ii) at lde 1 above pass it, and so do all
-- 12000 operators of the data file (check (i) of Test.KoptSynthRun).

_ : Data.List.Base.length (normal-forms II 1) ≡ 16
_ = refl
_ : Data.List.Base.length (normal-forms-unitary II 1) ≡ 2
_ = refl

-- Only the free bits differ, and the two restricted forms are among
-- the sixteen.
sublist-of-normal-forms : SixCases -> ℕ -> Bool
sublist-of-normal-forms p l =
  all (λ m -> any (λ m' -> m == m') (normal-forms p l)) (normal-forms-unitary p l)

_ : sublist-of-normal-forms II 1 ≡ true
_ = refl
_ : sublist-of-normal-forms III 1 ≡ true
_ = refl
_ : sublist-of-normal-forms VI 3 ≡ true
_ = refl

-- The two unitary forms are the ones whose bottom right block is
-- γ times a 2×2 permutation matrix: diagonal or antidiagonal.
_ : all (λ m -> any (λ m' -> m == m') pii2k1-unitary)
        (pii2k1 Odd Even Even Odd ∷ pii2k1 Even Odd Odd Even ∷ []) ≡ true
_ = refl

refine-unit-ok : Matrix 4 4 DComplex -> Bool
refine-unit-ok = refine-normal-form-unitary?

_ : refine-unit-ok k1-op ≡ true
_ = refl
_ : refine-unit-ok ck-op ≡ true       -- pattern (ii) at lde 1
_ = refl
_ : refine-unit-ok kc-op ≡ true       -- pattern (ii) at lde 1
_ = refl
_ : refine-unit-ok k0k1-op ≡ true
_ = refl
_ : refine-unit-ok cscirc-op ≡ true
_ = refl
_ : refine-unit-ok cxcirc-op ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Table II and Corollary IV.8

-- prkc is 2l, 2l-1 or 2l-2 depending on the pattern.
_ : prkc gp1 ≡ 0
_ = refl
_ : prkc k1-op ≡ 1          -- pattern (iii), l = 1
_ = refl
_ : prkc ck-op ≡ 2          -- pattern (ii), l = 1
_ = refl
-- K₀K₁ has all entries ±1/2, so its pattern is (vi): prkc = 2l-2 = 2.
_ : patof k0k1-op ≡ just VI
_ = refl
_ : prkc k0k1-op ≡ 2
_ = refl

-- Corollary IV.8: the lde can be recovered from prkc and the pattern.
lde-ok : Matrix 4 4 DComplex -> Bool
lde-ok m = lde-from-prkc m == lde m

_ : lde-ok gp1 ≡ true
_ = refl
_ : lde-ok k1-op ≡ true
_ = refl
_ : lde-ok ck-op ≡ true
_ = refl
_ : lde-ok k0k1-op ≡ true
_ = refl
_ : lde-ok cscirc-op ≡ true
_ = refl
_ : lde-ok cxcirc-op ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * synth

-- The circuit synth A implements A exactly (including the global
-- phase), it has exactly prkc A = kc A K gates, and at most
-- kc A + 1 CS gates (Corollary V.8).
synth-ok : Matrix 4 4 DComplex -> Bool
synth-ok m = go (synth m)
  where
    go : Circuit -> Bool
    go c = (⟦ c ⟧ == m)
             ∧ (kc c == prkc m)
             ∧ (csc c Nat.≤ᵇ suc (kc c))
             ∧ (rlen c Nat.≤ᵇ (10 Nat.* kc c Nat.+ 9))

_ : synth-ok 1 ≡ true
_ = refl
_ : synth-ok gp1 ≡ true
_ = refl
_ : synth-ok ⟦ Ex ∷ S₀ ∷ CS ∷ [] ⟧ ≡ true
_ = refl
_ : synth-ok k1-op ≡ true
_ = refl
_ : synth-ok ck-op ≡ true
_ = refl
_ : synth-ok kc-op ≡ true
_ = refl
_ : synth-ok k0k1-op ≡ true
_ = refl
_ : synth-ok cscirc-op ≡ true
_ = refl
_ : synth-ok cxcirc-op ≡ true
_ = refl

-- The K gates of synth K₁ and synth CK, spelled out: one K gate for
-- K₁ (pattern (iii) at lde 1) and two for CK (pattern (ii) at lde 1,
-- which is resolved by a CK gate, i.e. by two K gates).
_ : kc (synth k1-op) ≡ 1
_ = refl
_ : kc (synth ck-op) ≡ 2
_ = refl
_ : csc (synth ck-op) ≡ 1
_ = refl

-- optimize-gp does not change the operator, nor the K-count, and it
-- removes the controlled-K gates.
optimize-ok : Circuit -> Bool
optimize-ok c = go (optimize-gp c)
  where
    go : Circuit -> Bool
    go c' = (⟦ c' ⟧ == ⟦ c ⟧) ∧ (kc c' == kc (desugar-ck c))

_ : optimize-ok (X₀ ∷ CK ∷ X₀ ∷ []) ≡ true
_ = refl
_ : optimize-ok (S₀ ∷ Z₁ ∷ CS ∷ Ex ∷ CX ∷ []) ≡ true
_ = refl
_ : optimize-ok (K₁ ∷ S₁ ∷ K₀ ∷ []) ≡ true
_ = refl
