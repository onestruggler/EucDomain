-- Checks of Kopt.Permutations (Section III of the paper) that the
-- type checker can do: all 24 permutation circuits of Table I, and a
-- selection of diagonal unitaries and generalized permutations.
--
-- The exhaustive checks (all 256 diagonal unitaries, all 6144
-- generalized permutations, all 6144 commutations PD = D′P) are too
-- big for the type checker and are done by execution instead, in
-- Test.KoptPermutationsRun.
--
-- As in Test.KoptGates, equalities of 4×4 matrices are stated as
-- boolean tests "m == m'" and proved by refl, which is much cheaper
-- for the conversion checker than a propositional equality of
-- matrices.

{-# OPTIONS --without-K --safe #-}

module Test.KoptPermutations where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; length ; concatMap)
open import Data.Bool.ListAction using (all ; and)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations

-- ----------------------------------------------------------------------
-- * Table I: all 24 permutation circuits

-- ⟦perm-circuit p⟧ = perm-matrix p, with at most 3 gates and no K and
-- no CS gate, for each of the 24 permutations.
perm-ok : Tuple4 -> Bool
perm-ok p = (⟦ c ⟧ == perm-matrix-of p) ∧ (rlen c ≤ᵇ 3) ∧ (kc c == 0) ∧ (csc c == 0)
  where
    c : Circuit
    c = perm-circuit-of p

_ : all perm-ok all-perms ≡ true
_ = refl

-- all-perms really is a list of 24 distinct permutations.
_ : length all-perms ≡ 24
_ = refl

_ : all distinct4 all-perms ≡ true
_ = refl

-- Some entries of Table I, spelled out.
_ : perm-circuit 0 1 2 3 ≡ []
_ = refl
_ : perm-circuit 1 0 2 3 ≡ X₁ ∷ CX ∷ []
_ = refl
_ : perm-circuit 0 2 1 3 ≡ Ex ∷ []
_ = refl
_ : perm-circuit 0 1 3 2 ≡ CX ∷ []
_ = refl
_ : perm-circuit 0 3 2 1 ≡ XC ∷ []
_ = refl
_ : perm-circuit 2 3 0 1 ≡ X₀ ∷ []
_ = refl
_ : perm-circuit 1 0 3 2 ≡ X₁ ∷ []
_ = refl
_ : perm-circuit 3 1 0 2 ≡ Ex ∷ CX ∷ X₀ ∷ []
_ = refl

-- The exchange gate is P₀₂₁₃, the CNOTs are P₀₁₃₂ and P₀₃₂₁.
_ : (⟦ Ex ⟧g == perm-matrix 0 2 1 3) ≡ true
_ = refl
_ : (⟦ CX ⟧g == perm-matrix 0 1 3 2) ≡ true
_ = refl
_ : (⟦ XC ⟧g == perm-matrix 0 3 2 1) ≡ true
_ = refl
_ : (⟦ X₀ ⟧g == perm-matrix 2 3 0 1) ≡ true
_ = refl
_ : (⟦ X₁ ⟧g == perm-matrix 1 0 3 2) ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Diagonal unitaries

-- The generators, as diagonal matrices: Z₀ = diag(1,1,-1,-1) etc.
_ : (⟦ Z₀ ⟧g == diag-matrix 0 0 2 2) ≡ true
_ = refl
_ : (⟦ Z₁ ⟧g == diag-matrix 0 2 0 2) ≡ true
_ = refl
_ : (⟦ S₀ ⟧g == diag-matrix 0 0 1 1) ≡ true
_ = refl
_ : (⟦ S₁ ⟧g == diag-matrix 0 1 0 1) ≡ true
_ = refl
_ : (⟦ CZ ⟧g == diag-matrix 0 0 0 2) ≡ true
_ = refl
_ : (⟦ CS ⟧g == diag-matrix 0 0 0 1) ≡ true
_ = refl
_ : (⟦ Ii ⟧g == diag-matrix 1 1 1 1) ≡ true
_ = refl

diag-samples : List Tuple4
diag-samples =
    (0 , 0 , 0 , 0) ∷ (0 , 0 , 0 , 1) ∷ (0 , 0 , 0 , 2) ∷ (0 , 0 , 0 , 3)
  ∷ (0 , 1 , 2 , 3) ∷ (1 , 1 , 1 , 1) ∷ (3 , 2 , 2 , 0) ∷ (2 , 3 , 3 , 3)
  ∷ (3 , 3 , 3 , 3) ∷ (1 , 2 , 3 , 0) ∷ (2 , 0 , 2 , 0) ∷ (0 , 3 , 1 , 2)
  ∷ []

diag-ok : Tuple4 -> Bool
diag-ok e = (⟦ c ⟧ == diag-matrix-of e) ∧ (rlen c ≤ᵇ 9) ∧ (kc c == 0) ∧ (csc c ≤ᵇ 1)
  where
    c : Circuit
    c = diag-circuit-of e

_ : all diag-ok diag-samples ≡ true
_ = refl

-- The shape of the circuit: Z₀^b₀Z₁^b₁S₀^b₂S₁^b₃CZ^b₄CS^b₅·i^k.
_ : diag-circuit 0 0 0 0 ≡ []
_ = refl
_ : diag-circuit 0 0 0 1 ≡ CS ∷ []
_ = refl
_ : diag-circuit 0 0 0 2 ≡ CZ ∷ []
_ = refl
_ : diag-circuit 0 0 1 1 ≡ S₀ ∷ []
_ = refl
_ : diag-circuit 0 1 0 1 ≡ S₁ ∷ []
_ = refl
_ : diag-circuit 1 1 1 1 ≡ Ii ∷ []
_ = refl
_ : diag-circuit 0 2 2 0 ≡ Z₀ ∷ Z₁ ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- * Generalized permutations

gperm-samples : List (Tuple4 × Tuple4)
gperm-samples =
    ((0 , 1 , 2 , 3) , (0 , 0 , 0 , 0))
  ∷ ((0 , 1 , 2 , 3) , (0 , 0 , 0 , 1))
  ∷ ((0 , 2 , 3 , 1) , (3 , 2 , 2 , 0))   -- a worst case: 9 gates
  ∷ ((1 , 3 , 2 , 0) , (2 , 3 , 3 , 3))
  ∷ ((3 , 2 , 1 , 0) , (1 , 1 , 1 , 1))
  ∷ ((2 , 0 , 3 , 1) , (0 , 1 , 2 , 3))
  ∷ ((1 , 0 , 3 , 2) , (3 , 3 , 3 , 3))
  ∷ ((2 , 3 , 0 , 1) , (2 , 2 , 0 , 0))
  ∷ ((3 , 1 , 2 , 0) , (3 , 1 , 2 , 3))
  ∷ ((1 , 2 , 0 , 3) , (1 , 3 , 0 , 2))
  ∷ []

-- gperm-of finds a circuit that is exactly equal to the input
-- (including the global phase), of length ≤ 9, with ≤ 1 CS gate and
-- no K gate.
gperm-ok : Tuple4 × Tuple4 -> Bool
gperm-ok (p , ph) with gperm-of (gperm-matrix-of p ph)
... | nothing = false
... | just c = (⟦ c ⟧ == gperm-matrix-of p ph) ∧ (rlen c ≤ᵇ 9) ∧ (kc c == 0) ∧ (csc c ≤ᵇ 1)

_ : all gperm-ok gperm-samples ≡ true
_ = refl

-- Generalized permutations are recognised, non-examples are not.
_ : all (λ pph -> is-gperm (gperm-matrix-of (proj₁ pph) (proj₂ pph))) gperm-samples ≡ true
_ = refl

_ : is-gperm ⟦ K₀ ∷ [] ⟧ ≡ false
_ = refl
_ : is-gperm ⟦ CK ∷ [] ⟧ ≡ false
_ = refl
_ : is-gperm (2 scalarmult 1) ≡ false
_ = refl
_ : is-gperm ⟦ CS ∷ Ex ∷ X₀ ∷ Ii ∷ [] ⟧ ≡ true
_ = refl

-- gperm-of on a circuit built from the gate set reproduces it.
circuit-or-empty : Maybe Circuit -> Circuit
circuit-or-empty (just c) = c
circuit-or-empty nothing = []

_ : (⟦ CS ∷ Ex ∷ X₀ ∷ Ii ∷ [] ⟧ == ⟦ circuit-or-empty (gperm-of ⟦ CS ∷ Ex ∷ X₀ ∷ Ii ∷ [] ⟧) ⟧) ≡ true
_ = refl

_ : circuit-or-empty (gperm-of ⟦ CS ∷ Ex ∷ X₀ ∷ Ii ∷ [] ⟧) ≡ CS ∷ Ii ∷ Ex ∷ X₀ ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- * The commutation PD = D′P of Section III C

commute-ok : Tuple4 -> Tuple4 -> Bool
commute-ok p e =
  ((perm-matrix-of p * diag-matrix-of e) == (diag-matrix-of (diag-commute p e) * perm-matrix-of p))
    ∧ (csc (diag-circuit-of (diag-commute p e)) == csc (diag-circuit-of e))

_ : and (map (λ p -> commute-ok p (0 , 1 , 2 , 3)) all-perms) ≡ true
_ = refl
_ : and (map (λ e -> commute-ok (0 , 2 , 3 , 1) e) diag-samples) ≡ true
_ = refl
_ : and (map (λ e -> commute-ok (2 , 3 , 0 , 1) e) diag-samples) ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * All 256 diagonal unitaries

-- The 4⁴ = 256 diagonal unitaries diag(i^a,i^b,i^c,i^d) of Section
-- III B, exhaustively, at type-check time. (The same check for all
-- 24·256 = 6144 generalized permutations also succeeds by refl, but
-- takes about three more minutes of type checking, so it is left to
-- Test.KoptPermutationsRun.)
digits : List ℕ
digits = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

all-phases : List Tuple4
all-phases =
  concatMap (λ a -> concatMap (λ b -> concatMap (λ c ->
    map (λ d -> (a , b , c , d)) digits) digits) digits) digits

_ : length all-phases ≡ 256
_ = refl

_ : all diag-ok all-phases ≡ true
_ = refl
