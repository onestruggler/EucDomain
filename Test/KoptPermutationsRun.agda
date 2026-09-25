-- Compiled (executed) exhaustive checks of Kopt.Permutations. These
-- are the checks that are too big to run in the type checker:
--
--  * all 24 permutation circuits of Table I,
--  * all 256 diagonal unitaries diag(i^a,i^b,i^c,i^d),
--  * all 24·256 = 6144 generalized permutations, and
--  * the commutation PD = D′P for all 6144 pairs (P,D).
--
-- Run with scratchpad/agda-run.sh Test/KoptPermutationsRun.agda; each
-- line prints "PASS n/n" or "FAIL k/n".

{-# OPTIONS --guardedness #-}

module Test.KoptPermutationsRun where

open import IO
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_ ; length)
open import Data.Bool.ListAction using (and)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base using (String)
import Data.String.Base as Str

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations

-- ----------------------------------------------------------------------
-- * Test harness

count-true : List Bool -> ℕ
count-true [] = zero
count-true (true ∷ bs) = suc (count-true bs)
count-true (false ∷ bs) = count-true bs

report : String -> List Bool -> String
report name bs =
  (if and bs then "PASS " else "FAIL ")
    Str.++ show (count-true bs) Str.++ "/" Str.++ show (length bs)
    Str.++ "  " Str.++ name

-- ----------------------------------------------------------------------
-- * Enumerations

digits : List ℕ
digits = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

all-phases : List Tuple4
all-phases =
  List.concatMap (λ a ->
    List.concatMap (λ b ->
      List.concatMap (λ c ->
        List.map (λ d -> (a , b , c , d)) digits) digits) digits) digits

all-gperms : List (Tuple4 × Tuple4)
all-gperms = List.concatMap (λ p -> List.map (λ ph -> (p , ph)) all-phases) all-perms

-- ----------------------------------------------------------------------
-- * The checks

-- Table I: ⟦perm-circuit p⟧ = perm-matrix p, with ≤ 3 gates and no
-- K and no CS gate.
perm-ok : Tuple4 -> Bool
perm-ok p = (⟦ c ⟧ == perm-matrix-of p) ∧ (rlen c ≤ᵇ 3) ∧ (kc c == 0) ∧ (csc c == 0)
  where
    c : Circuit
    c = perm-circuit-of p

-- Section III B: ⟦diag-circuit a b c d⟧ = diag(i^a,i^b,i^c,i^d), with
-- ≤ 6 gates besides the scalar ones, ≤ 1 CS gate and no K gate.
diag-ok : Tuple4 -> Bool
diag-ok e = (⟦ c ⟧ == diag-matrix-of e) ∧ (rlen c ≤ᵇ 9) ∧ (kc c == 0) ∧ (csc c ≤ᵇ 1)
  where
    c : Circuit
    c = diag-circuit-of e

-- Section III C: gperm-of produces an exact circuit of ≤ 9 gates with
-- ≤ 1 CS gate and no K gate.
gperm-ok : Tuple4 × Tuple4 -> Bool
gperm-ok (p , ph) with gperm-of (gperm-matrix-of p ph)
... | nothing = false
... | just c = (⟦ c ⟧ == gperm-matrix-of p ph) ∧ (rlen c ≤ᵇ 9) ∧ (kc c == 0) ∧ (csc c ≤ᵇ 1)

-- Section III C: PD = D′P with D′ = diag-commute P D, and D′ has the
-- same CS-count as D.
commute-ok : Tuple4 × Tuple4 -> Bool
commute-ok (p , e) =
  ((perm-matrix-of p * diag-matrix-of e) == (diag-matrix-of (diag-commute p e) * perm-matrix-of p))
    ∧ (csc (diag-circuit-of (diag-commute p e)) == csc (diag-circuit-of e))

-- The generalized permutations all have lde 0.
lde0-ok : Tuple4 × Tuple4 -> Bool
lde0-ok (p , ph) = lde (gperm-matrix-of p ph) == 0

gperm-ok2 : Tuple4 × Tuple4 -> Bool
gperm-ok2 (p , ph) = is-gperm (gperm-matrix-of p ph)

-- Non-examples: matrices that are not generalized permutations.
non-gperms : List (Matrix 4 4 DComplex)
non-gperms =
    ⟦ K₀ ∷ [] ⟧
  ∷ ⟦ K₁ ∷ CS ∷ K₁ ∷ [] ⟧
  ∷ ⟦ CK ∷ [] ⟧
  ∷ (2 scalarmult 1)
  ∷ 0
  ∷ matrix4x4 (1 , 1 , 0 , 0) (0 , 0 , 0 , 0) (0 , 0 , 1 , 0) (0 , 0 , 0 , 1)
  ∷ matrix4x4 (1 , 0 , 0 , 0) (0 , 1 , 0 , 0) (0 , 0 , 1 , 0) (0 , 0 , 0 , 0)
  ∷ []

main : Main
main = run do
  putStrLn (report "24 permutation circuits (Table I)" (List.map perm-ok all-perms))
  putStrLn (report "256 diagonal unitaries" (List.map diag-ok all-phases))
  putStrLn (report "6144 generalized permutations (gperm-of)" (List.map gperm-ok all-gperms))
  putStrLn (report "6144 generalized permutations have lde 0" (List.map lde0-ok all-gperms))
  putStrLn (report "6144 commutations PD = D'P" (List.map commute-ok all-gperms))
  putStrLn (report "is-gperm on generalized permutations" (List.map gperm-ok2 all-gperms))
  putStrLn (report "is-gperm rejects non-examples" (List.map (λ m -> not (is-gperm m)) non-gperms))
