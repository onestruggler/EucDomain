-- The refinement of pattern (ii), at the level of residues.
--
-- Section IV B 1. For an operator of pattern (ii) and lde greater than
-- one, the refinement produces circuits L and R with
--
--   ρ-l-2 of (L A R) = pii2 d
--
-- for some digit d. This module carries the residue half of that: a
-- mirror of the refinement chain that works on a 4x4 matrix over
-- Z[i]/gamma^2 and nothing else, the conditions that unitarity puts on
-- the candidates, and the enumeration.
--
-- Everything here is pure Z[i]/gamma^2 data. The chain of
-- Kopt.Patterns.refine-ii-at multiplies by im-res and by r2-of-circuit,
-- both of which are defined through the dyadic complex numbers; the
-- tables of Kopt.ImRes stand in for them, so that running the chain on a
-- candidate evaluates no dyadic arithmetic at all.
--
-- The conditions are the ones Kopt.Unitary3 proves. (C1) is that the
-- rho-2 inner product of any two columns, and of any two rows, vanishes
-- at positive lde. (C2) is the third rho-3 digit of a norm: by r3-self
-- and r3-ip4-self it is a function of the rho-2 digits alone -- the first
-- two rho-3 digits of an entry are its rho-2 digits -- and it vanishes
-- from lde two on.

{-# OPTIONS --without-K --safe #-}

module Kopt.RefineII where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Properties.Algebra
open import Kopt.Permutations using (Tuple4)
open import Kopt.Patterns
  using (R2 ; r2-zero ; r2-one ; r2-i ; r2-shift ; _r2+_ ; _r2∙_
        ; index-4 ; rows-4 ; im-exp ; pii2)
open import Kopt.ImRes using (imr ; r2-nil ; r2-cx)

-- ----------------------------------------------------------------------
-- * The rho-2 inner product, on residue data

-- rho-2 fixes the adjoint, so no conjugation appears.
r2-ip : Vector 4 R2 -> Vector 4 R2 -> R2
r2-ip (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ []) =
  add₂ (mul₂ x₀ y₀) (add₂ (mul₂ x₁ y₁) (add₂ (mul₂ x₂ y₂) (mul₂ x₃ y₃)))

private
  col : Matrix 4 4 R2 -> ℕ -> Vector 4 R2
  col M j = index-4 M 0 j ∷ index-4 M 1 j ∷ index-4 M 2 j ∷ index-4 M 3 j ∷ []

  row : Matrix 4 4 R2 -> ℕ -> Vector 4 R2
  row M i = index-4 M i 0 ∷ index-4 M i 1 ∷ index-4 M i 2 ∷ index-4 M i 3 ∷ []

  zero? : R2 -> Bool
  zero? v = v == r2-zero

-- ----------------------------------------------------------------------
-- * (C1): the rho-2 inner products vanish

-- All ten pairs on each side, the four norms included: at positive lde
-- every one of them is zero (Kopt.Unitary3.r2-col-norm and friends).
orth2? : Matrix 4 4 R2 -> Bool
orth2? M =
  pairs (col M) ∧ pairs (row M)
  where
    pairs : (ℕ -> Vector 4 R2) -> Bool
    pairs f =
      zero? (r2-ip (f 0) (f 0)) ∧ zero? (r2-ip (f 1) (f 1)) ∧
      zero? (r2-ip (f 2) (f 2)) ∧ zero? (r2-ip (f 3) (f 3)) ∧
      zero? (r2-ip (f 0) (f 1)) ∧ zero? (r2-ip (f 0) (f 2)) ∧
      zero? (r2-ip (f 0) (f 3)) ∧ zero? (r2-ip (f 1) (f 2)) ∧
      zero? (r2-ip (f 1) (f 3)) ∧ zero? (r2-ip (f 2) (f 3))

-- ----------------------------------------------------------------------
-- * (C2): the third rho-3 digit of a norm

-- For an entry with rho-2 digits (a , b), the third rho-3 digit of its
-- norm is b(a+1) (Kopt.Unitary3.r3-self), and add-3 carries, so summing
-- four of them also collects the pairwise products of the leading digits
-- (r3-ip4-self).
private
  hd : R2 -> Z2
  hd (a ∷ b ∷ []) = a

  sd : R2 -> Z2
  sd (a ∷ b ∷ []) = b

  e₂ : Z2 -> Z2 -> Z2 -> Z2 -> Z2
  e₂ p₀ p₁ p₂ p₃ = p₂ * p₃ + (p₁ * (p₂ + p₃) + p₀ * (p₁ + (p₂ + p₃)))

norm3 : Vector 4 R2 -> Z2
norm3 (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) =
  (sd x₀ * (hd x₀ + Odd) + (sd x₁ * (hd x₁ + Odd)
    + (sd x₂ * (hd x₂ + Odd) + sd x₃ * (hd x₃ + Odd))))
  + e₂ (hd x₀) (hd x₁) (hd x₂) (hd x₃)

-- From lde two on, rho-3 of 2^l vanishes, so every norm has third digit
-- Even.
norm3? : Matrix 4 4 R2 -> Bool
norm3? M =
  ev (norm3 (col M 0)) ∧ ev (norm3 (col M 1)) ∧ ev (norm3 (col M 2)) ∧ ev (norm3 (col M 3)) ∧
  ev (norm3 (row M 0)) ∧ ev (norm3 (row M 1)) ∧ ev (norm3 (row M 2)) ∧ ev (norm3 (row M 3))
  where
    ev : Z2 -> Bool
    ev x = x == Even

-- A candidate is admissible if it satisfies both.
adm-ii? : Matrix 4 4 R2 -> Bool
adm-ii? M = orth2? M ∧ norm3? M

-- ----------------------------------------------------------------------
-- * The refinement chain, mirrored
--
-- Step for step Kopt.Patterns.refine-ii-at, with the tables of
-- Kopt.ImRes in place of im-res and r2-of-circuit, and keeping only the
-- residue matrix (the circuits are what the algorithm returns; the normal
-- form is a statement about this).

ref-ii-r2 : Matrix 4 4 R2 -> Matrix 4 4 R2
ref-ii-r2 mres = mres''''
  where
    rc : Tuple4
    rc = if index-4 mres 0 0 r2+ index-4 mres 0 1 == r2-zero
         then (im-exp (index-4 mres 0 0) , im-exp (index-4 mres 0 1) , 0 , 0)
         else (im-exp (index-4 mres 0 0) , im-exp (index-4 mres 0 1) , 0 , 1)

    mres' : Matrix 4 4 R2
    mres' = mres r2∙ imr rc

    lc : Tuple4
    lc = if index-4 mres' 1 0 == r2-one
         then (0 , 0 , 0 , 0)
         else (0 , im-exp (index-4 mres' 1 0) , 0 , 1)

    mres'' : Matrix 4 4 R2
    mres'' = imr lc r2∙ mres'

    l'' : Matrix 4 4 R2
    l'' = if index-4 mres'' 2 0 == r2-shift then r2-nil else r2-cx

    mres''' : Matrix 4 4 R2
    mres''' = l'' r2∙ mres''

    -- The fourth factor. refine-ii-at reads it off mres''' and appends it
    -- to the right-hand circuit, so the residue of the operator the
    -- refinement produces has it too: the right-hand circuit is
    -- lev-rcir ++ im-circuit rc ++ r''. Leaving it out is what made half
    -- of the admissible candidates miss the normal form.
    r'' : Matrix 4 4 R2
    r'' = if index-4 mres''' 0 2 == r2-shift then r2-nil else r2-cx

    mres'''' : Matrix 4 4 R2
    mres'''' = mres''' r2∙ r''

-- The two normal forms it is meant to land in.
ok-ii? : Matrix 4 4 R2 -> Bool
ok-ii? N = (N == pii2 Even) ∨ (N == pii2 Odd)

-- ----------------------------------------------------------------------
-- * The candidates
--
-- The leading digits are those of pattern (ii); the sixteen second digits
-- are free, and it is the conditions above that cut them down.

cand-ii : (b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃
           b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃ : Z2) -> Matrix 4 4 R2
cand-ii b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃ =
  matrix4x4 ((Odd ∷ b₀₀ ∷ []) , (Odd ∷ b₀₁ ∷ []) , (Even ∷ b₀₂ ∷ []) , (Even ∷ b₀₃ ∷ []))
            ((Odd ∷ b₁₀ ∷ []) , (Odd ∷ b₁₁ ∷ []) , (Even ∷ b₁₂ ∷ []) , (Even ∷ b₁₃ ∷ []))
            ((Even ∷ b₂₀ ∷ []) , (Even ∷ b₂₁ ∷ []) , (Even ∷ b₂₂ ∷ []) , (Even ∷ b₂₃ ∷ []))
            ((Even ∷ b₃₀ ∷ []) , (Even ∷ b₃₁ ∷ []) , (Even ∷ b₃₂ ∷ []) , (Even ∷ b₃₃ ∷ []))


-- ----------------------------------------------------------------------
-- * The enumeration
--
-- The sixteen second digits are quantified by a nested fold rather than
-- collected into a list: a list of 65536 matrices over Z[i]/gamma^2 would
-- be built in full before anything was checked, while the fold evaluates
-- one candidate at a time.
--
-- It is split by the four second digits of the first row, so that one
-- block of 4096 can be measured on its own, and so that a block is a
-- statement one can check in isolation.

allZ2 : (Z2 -> Bool) -> Bool
allZ2 f = f Even ∧ f Odd

-- A candidate that satisfies both conditions lands in a normal form.
leaf-ii : (b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃ : Z2) -> Bool
leaf-ii b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃ =
  if adm-ii? M then ok-ii? (ref-ii-r2 M) else true
  where
    M : Matrix 4 4 R2
    M = cand-ii b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃

-- One block: the first row fixed, the remaining twelve digits quantified.
block-ii : (b₀₀ b₀₁ b₀₂ b₀₃ : Z2) -> Bool
block-ii b₀₀ b₀₁ b₀₂ b₀₃ =
  allZ2 (λ b₁₀ ->
    allZ2 (λ b₁₁ ->
      allZ2 (λ b₁₂ ->
        allZ2 (λ b₁₃ ->
          allZ2 (λ b₂₀ ->
            allZ2 (λ b₂₁ ->
              allZ2 (λ b₂₂ ->
                allZ2 (λ b₂₃ ->
                  allZ2 (λ b₃₀ ->
                    allZ2 (λ b₃₁ ->
                      allZ2 (λ b₃₂ ->
                        allZ2 (λ b₃₃ ->
                          leaf-ii b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃))))))))))))

-- All sixteen blocks.
check-ii : Bool
check-ii =
  allZ2 (λ b₀₀ ->
    allZ2 (λ b₀₁ ->
      allZ2 (λ b₀₂ ->
        allZ2 (λ b₀₃ ->
          block-ii b₀₀ b₀₁ b₀₂ b₀₃))))

-- ----------------------------------------------------------------------
-- * Counting
--
-- How many of the 65536 candidates the two conditions admit, and how many
-- of those the refinement does not carry into a normal form. The roadmap
-- that planned this predicted 64 admissible, all of them landing.

sumZ2 : (Z2 -> ℕ) -> ℕ
sumZ2 f = f Even Nat.+ f Odd

count-adm : ℕ
count-adm =
  sumZ2 (λ b₀₀ ->
    sumZ2 (λ b₀₁ ->
      sumZ2 (λ b₀₂ ->
        sumZ2 (λ b₀₃ ->
          sumZ2 (λ b₁₀ ->
            sumZ2 (λ b₁₁ ->
              sumZ2 (λ b₁₂ ->
                sumZ2 (λ b₁₃ ->
                  sumZ2 (λ b₂₀ ->
                    sumZ2 (λ b₂₁ ->
                      sumZ2 (λ b₂₂ ->
                        sumZ2 (λ b₂₃ ->
                          sumZ2 (λ b₃₀ ->
                            sumZ2 (λ b₃₁ ->
                              sumZ2 (λ b₃₂ ->
                                sumZ2 (λ b₃₃ ->
                                  (if adm-ii? (cand-ii b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃) then 1 else 0)))))))))))))))))

-- The two conditions admit exactly 64 of the 65536 candidates. (This is
-- not needed for anything below; it is recorded because it is the number
-- the analysis behind this module predicted, and it is the check that the
-- conditions are the intended ones rather than something weaker.)
how-many-adm : count-adm ≡ 64
how-many-adm = refl

-- ----------------------------------------------------------------------
-- * The normal form of pattern (ii) at lde greater than one
--
-- Every admissible candidate is carried by the refinement into pii2 Even
-- or pii2 Odd. With Kopt.LevelSound and the residue arithmetic this is
-- the residue half of Section IV B 1.
ii-check : check-ii ≡ true
ii-check = refl
