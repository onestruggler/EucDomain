-- Small refl-based tests of Quantum.Synthesis.GridProblems. The
-- expected values were computed with the Haskell reference
-- implementation (newsynth-0.4.1.0, ~/nsref/eval.sh).

{-# OPTIONS --without-K --safe --guardedness #-}

module Test.GridProblems where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁)
import Data.Maybe.Base
open import Data.Float.Base using (Float)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.GridProblems

-- Haskell: gridpoints (0 :: Double, 5) (-1, 1)
test-gridpoints-Float : showList showsPrec (gridpoints {Float} (0.0 , 5.0) (-1.0 , 1.0))
  ≡ "[0,1,1 + roottwo,2 + roottwo,2 + 2*roottwo]"
test-gridpoints-Float = refl

-- The same, with exact arithmetic in ℚ[√2].
test-gridpoints-QRootTwo : gridpoints {QRootTwo} (0 , 5) (-1 , 1)
  ≡ 0 ∷ 1 ∷ 1 + roottwo ∷ 2 + roottwo ∷ 2 + 2 * roottwo ∷ []
test-gridpoints-QRootTwo = refl

-- Haskell: gridpoints_scaled (0 :: QRootTwo, 1) (-1, 1) 4 (exact; at
-- FixedPrec the boundary point 1 is lost to rounding).
test-gridpoints-scaled : showList showsPrec (gridpoints-scaled {QRootTwo} (0 , 1) (-1 , 1) 4)
  ≡ "[0,-1/4 + 1/4*roottwo,1/2 - 1/4*roottwo,1/4,1/4*roottwo,-1/4 + 1/2*roottwo,1/2,1/4 + 1/4*roottwo,1/2*roottwo,3/4,1/2 + 1/4*roottwo,1/4 + 1/2*roottwo,1]"
test-gridpoints-scaled = refl

-- Haskell: floorlog (1 + roottwo :: QRootTwo) 100 == (5, ...), and
-- lambdapower (-3) :: ZRootTwo == -7 + 5*roottwo.
test-floorlog : proj₁ (floorlog {QRootTwo} lambda 100) ≡ 5
test-floorlog = refl

test-lambdapower : lambdapower {ZRootTwo} -3 ≡ -7 + 5 * roottwo
test-lambdapower = refl

-- Grid operators: S² = matrix [[3 + 2√2, 0], [0, 3 - 2√2]], and
-- the special inverse of K is K⁻¹.
test-opS : show (opS-power {DRootTwo} 2) ≡ "matrix [[3 + 2*roottwo,0],[0,3 - 2*roottwo]]"
test-opS = refl

test-special-inverse : special-inverse (opK {DRootTwo}) * opK ≡ 1
test-special-inverse = refl

-- Haskell: to_upright (operator_from_bz (3 :: FixedPrec P100) 1.5,
-- operator_from_bz (-2) (-0.7)) == matrix [[1 + roottwo,0],[0,1 - roottwo]]
-- (checked in Test.GridProblemsRun); here the Step Lemma at Float:
test-step-lemma : Data.Maybe.Base.map show (step-lemma {Float} (operator-from-bz 30.0 0.1 , operator-from-bz 20.0 0.2))
  ≡ just "roothalf * matrix [[1,-1],[1,1]]"
test-step-lemma = refl
