{-# OPTIONS --guardedness #-}
-- Compiled tests for Quantum.Synthesis.EulerAngles and
-- Quantum.Synthesis.RotationDecomposition, over Float (Haskell Double)
-- and FixedPrec 20 (Haskell FixedPrec (PPlus10 P10)). Each output line
-- was compared with the output of the corresponding Haskell expression
-- (newsynth-0.4.1.0, random-1.1); all 18 lines were identical. The
-- Haskell expressions were (with s = sqrt 0.5 :: Double,
-- had = matrix2x2 (Cplx s 0, Cplx s 0) (Cplx s 0, Cplx (-s) 0),
-- m4 = random_unitary (mkStdGen 1) :: Matrix Four Four CDouble,
-- m3 = random_unitary (mkStdGen 7) :: Matrix Three Three CDouble,
-- f2 = random_unitary (mkStdGen 1) :: Matrix Two Two (Cplx (FixedPrec (PPlus10 P10))),
-- f3 = random_unitary (mkStdGen 3) :: Matrix Three Three (Cplx (FixedPrec (PPlus10 P10)))):
--   euler_angles had; matrix_of_euler_angles (0.1,0.2,0.3,0.4 :: Double);
--   euler_angles (matrix_of_euler_angles (0.1,0.2,0.3,0.4 :: Double));
--   euler_angles (from_gates [T,H,S] :: U2 CDouble); m4; rotation_decomposition m4;
--   matrix_of_elementaries (rotation_decomposition m4); m3; rotation_decomposition m3;
--   f2; euler_angles f2; matrix_of_euler_angles (euler_angles f2); f3;
--   rotation_decomposition f3; matrix_of_elementaries (rotation_decomposition f3);
--   and the three lines of Haskell's test with the generator mkStdGen 42.
module Test.RotationDecompositionRun where

open import IO
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base as String using (String ; _++_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.EulerAngles
open import Quantum.Synthesis.RotationDecomposition
open import Quantum.Synthesis.Random
open import Data.Number.FixedPrec
open import Quantum.Synthesis.Ring.FixedPrec
open import Quantum.Synthesis.ArcTan2

-- Haskell's show for 4-tuples.
show4 : {A : Set} {{_ : Show A}} -> A × A × A × A -> String
show4 (a , b , c , d) = "(" ++ show a ++ "," ++ show b ++ "," ++ show c ++ "," ++ show d ++ ")"

showL : {A : Set} {{_ : Show A}} -> List A -> String
showL = showList showsPrec

FP : Set
FP = FixedPrec 20

instance
  ShowCFP : Show (FP [i])
  ShowCFP .showsPrec = showsPrec-Cplx

  ShowMatrixCFP : {m n : ℕ} -> Show (Matrix m n (FP [i]))
  ShowMatrixCFP .showsPrec = showsPrec-Matrix showsPrec

angles0 : Float × Float × Float × Float
angles0 = 0.1 , 0.2 , 0.3 , 0.4

s : Float
s = sqrt 0.5

had : U2 CDouble
had = matrix2x2 (Cplx s 0.0 , Cplx s 0.0) (Cplx s 0.0 , Cplx (Float.- s) 0.0)

m4 : Matrix Four Four CDouble
m4 = random-unitary (mkStdGen 1)

m3 : Matrix Three Three CDouble
m3 = random-unitary (mkStdGen 7)

f2 : Matrix Two Two (FP [i])
f2 = random-unitary (mkStdGen 1)

f3 : Matrix Three Three (FP [i])
f3 = random-unitary (mkStdGen 3)

lines : List String
lines =
  show4 (euler-angles had)
  ∷ show (matrix-of-euler-angles angles0)
  ∷ show4 (euler-angles (matrix-of-euler-angles angles0))
  ∷ show4 (euler-angles (U2 CDouble ∋ from-gates (T ∷ H ∷ S ∷ [])))
  ∷ show m4
  ∷ showL (rotation-decomposition m4)
  ∷ show (Matrix Four Four CDouble ∋ matrix-of-elementaries (rotation-decomposition m4))
  ∷ show m3
  ∷ showL (rotation-decomposition m3)
  ∷ show f2
  ∷ show4 (euler-angles f2)
  ∷ show (matrix-of-euler-angles (euler-angles f2))
  ∷ show f3
  ∷ showL (rotation-decomposition f3)
  ∷ show (Matrix Three Three (FP [i]) ∋ matrix-of-elementaries (rotation-decomposition f3))
  ∷ test (mkStdGen 42)

main : Main
main = run (putStr (String.unlines lines))
