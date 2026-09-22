{-# OPTIONS --guardedness #-}
-- Compiled tests for Quantum.Synthesis.LaTeX. Each output line is
-- compared with the output of the corresponding Haskell expression of
-- newsynth-0.4.1.0 (see the list below; the outputs were identical,
-- character for character).
--
--   putStrLn (showlatex [TL_X 0 1, TL_H 1 2, TL_T 3 0 1, TL_T 8 0 1, TL_T (-1) 2 3, TL_omega 1 0, TL_omega 5 2, TL_omega (-3) 1, TL_T 1 0 2, TL_omega 8 3])
--   putStrLn (unwords (map showlatex [Omega 1 (-2) 0 3, ... :: ZOmega]))
--   ... (one line per line of output, in the same order)
module Test.LaTeXRun where

open import IO
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ ; +_)
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base as Float using (Float)
open import Data.String.Base as String using (String ; _++_ ; unwords)
open import Function.Base using (_∋_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_,_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix hiding (Plus ; Times)
open import Quantum.Synthesis.MultiQubitSynthesis
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.LaTeX

L : {A : Set} {{_ : ShowLaTeX A}} -> List A -> String
L xs = unwords (List.map showlatex xs)

just-matrix : {m n : ℕ} {A : Set} {{_ : Ring A}} -> Maybe (Matrix m n A) -> Matrix m n A
just-matrix (just x) = x
just-matrix nothing = null-matrix

neg : Float -> Float
neg = Float.-_

lines : List String
lines =
  showlatex (TL-X 0 1 ∷ TL-H 1 2 ∷ TL-T 3 0 1 ∷ TL-T 8 0 1 ∷ TL-T -1 2 3 ∷ TL-omega 1 0 ∷ TL-omega 5 2 ∷ TL-omega -3 1 ∷ TL-T 1 0 2 ∷ TL-omega 8 3 ∷ [])
  ∷ L (List ZOmega ∋ Omega 1 -2 0 3 ∷ Omega 0 0 0 0 ∷ Omega -1 1 -1 1 ∷ Omega 0 0 0 -5 ∷ Omega 2 0 0 0 ∷ Omega 0 0 1 0 ∷ Omega 0 -1 0 1 ∷ [])
  ∷ L (List ℚ ∋ (+ 3 Rat./ 4) ∷ -3 ∷ 0 ∷ 7 ∷ [])
  ∷ L (dyadic 3 2 ∷ dyadic -5 0 ∷ dyadic 6 3 ∷ [])
  ∷ L (List ZRootTwo ∋ RootTwo 1 2 ∷ RootTwo 1 -1 ∷ RootTwo 0 -1 ∷ RootTwo 0 3 ∷ RootTwo -2 -3 ∷ RootTwo 0 1 ∷ RootTwo 5 0 ∷ RootTwo 0 -4 ∷ RootTwo -1 1 ∷ [])
  ∷ L (List DRootTwo ∋ roothalf ∷ 1 + roothalf ∷ roottwo - 3 * roothalf ∷ [])
  ∷ L (List ZComplex ∋ Cplx 1 2 ∷ Cplx 0 -1 ∷ Cplx 3 -1 ∷ Cplx 0 2 ∷ Cplx -1 -4 ∷ Cplx 0 1 ∷ Cplx 0 -3 ∷ Cplx -2 1 ∷ [])
  ∷ L (List (ZRootTwo [i]) ∋ Cplx (RootTwo 1 1) (RootTwo 0 -1) ∷ Cplx 0 (RootTwo 2 1) ∷ Cplx (RootTwo 0 2) (RootTwo -1 1) ∷ Cplx 1 (RootTwo 0 -3) ∷ [])
  ∷ L (List DOmega ∋ omega ∷ roothalf ∷ roothalf * omega ∷ 1 + roothalf ∷ omega ^ 3 * roothalf ^ 3 ∷ 0 ∷ -1 ∷ [])
  ∷ (showlatex-p 7 (DOmega ∋ roothalf) ++ " " ++ showlatex-p 7 (ZOmega ∋ Omega 1 0 0 1))
  ∷ L (List (Z2 [ω]) ∋ Omega 1 0 1 1 ∷ Omega 0 0 0 0 ∷ [])
  ∷ L (List Float ∋ 1.0 Float.÷ 3.0 ∷ neg 2.5 ∷ 0.0 ∷ 1.0e-12 ∷ 123456.789 ∷ 0.125 ∷ 1.0e22 ∷ neg 0.0 ∷ 5.0e-324 ∷ 2.0 Float.÷ 3.0 ∷ π
         ∷ 0.99999999995 ∷ 0.00000000005 ∷ 0.00000000015 ∷ 1.5e-11 ∷ 2.5 ∷ 1.0e300 ∷ 1.7976931348623157e308 ∷ 2.2250738585072014e-308
         ∷ 0.1 ∷ 1234.56789012345678 ∷ sqrt 2.0 ∷ exp 1.0 ∷ neg 1.0e-11 ∷ [])
  ∷ L (List Float ∋ sin 1.0 ∷ cos 1.0 ∷ tan 1.0 ∷ 1.0 Float.÷ 7.0 ∷ 22.0 Float.÷ 7.0 ∷ 1.0e15 Float.÷ 3.0 ∷ 3.0e-5 Float.÷ 7.0
         ∷ 1.0 Float.÷ 0.0 ∷ neg 1.0 Float.÷ 0.0 ∷ [])
  ∷ showlatex (U2 DOmega ∋ from-gates (H ∷ []))
  ∷ showlatex (U2 DOmega ∋ from-gates (H ∷ T ∷ S ∷ H ∷ []))
  ∷ showlatex (U2 DRComplex ∋ from-gates (T ∷ H ∷ []))
  ∷ showlatex (U2 DRComplex ∋ from-gates (H ∷ T ∷ []))
  ∷ showlatex (U2 DOmega ∋ from-gates (S ∷ []))
  ∷ showlatex (Matrix Two Two ℤ ∋ matrix2x2 (1 , 2) (-3 , 4))
  ∷ showlatex (U2 CDouble ∋ matrix2x2 (Cplx 0.5 0.5 , 0) (0 , Cplx 1.0 (neg 1.0)))
  ∷ showlatex (U2 CDouble ∋ from-gates (H ∷ T ∷ []))
  ∷ showlatex (just-matrix {Two} {Three} {ℤ} (matrix ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [])))
  ∷ L ((H ∷ T ∷ W ∷ W ∷ S ∷ W ∷ []) ∷ (W ∷ []) ∷ [] ∷ (W ∷ W ∷ W ∷ H ∷ []) ∷ (H ∷ W ∷ []) ∷ (W ∷ H ∷ W ∷ T ∷ []) ∷ [])
  ∷ L (Plus (Const 1) (Times Pi (Negate (Const 2))) ∷ Div (Const 1) (Minus (Const 3) (Plus Pi Euler))
       ∷ Power (Sqrt (Const 2)) (Div Pi (Const 4)) ∷ Negate (Negate (Const -3)) ∷ Abs (Sin (Plus Pi Pi))
       ∷ ArcTan2 (Const 1) (Negate (Const 2)) ∷ Exp (Log (Const 2)) ∷ Recip (Recip (Const 5)) ∷ Signum (Cos (Const 0))
       ∷ Times (Plus (Const 1) (Const 2)) (Minus (Const 3) (Minus (Const 4) (Const 5))) ∷ [])
  ∷ L (Decimal (+ 1 Rat./ 2) "0.5" ∷ Tan (ASin (ACos (ATan (Const 1)))) ∷ Sinh (Tanh (Cosh (ASinh (ATanh (ACosh (Const 2))))))
       ∷ Power (Power (Const 2) (Const 3)) (Const 4) ∷ Times (Div (Const 1) (Const 2)) (Recip (Const 3)) ∷ [])
  ∷ []

main : Main
main = run (putStr (String.unlines lines))
