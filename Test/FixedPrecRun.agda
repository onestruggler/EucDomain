{-# OPTIONS --guardedness #-}
-- Compiled test of Data.Number.FixedPrec, ArcTan2, ToReal, SymReal
-- and QuadraticEquation: prints values at 30 to 2000 digits. The
-- output was compared line by line with the Haskell reference
-- (fixedprec-0.2.2.2 / newsynth-0.4.1.0 via ~/nsref/eval.sh) and is
-- identical, except that ℚ is printed as a/b instead of a % b.
module Test.FixedPrecRun where

open import IO
open import Data.List.Base using (List ; [] ; _∷_ ; map)
import Data.List.Base
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁)
open import Quantum.Synthesis.Random using (randomR ; random ; mkStdGen)
open import Data.String.Base using (String ; _++_ ; unwords)
open import Instances
open import Literals
open import Data.Number.FixedPrec
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base using (Float)
open import Quantum.Synthesis.ArcTan2 renaming (ArcTan2 to ArcTan2-class)
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.Ring using (RootTwo ; QRootTwo)
open import Quantum.Synthesis.QuadraticEquation

-- The decimal a/b at precision e (Haskell: a literal a/b).
d : {e : ℕ} -> ℤ -> ℕ -> FixedPrec e
d = fromRat

P : ℕ -> Set
P = FixedPrec

showQ : {e : ℕ} -> Maybe (FixedPrec e × FixedPrec e) -> String
showQ nothing = "Nothing"
showQ (just (a , b)) = "Just (" ++ show a ++ "," ++ show b ++ ")"

lines : List String
lines =
  show (pi {P 100}) ∷
  show (sqrt {P 100} 2) ∷
  show (exp {P 100} 1) ∷
  show (log {P 100} 2) ∷
  show (atan {P 100} 1 * 4) ∷
  show (sin {P 50} 1) ∷
  show (cos {P 50} 1) ∷
  show (sin {P 50} 100) ∷
  show (cos {P 50} (- d 15 2)) ∷
  show (tan {P 50} (d 1 2)) ∷
  show (exp {P 50} 10) ∷
  show (exp {P 50} -10) ∷
  show (log {P 50} 1000) ∷
  show (log {P 50} (d 1 1000)) ∷
  show (asin {P 40} (d 1 2)) ∷
  show (acos {P 40} (d 3 10)) ∷
  show (asin {P 40} (- d 9 10)) ∷
  show (acos {P 40} (- d 99 100)) ∷
  show (sinh {P 40} 1) ∷
  show (cosh {P 40} 2) ∷
  show (tanh {P 40} (d 1 2)) ∷
  show (asinh {P 40} 3) ∷
  show (acosh {P 40} 3) ∷
  show (atanh {P 40} (d 1 2)) ∷
  show (_**_ {P 30} 2 (d 1 2)) ∷
  show (_**_ {P 30} 3 (d 21 2)) ∷
  show (logBase {P 30} 2 1024) ∷
  show (logBase {P 30} 10 2) ∷
  show (_/_ {P 0} 3 7) ∷
  show (_/_ {P 1} 3 7) ∷
  show (_/_ {P 10} 3 7) ∷
  show (_/_ {P 5} -1 3) ∷
  show (d {0} 1 2) ∷
  show (- d {3} 1 2) ∷
  unwords (map (λ x -> show (round x)) (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ [])) ∷
  unwords (map (λ x -> show (floor x)) (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ [])) ∷
  unwords (map (λ x -> show (ceiling x)) (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ [])) ∷
  unwords (map (λ x -> show (truncate x)) (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ [])) ∷
  showQ (solve-quadratic {20} -3 2) ∷
  showQ (solve-quadratic {20} 1 1) ∷
  showQ (solve-quadratic {30} (d 1 3) (- sqrt 2)) ∷
  show (exp {P 30} 100) ∷
  show (log {P 30} (fromℤ (10 ^ 50))) ∷
  show (sin {P 30} 1000) ∷
  show (cos {P 30} -1000) ∷
  show (_**_ {P 30} pi pi) ∷
  show (fractional {3} (- d 11 4)) ∷
  show (cast {10} {5} pi) ∷
  show (toℚ (pi {P 10})) ∷
  show (pi {P 1000}) ∷
  show (sqrt {P 2000} 2) ∷
  []

P50 : Set
P50 = FixedPrec 50

tiny : P50
tiny = fromRat 1 (10 ^ 30)

showQF : Maybe (Float × Float) -> String
showQF nothing = "Nothing"
showQF (just (a , b)) = "Just (" ++ show a ++ "," ++ show b ++ ")"

exprs : List String
exprs = "pi/128" ∷ "2*pi/3" ∷ "(1+sin(pi/3))^2" ∷ "abs(-3)*e" ∷ "sqrt 2 - 1 - 1" ∷ "2**0.5" ∷
  "arctan2 1 (-1)" ∷ "log 10 / log 2" ∷ "tanh 1 + cosh 1 + sinh 1" ∷ "asin 1 + acos 0.5 + atan 3" ∷
  "asinh 2 + atanh 0.5" ∷ "signum (-3) * recip 4" ∷ "tan 1" ∷ "-1.5e-3" ∷ "e^pi - pi" ∷ "exp(-100)" ∷ "0.3" ∷ []

eval50 : String -> String
eval50 s with parse-SymReal s
... | nothing = "Nothing"
... | just x = show (to-real {R = P50} x)

evalF : String -> String
evalF s with parse-SymReal s
... | nothing = "Nothing"
... | just x = show (to-real {R = Float} x)

at2 : P50 × P50 -> String
at2 (y , x) = show (arctan2 y x)

f01 : Float
f01 = 0.1

two : ℤ
two = 2

lines2 : List String
lines2 =
  map at2
    (((1 , 1) ∷ (1 , -1) ∷ (-1 , -1) ∷ (-1 , 1) ∷ (0 , -1) ∷ (0 , 0) ∷ (1 , 0) ∷ (0 , 1) ∷ (-3 , 0) ∷
     (-2 , d 1 2) ∷ (d 1 2 , -2) ∷ (- d 1 2 , -2) ∷ (tiny , -1) ∷ (- tiny , -1) ∷ []))
  Data.List.Base.++
  map eval50 exprs Data.List.Base.++
  map evalF ("pi/128" ∷ "2*pi/3" ∷ "(1+sin(pi/3))^2" ∷ "e^pi - pi" ∷ "arctan2 (-1) (-1)" ∷ []) Data.List.Base.++
  show (to-real {R = FixedPrec 30} f01) ∷
  dynamic-fixedprec 25 (λ x -> show x) (Div Pi (Const 3)) ∷
  dynamic-fixedprec2 12 (λ x y -> show (x * y)) Pi two ∷
  show (log-double (fromℕ {FixedPrec 10} 123456789)) ∷
  showQ (quadratic {QRootTwo} {P 100} (RootTwo 1 0) (RootTwo 0 -3) (RootTwo 1 0)) ∷
  showQ (quadratic {QRootTwo} {P 100} (RootTwo 7 -2) (RootTwo (1 Rat./ 3) 5) (RootTwo -2 1)) ∷
  showQ (quadratic {QRootTwo} {P 1000} (RootTwo 7 -2) (RootTwo (1 Rat./ 3) 5) (RootTwo -2 1)) ∷
  showQF (quadratic {ℚ} 2 -3 1) ∷
  showQF (quadratic {ℚ} 1 3 1) ∷
  showQF (quadratic {ℤ} 1 0 1) ∷
  showQ (quadratic {ℚ} {P 20} 3 -7 (-1 Rat./ 3)) ∷
  show (sin {P 1000} (pi / 7)) ∷
  show (cos {P 1000} (fromRat 12345678 1000)) ∷
  show (exp {P 1000} (- d 1 2)) ∷
  show (atan {P 1000} (d 3 10)) ∷
  show (log {P 1000} 3) ∷
  show (proj₁ (randomR {FixedPrec 10} (-2 , d 7 2) (mkStdGen 1))) ∷
  show (proj₁ (random {FixedPrec 30} (mkStdGen 5))) ∷
  []

main : Main
main = run (IO.List.mapM′ putStrLn (lines Data.List.Base.++ lines2))
