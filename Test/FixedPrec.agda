-- Refl-based tests of Data.Number.FixedPrec, Quantum.Synthesis.ArcTan2,
-- SymReal, Ring.FixedPrec, Ring.SymReal and QuadraticEquation, on tiny
-- precisions only (the type checker evaluates them). The expected
-- values were computed with the Haskell reference implementation
-- (fixedprec-0.2.2.2, newsynth-0.4.1.0). Larger computations are in
-- Test.FixedPrecRun (compiled).

{-# OPTIONS --without-K --safe #-}

module Test.FixedPrec where

open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Data.Bool.Base using (true ; false)
open import Data.Nat.Base using (ℕ)
open import Data.Rational.Base using (ℚ)
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base using (String ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (does)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open import Quantum.Synthesis.ArcTan2 renaming (ArcTan2 to ArcTan2-class)
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.Ring using (RootTwo ; QRootTwo ; dyadic)
open import Quantum.Synthesis.Ring.FixedPrec
open import Quantum.Synthesis.Ring.SymReal
open import Quantum.Synthesis.QuadraticEquation

d : {e : ℕ} -> ℤ -> ℕ -> FixedPrec e
d = fromRat

showQ : {e : ℕ} -> Maybe (FixedPrec e × FixedPrec e) -> String
showQ nothing = "Nothing"
showQ (just (a , b)) = "Just (" ++ show a ++ "," ++ show b ++ ")"

-- ----------------------------------------------------------------------
-- Printing, rounding, arithmetic

_ : show (d {3} 1 3) ≡ "0.333"
_ = refl

_ : show (_/_ {FixedPrec 0} 3 7) ≡ "0.0"
_ = refl

_ : show (d {0} 1 2) ≡ "1.0"
_ = refl

_ : show (- d {3} 1 2) ≡ "-0.500"
_ = refl

_ : show (_/_ {FixedPrec 5} -1 3) ≡ "-0.33333"
_ = refl

_ : show (fromℤ {FixedPrec 2} -3) ≡ "-3.00"
_ = refl

_ : show (d {2} -7 3) ≡ "-2.33"
_ = refl

_ : show (cast {3} {2} (d 2345 1000)) ≡ "2.35"
_ = refl

_ : show (cast {3} {2} (- d 2345 1000)) ≡ "-2.34"
_ = refl

_ : map round (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ []) ≡ 2 ∷ -2 ∷ 4 ∷ 0 ∷ []
_ = refl

_ : map floor (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ []) ≡ 2 ∷ -3 ∷ 3 ∷ -1 ∷ []
_ = refl

_ : map ceiling (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ []) ≡ 3 ∷ -2 ∷ 4 ∷ 0 ∷ []
_ = refl

_ : map truncate (d {3} 5 2 ∷ - d 5 2 ∷ d 7 2 ∷ - d 2 5 ∷ []) ≡ 2 ∷ -2 ∷ 3 ∷ 0 ∷ []
_ = refl

_ : show (fractional {3} (- d 11 4)) ≡ "0.250"
_ = refl

_ : showQ (solve-quadratic {2} -3 2) ≡ "Just (1.00,2.00)"
_ = refl

_ : showQ (solve-quadratic {2} 1 1) ≡ "Nothing"
_ = refl

-- ----------------------------------------------------------------------
-- Analytic functions

_ : show (pi {FixedPrec 5}) ≡ "3.14159"
_ = refl

_ : show (sqrt {FixedPrec 5} 2) ≡ "1.41421"
_ = refl

_ : show (exp {FixedPrec 5} 1) ≡ "2.71828"
_ = refl

_ : show (log {FixedPrec 5} 2) ≡ "0.69315"
_ = refl

_ : show (sin {FixedPrec 5} 1) ≡ "0.84147"
_ = refl

_ : show (atan {FixedPrec 5} 1) ≡ "0.78540"
_ = refl

_ : show (cos {FixedPrec 4} (- d 15 2)) ≡ "0.3466"
_ = refl

_ : show (exp {FixedPrec 4} -3) ≡ "0.0498"
_ = refl

_ : show (exp {FixedPrec 4} 3) ≡ "20.0855"
_ = refl

_ : show (log {FixedPrec 4} 10) ≡ "2.3026"
_ = refl

_ : show (asin {FixedPrec 4} (d 1 2)) ≡ "0.5236"
_ = refl

_ : show (acos {FixedPrec 4} (- d 1 2)) ≡ "2.0944"
_ = refl

_ : show (_**_ {FixedPrec 4} 2 (d 1 2)) ≡ "1.4142"
_ = refl

_ : show (logBase {FixedPrec 4} 2 10) ≡ "3.3219"
_ = refl

_ : show (sinh {FixedPrec 4} 1) ≡ "1.1752"
_ = refl

-- arctan2 in all quadrants and on the axes.
at2 : FixedPrec 5 × FixedPrec 5 -> String
at2 (y , x) = show (arctan2 y x)

_ : map at2
      ((1 , 1) ∷ (1 , -1) ∷ (-1 , -1) ∷ (-1 , 1) ∷ (0 , -1) ∷ (0 , 0) ∷ (1 , 0) ∷
       (-2 , d 1 2) ∷ (d 1 2 , -2) ∷ (- d 1 2 , -2) ∷ [])
    ≡ "0.78540" ∷ "2.35620" ∷ "-2.35620" ∷ "-0.78540" ∷ "3.14159" ∷ "0.00000" ∷ "1.57080" ∷
      "-1.32582" ∷ "2.89661" ∷ "-2.89661" ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- Ring instances

_ : show (fromℤ[√2] {FixedPrec 5} 1 1) ≡ "2.41421"
_ = refl

_ : show (fromℤ[√2] {FixedPrec 5} 1 -1) ≡ "-0.41421"
_ = refl

-- fromDRootTwo (RootTwo (Dyadic 3 2) (Dyadic (-1) 1)) = 3/4 - √2/2
_ : show (fromD[√2] {FixedPrec 5} 3 2 -1 1) ≡ "0.04289"
_ = refl

_ : show (fromℤ/2^ {FixedPrec 2} 1 3) ≡ "0.13"
_ = refl

_ : show (roothalf {FixedPrec 5}) ≡ "0.70711"
_ = refl

_ : show (half {FixedPrec 0}) ≡ "1.0"
_ = refl

_ : show (fromD[√2] {SymReal} 3 2 -1 1) ≡ "3*1/2*1/2+sqrt 2*(-1)*1/2"
_ = refl

_ : show (roothalf {SymReal}) ≡ "sqrt (1/2)"
_ = refl

_ : show (fromℤ[√2] {SymReal} 2 -3) ≡ "2+sqrt 2*(-3)"
_ = refl

_ : map (λ { (a , n) -> show (fromℤ/2^ {SymReal} a n) }) ((5 , 3) ∷ (5 , 0) ∷ (6 , 3) ∷ (5 , 7) ∷ [])
    ≡ "5*1/2*1/2*1/2" ∷ "5*1" ∷ "3*1/2*1/2" ∷ "5*1/2*1/2*1/2*1/2*1/2*1/2*1/2" ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- SymReal parsing and printing

_ : map (λ s -> Maybe.map show (parse-SymReal s))
      ("pi/128" ∷ "2*pi/3" ∷ "-1.5e-3" ∷ "(1+sin(pi/3))^2" ∷ " - 2 ^ 3 ^ 2 " ∷
       "arctan2 1 (-1)" ∷ "1." ∷ ".5" ∷ "abs(-3)*e" ∷ "sqrt 2 - 1 - 1" ∷ "10/3/2" ∷
       "1e5" ∷ "sinh 1 + acosh 2" ∷ "-(pi)" ∷ "+3" ∷ "2**-1" ∷ "exp(1)**2" ∷
       "0.0001" ∷ "007.50" ∷ [])
    ≡ just "pi/128" ∷ just "2*pi/3" ∷ nothing ∷ just "(1+sin (pi/3))**2" ∷ just "-2**(3**2)" ∷
      just "arctan2 1 (-1)" ∷ just "1.0" ∷ just "0.5" ∷ just "abs (-3)*e" ∷ just "sqrt 2-1-1" ∷
      just "10/3/2" ∷ nothing ∷ just "sinh 1+acosh 2" ∷ just "-pi" ∷ just "3" ∷ nothing ∷
      just "exp 1**2" ∷ just "0.0001" ∷ just "007.50" ∷ []
_ = refl

_ : parse-SymReal "2*pi/3" ≡ just (Div (Times (Const 2) Pi) (Const 3))
_ = refl

-- symbolic equality
_ : Maybe.map (λ x -> does (x ≟ 2 * pi / 3)) (parse-SymReal "2*pi/3") ≡ just true
_ = refl

_ : does (Plus Pi (Const 1) ≟ Plus Pi (Const 2)) ≡ false
_ = refl

-- evaluation
_ : Maybe.map (λ x -> show (to-real {R = FixedPrec 4} x)) (parse-SymReal "2*pi/3") ≡ just "2.0944"
_ = refl

-- ----------------------------------------------------------------------
-- Quadratic equations

_ : showQ (quadratic {QRootTwo} {FixedPrec 2} (RootTwo 1 0) (RootTwo 0 -3) (RootTwo 1 0))
    ≡ "Just (0.25,4.00)"
_ = refl

_ : showQ (quadratic {ℚ} {FixedPrec 2} 2 -3 1) ≡ "Just (0.50,1.00)"
_ = refl
