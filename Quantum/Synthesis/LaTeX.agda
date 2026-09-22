-- This module is an Agda port of the module Quantum.Synthesis.LaTeX of
-- the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It provides some functionality for pretty-printing certain types to
-- LaTeX format. The output is character for character that of the
-- Haskell implementation.
--
-- Differences from the Haskell version:
--
-- * showlatex-p d x returns a String (Haskell: a ShowS function
--   String → String, i.e. showlatex_p d x s = showlatex-p d x ++ s).
--   The class ShowLaTeX has the single field showlatex-p, and showlatex
--   is derived; instances that only define showlatex in Haskell ignore
--   the precedence, as Haskell's default showlatex_p does.
--
-- * Haskell has an instance ShowLaTeX (Matrix n m a) for all a, which
--   is overlapped by the instances for matrices over DOmega and
--   DRComplex (these pull out a common denominator exponent). Agda
--   does not support overlapping instances, so there are instances for
--   matrices over each particular entry type (ℤ, ℚ, Dyadic, Float,
--   SymReal, ZOmega, Z2 [ω], ZRootTwo, DRootTwo, QRootTwo, ZComplex,
--   DComplex, QComplex, CDouble, ZRootTwo [i], QRComplex, TwoLevel,
--   DOmega, DRComplex). For other entry types, use the generic
--   function showlatex-Matrix.
--
-- * The instances for A [√2] and A [i] require DecOrd A instead of
--   Haskell's (Eq a, Num a): the comparisons with 0, 1, -1 in the
--   patterns are done as x ≤ y ∧ y ≤ x (this is IEEE equality for
--   Float, like Haskell's ==; the framework's DecEq Float compares bit
--   patterns), and "signum b == 1" is done as 0 < b (which is the
--   same for all ordered types, including Float with NaN and -0.0).
--
-- * Haskell's printf "%0.10f" on Double (i.e. showFFloat (Just 10)) is
--   implemented exactly: the shortest decimal digits of the double are
--   computed with GHC's floatToDigits algorithm, and rounded to 10
--   decimals with GHC's roundTo (round-half-even on the digit string).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.LaTeX where

open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_ ; _∧_ ; _∨_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Show as NatS
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Show as IntS
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Data.Vec.Base using ([] ; _∷_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.MultiQubitSynthesis
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal

-- ----------------------------------------------------------------------
-- * The ShowLaTeX class

-- A type class for things that can be printed to LaTeX format.
record ShowLaTeX (A : Set) : Set where
  field
    -- Print to LaTeX format, with precedence. Analogous to showsPrec.
    showlatex-p : ℕ -> A -> String

  -- Print to LaTeX format.
  showlatex : A -> String
  showlatex = showlatex-p 0
open ShowLaTeX {{...}} public

-- An instance defined by showlatex only (the precedence is ignored).
showlatex-instance : {A : Set} -> (A -> String) -> ShowLaTeX A
showlatex-instance f .ShowLaTeX.showlatex-p _ x = f x

-- ----------------------------------------------------------------------
-- * Auxiliary: Haskell's printf "%0.10f" for Double

private
  divN modN : ℕ -> ℕ -> ℕ
  divN a zero = 0
  divN a (suc b) = a Nat./ suc b
  modN a zero = a
  modN a (suc b) = a Nat.% suc b

  pow : ℕ -> ℕ -> ℕ
  pow b n = b Nat.^ n

  evenN : ℕ -> Bool
  evenN n = modN n 2 Nat.≡ᵇ 0

  -- Haskell's quot on integers, for a positive divisor.
  quotℤ : ℤ -> ℕ -> ℤ
  quotℤ (+ a) b = + divN a b
  quotℤ a@(-[1+ _ ]) b = - (+ divN Int.∣ a ∣ b)

  -- fixup (GHC's floatToDigits): the least n ≥ k0 such that
  -- r + mUp ≤ 10ⁿ s. The first argument is fuel.
  fixup : ℕ -> ℕ -> ℕ -> ℕ -> ℤ -> ℤ
  fixup zero r s mUp n = n
  fixup (suc fu) r s mUp n@(+ np) =
    if r Nat.+ mUp Nat.≤ᵇ pow 10 np Nat.* s then n else fixup fu r s mUp (n + 1)
  fixup (suc fu) r s mUp n@(-[1+ q ]) =
    if pow 10 (suc q) Nat.* (r Nat.+ mUp) Nat.≤ᵇ s then n else fixup fu r s mUp (n + 1)

  -- gen (GHC's floatToDigits): generate the digits (in reverse). The
  -- first argument is fuel (at most 17 digits are generated for a
  -- double).
  gen : ℕ -> List ℕ -> ℕ -> ℕ -> ℕ -> ℕ -> List ℕ
  gen zero ds rn sN mUpN mDnN = ds
  gen (suc fu) ds rn sN mUpN mDnN =
    if low then (if high then (if rn' Nat.* 2 Nat.<ᵇ sN then dn ∷ ds else suc dn ∷ ds) else dn ∷ ds)
    else if high then suc dn ∷ ds
    else gen fu (dn ∷ ds) rn' sN mUpN' mDnN'
    where
      dn rn' mUpN' mDnN' : ℕ
      dn = divN (rn Nat.* 10) sN
      rn' = modN (rn Nat.* 10) sN
      mUpN' = mUpN Nat.* 10
      mDnN' = mDnN Nat.* 10
      low high : Bool
      low = rn' Nat.<ᵇ mDnN'
      high = sN Nat.<ᵇ rn' Nat.+ mUpN'

  -- GHC's floatToDigits 10 for the positive double m⋅2ᵗ (m odd).
  -- Returns ([d₁,…,dₙ], k) such that the double is 0.d₁…dₙ ⋅ 10ᵏ,
  -- with the shortest digit sequence that uniquely identifies it.
  digits-of : ℕ -> ℤ -> List ℕ × ℤ
  digits-of m t = List.reverse rds , k
    where
      L : ℤ
      L = + hibit m
      -- The exponent, adjusted for denormalized numbers (minExp = -1074).
      e : ℤ
      e = max -1074 (t + L - 53)
      f : ℕ
      f = m Nat.* pow 2 Int.∣ t - e ∣
      rsm : ℕ × ℕ × ℕ × ℕ
      rsm with e
      ... | + ep = if f Nat.≡ᵇ pow 2 52 then (f Nat.* be Nat.* 4 , 4 , be Nat.* 2 , be)
                   else (f Nat.* be Nat.* 2 , 2 , be , be)
        where be = pow 2 ep
      ... | -[1+ q ] = if (-1074 <ᵇ e) ∧ (f Nat.≡ᵇ pow 2 52) then (f Nat.* 4 , pow 2 (suc (suc q)) Nat.* 2 , 2 , 1)
                       else (f Nat.* 2 , pow 2 (suc q) Nat.* 2 , 1 , 1)
      r s mUp mDn : ℕ
      r = proj₁ rsm
      s = proj₁ (proj₂ rsm)
      mUp = proj₁ (proj₂ (proj₂ rsm))
      mDn = proj₂ (proj₂ (proj₂ rsm))
      -- GHC's estimate k0 of k (never too large).
      lx k1 k0 k : ℤ
      lx = t + L - 1
      k1 = quotℤ (lx * 8651) 28738
      k0 = if 0 ≤ᵇ lx then k1 + 1 else k1
      k = fixup 2000 r s mUp k0
      rds : List ℕ
      rds with k
      ... | + kp = gen 40 [] r (s Nat.* pow 10 kp) mUp mDn
      ... | -[1+ q ] = gen 40 [] (r Nat.* bk) s (mUp Nat.* bk) (mDn Nat.* bk)
        where bk = pow 10 (suc q)

  -- floatToDigits 10 x for a finite x > 0.
  float-to-digits : Float -> List ℕ × ℤ
  float-to-digits x with Float.toRatio x
  ... | n , d = if n == 0 then (0 ∷ [] , 0) else digits-of m (+ v - + kd)
    where
      v : ℕ
      v = Int.∣ lobit n ∣
      m : ℕ
      m = Int.∣ shiftR n v ∣
      kd : ℕ
      kd with log2 d
      ... | just k = k
      ... | nothing = 0

  all-zero : List ℕ -> Bool
  all-zero [] = true
  all-zero (x ∷ xs) = (x Nat.≡ᵇ 0) ∧ all-zero xs

  -- GHC's roundTo 10 (round half to even on the digit string).
  roundTo-f : ℕ -> Bool -> List ℕ -> ℕ × List ℕ
  roundTo-f n _ [] = 0 , List.replicate n 0
  roundTo-f zero e (x ∷ xs) =
    if (x Nat.≡ᵇ 5) ∧ e ∧ all-zero xs then (0 , [])
    else ((if 5 Nat.≤ᵇ x then 1 else 0) , [])
  roundTo-f (suc n) _ (i ∷ xs) with roundTo-f n (evenN i) xs
  ... | c , is = if c Nat.+ i Nat.≡ᵇ 10 then (1 , 0 ∷ is) else (0 , c Nat.+ i ∷ is)

  roundTo : ℕ -> List ℕ -> ℕ × List ℕ
  roundTo d is with roundTo-f d true is
  ... | zero , xs = 0 , xs
  ... | suc _ , xs = 1 , 1 ∷ xs

  digit-string : List ℕ -> String
  digit-string ds = String.concat (List.map NatS.show ds)

  -- GHC's formatRealFloatAlt FFFixed (Just dec) False, for (is, e) =
  -- floatToDigits 10 x.
  format-fixed : ℕ -> List ℕ × ℤ -> String
  format-fixed dec (is , + e) with roundTo (dec Nat.+ e) is
  ... | ei , is' = mk0 (digit-string (List.take (e Nat.+ ei) is')) ++ rest (List.drop (e Nat.+ ei) is')
    where
      mk0 : String -> String
      mk0 "" = "0"
      mk0 ls = ls
      rest : List ℕ -> String
      rest [] = ""
      rest rs = "." ++ digit-string rs
  format-fixed dec (is , -[1+ q ]) with roundTo dec (List.replicate (suc q) 0 List.++ is)
  ... | ei , is' with (if 0 Nat.<ᵇ ei then is' else 0 ∷ is')
  ...   | [] = ""
  ...   | d ∷ [] = NatS.show d
  ...   | d ∷ ds' = NatS.show d ++ "." ++ digit-string ds'

-- Haskell's showFFloat (Just dec) x, which is also printf "%0.<dec>f" x.
show-ffloat : ℕ -> Float -> String
show-ffloat dec x =
  if Float.isNaN x then "NaN"
  else if Float.isInfinite x then (if x Float.<ᵇ 0.0 then "-Infinity" else "Infinity")
  else if (x Float.<ᵇ 0.0) ∨ Float.isNegativeZero x then "-" ++ format-fixed dec (float-to-digits (Float.- x))
  else format-fixed dec (float-to-digits x)

-- ----------------------------------------------------------------------
-- * Auxiliary functions

private
  -- Equality via the order (IEEE equality for Float).
  _≃_ : {A : Set} {{_ : DecOrd A}} -> A -> A -> Bool
  x ≃ y = (x ≤ᵇ y) ∧ (y ≤ᵇ x)

-- Generic showlatex-like method that factors out a common denominator
-- exponent.
showlatex-denomexp-p : {A B : Set} {{_ : WholePart A B}} {{_ : ShowLaTeX B}} {{_ : DenomExp A}} -> ℕ -> A -> String
showlatex-denomexp-p {A} {B} d a with denomexp-decompose {A} {B} a
... | b , zero = showlatex-p d b
... | b , suc zero = showParen d 7 ("\\frac{1}{\\sqrt{2}}" ++ showlatex-p 7 b)
... | b , k = showParen d 7 ("\\frac{1}{\\sqrt{2}^{" ++ show k ++ "}}" ++ showlatex-p 7 b)

-- The LaTeX representation of a matrix, given the representation of
-- the entries.
showlatex-Matrix : {m n : ℕ} {A : Set} -> (A -> String) -> Matrix m n A -> String
showlatex-Matrix {A = A} sl (Matrix' a) =
  "\\begin{pmatrix}" ++ String.concat (list-of-vector (vector-map showrow (vector-transpose a))) ++ "\\end{pmatrix}"
  where
    showrow : {k : ℕ} -> Vector k A -> String
    showrow [] = "\\\\"
    showrow (h ∷ []) = sl h ++ "\\\\"
    showrow (h ∷ t@(_ ∷ _)) = sl h ++ " & " ++ showrow t

-- ----------------------------------------------------------------------
-- * Instances

-- Printing of TwoLevel operators (indices are printed 1-based).
showlatex-TwoLevel : TwoLevel -> String
showlatex-TwoLevel (TL-X i j) = "X\\level{" ++ show (suc i) ++ "," ++ show (suc j) ++ "} "
showlatex-TwoLevel (TL-H i j) = "H\\level{" ++ show (suc i) ++ "," ++ show (suc j) ++ "} "
showlatex-TwoLevel (TL-T m i j) =
  if m' Nat.≡ᵇ 0 then ""
  else if m' Nat.≡ᵇ 1 then "T\\level{" ++ show (suc i) ++ "," ++ show (suc j) ++ "} "
  else "T^" ++ show m' ++ "\\level{" ++ show (suc i) ++ "," ++ show (suc j) ++ "} "
  where m' = mod8 m
showlatex-TwoLevel (TL-omega m i) =
  if m' Nat.≡ᵇ 0 then ""
  else if m' Nat.≡ᵇ 1 then "\\omega\\level{" ++ show (suc i) ++ "} "
  else "\\omega^" ++ show m' ++ "\\level{" ++ show (suc i) ++ "} "
  where m' = mod8 m

private
  -- The ZOmega instance.
  tosigned : ℤ -> ℤ × ℤ
  tosigned a = if a <ᵇ 0 then (-1 , - a) else if a == 0 then (0 , 0) else (1 , a)

  -- (sign, text) of a coefficient a with unit u (nothing: the unit 1).
  signedunit : ℤ × Maybe String -> ℤ × String
  signedunit (a , u) with tosigned a
  ... | s , a' with u
  ...   | nothing = s , show a'
  ...   | just u' = s , (if a' == 1 then u' else show a' ++ u')

  cont : List (ℤ × String) -> String
  cont [] = ""
  cont ((s , a) ∷ t) =
    if s == 1 then "+" ++ a ++ cont t
    else if s == 0 then cont t
    else "-" ++ a ++ cont t

  format-signed-list : List (ℤ × String) -> String
  format-signed-list [] = "0"
  format-signed-list ((s , a) ∷ t) = if s == 1 then a ++ cont t else "-" ++ a ++ cont t

showlatex-p-ZOmega : ℕ -> ZOmega -> String
showlatex-p-ZOmega prec (Omega a b c d) = showParen prec 6 (format-signed-list list2)
  where
    list2 : List (ℤ × String)
    list2 = List.filterᵇ (λ p -> proj₁ p /= 0)
      (List.map signedunit ((a , just "\\omega^3") ∷ (b , just "\\omega^2") ∷ (c , just "\\omega") ∷ (d , nothing) ∷ []))

showlatex-ℚ : ℚ -> String
showlatex-ℚ r = "\\frac{" ++ show (Rat.↥ r) ++ "}{" ++ show (Rat.↧ r) ++ "}"

-- Printing of gate lists (the global phase W is collected).
private
  omega-power-latex : ℕ -> String
  omega-power-latex zero = ""
  omega-power-latex (suc zero) = "{\\omega}"
  omega-power-latex n = "\\omega^" ++ show n

  gates-aux : ℕ -> List Gate -> String
  gates-aux n (W ∷ t) = gates-aux (suc n) t
  gates-aux n [] = omega-power-latex n
  gates-aux n (h ∷ t) = omega-power-latex n ++ show h ++ gates-aux 0 t

showlatex-gates : List Gate -> String
showlatex-gates [] = "\\epsilon"
showlatex-gates gs@(_ ∷ _) = gates-aux 0 gs

module _ {A : Set} {{_ : ShowLaTeX A}} {{_ : Ring A}} {{_ : DecOrd A}} where
  open LiteralsFor A

  showlatex-p-RootTwo : ℕ -> A [√2] -> String
  showlatex-p-RootTwo d (RootTwo a b) =
    if b ≃ 0 then showlatex-p d a
    else if a ≃ 0 then irr d b
    else if 0 <ᵇ b then showParen d 6 (showlatex-p 6 a ++ " + " ++ irr 6 b)
    else showParen d 6 (showlatex-p 6 a ++ " - " ++ irr 7 (- b))
    where
      -- showlatex_p d (RootTwo 0 b), b ≠ 0.
      irr : ℕ -> A -> String
      irr d b =
        if b ≃ 1 then "\\sqrt{2}"
        else if b ≃ -1 then showParen d 6 "-\\sqrt{2}"
        else showParen d 7 (showlatex-p 7 b ++ " \\sqrt{2}")

  showlatex-p-Cplx : ℕ -> A [i] -> String
  showlatex-p-Cplx d (Cplx a b) =
    if b ≃ 0 then showlatex-p d a
    else if a ≃ 0 then imag d b
    else if 0 <ᵇ b then showParen d 6 (showlatex-p 6 a ++ "+" ++ imag 7 b)
    else showParen d 6 (showlatex-p 6 a ++ "-" ++ imag 7 (- b))
    where
      -- showlatex_p d (Cplx 0 b), b ≠ 0.
      imag : ℕ -> A -> String
      imag d b =
        if b ≃ 1 then "i"
        else if b ≃ -1 then showParen d 6 "-i"
        else showParen d 7 (showlatex-p 7 b ++ "\\,i")

showlatex-p-SymReal : ℕ -> SymReal -> String
showlatex-p-SymReal d (Const x) = show x
showlatex-p-SymReal d (Decimal x s) = s
showlatex-p-SymReal d (Plus x y) = showParen d 6 (showlatex-p-SymReal 6 x ++ "+" ++ showlatex-p-SymReal 6 y)
showlatex-p-SymReal d (Minus x y) = showParen d 6 (showlatex-p-SymReal 6 x ++ "-" ++ showlatex-p-SymReal 7 y)
showlatex-p-SymReal d (Times x y) = showParen d 7 (showlatex-p-SymReal 7 x ++ "\\cdot" ++ showlatex-p-SymReal 7 y)
showlatex-p-SymReal d (Div x y) = showParen d 7 (showlatex-p-SymReal 7 x ++ "/" ++ showlatex-p-SymReal 8 y)
showlatex-p-SymReal d (Power x y) = showParen d 11 (showlatex-p-SymReal 12 x ++ "^{" ++ showlatex-p-SymReal 0 y ++ "}")
showlatex-p-SymReal d (Negate x) = showParen d 5 ("-" ++ showlatex-p-SymReal 7 x)
showlatex-p-SymReal d (Abs x) = showParen d 10 ("|" ++ showlatex-p-SymReal 11 x ++ "|")
showlatex-p-SymReal d (Signum x) = showParen d 10 ("\\signum " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Recip x) = showParen d 7 ("1/" ++ showlatex-p-SymReal 8 x)
showlatex-p-SymReal d Pi = "\\pi"
showlatex-p-SymReal d Euler = "e"
showlatex-p-SymReal d (Exp x) = showParen d 10 ("e^{" ++ showlatex-p-SymReal 0 x ++ "}")
showlatex-p-SymReal d (Sqrt x) = "\\sqrt{" ++ showlatex-p-SymReal 0 x ++ "}"
showlatex-p-SymReal d (Log x) = showParen d 10 ("\\log " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Sin x) = showParen d 10 ("\\sin " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Tan x) = showParen d 10 ("\\tan " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Cos x) = showParen d 10 ("\\cos " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ASin x) = showParen d 10 ("\\asin " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ATan x) = showParen d 10 ("\\atan " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ACos x) = showParen d 10 ("\\acos " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Sinh x) = showParen d 10 ("\\sinh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Tanh x) = showParen d 10 ("\\tanh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (Cosh x) = showParen d 10 ("\\cosh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ASinh x) = showParen d 10 ("\\asinh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ATanh x) = showParen d 10 ("\\atanh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ACosh x) = showParen d 10 ("\\acosh " ++ showlatex-p-SymReal 11 x)
showlatex-p-SymReal d (ArcTan2 y x) =
  showParen d 10 ("\\arctan2 " ++ showlatex-p-SymReal 11 y ++ " " ++ showlatex-p-SymReal 11 x)

instance
  ShowLaTeXTwoLevel : ShowLaTeX TwoLevel
  ShowLaTeXTwoLevel = showlatex-instance showlatex-TwoLevel

  ShowLaTeXTwoLevels : ShowLaTeX (List TwoLevel)
  ShowLaTeXTwoLevels = showlatex-instance (λ gs -> String.concat (List.map showlatex-TwoLevel gs))

  ShowLaTeXℤ : ShowLaTeX ℤ
  ShowLaTeXℤ = showlatex-instance show

  ShowLaTeXZOmega : ShowLaTeX ZOmega
  ShowLaTeXZOmega .showlatex-p = showlatex-p-ZOmega

  ShowLaTeXℚ : ShowLaTeX ℚ
  ShowLaTeXℚ = showlatex-instance showlatex-ℚ

  ShowLaTeXDyadic : ShowLaTeX Dyadic
  ShowLaTeXDyadic = showlatex-instance (λ x -> showlatex-ℚ (toℚ x))

  ShowLaTeXRootTwo : {A : Set} {{_ : ShowLaTeX A}} {{_ : Ring A}} {{_ : DecOrd A}} -> ShowLaTeX (A [√2])
  ShowLaTeXRootTwo .showlatex-p = showlatex-p-RootTwo

  ShowLaTeXOmegaZ2 : ShowLaTeX (Z2 [ω])
  ShowLaTeXOmegaZ2 = showlatex-instance λ { (Omega a b c d) -> show a ++ show b ++ show c ++ show d }

  ShowLaTeXCplx : {A : Set} {{_ : ShowLaTeX A}} {{_ : Ring A}} {{_ : DecOrd A}} -> ShowLaTeX (A [i])
  ShowLaTeXCplx .showlatex-p = showlatex-p-Cplx

  ShowLaTeXFloat : ShowLaTeX Float
  ShowLaTeXFloat = showlatex-instance (show-ffloat 10)

  ShowLaTeXDOmega : ShowLaTeX DOmega
  ShowLaTeXDOmega .showlatex-p = showlatex-denomexp-p {DOmega} {ZOmega}

  ShowLaTeXGates : ShowLaTeX (List Gate)
  ShowLaTeXGates = showlatex-instance showlatex-gates

  ShowLaTeXSymReal : ShowLaTeX SymReal
  ShowLaTeXSymReal .showlatex-p = showlatex-p-SymReal

-- Matrices (see the comment at the top).
instance
  ShowLaTeXMatrixℤ : {m n : ℕ} -> ShowLaTeX (Matrix m n ℤ)
  ShowLaTeXMatrixℤ = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixℚ : {m n : ℕ} -> ShowLaTeX (Matrix m n ℚ)
  ShowLaTeXMatrixℚ = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixDyadic : {m n : ℕ} -> ShowLaTeX (Matrix m n Dyadic)
  ShowLaTeXMatrixDyadic = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixFloat : {m n : ℕ} -> ShowLaTeX (Matrix m n Float)
  ShowLaTeXMatrixFloat = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixSymReal : {m n : ℕ} -> ShowLaTeX (Matrix m n SymReal)
  ShowLaTeXMatrixSymReal = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixTwoLevel : {m n : ℕ} -> ShowLaTeX (Matrix m n TwoLevel)
  ShowLaTeXMatrixTwoLevel = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixZOmega : {m n : ℕ} -> ShowLaTeX (Matrix m n ZOmega)
  ShowLaTeXMatrixZOmega = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixOmegaZ2 : {m n : ℕ} -> ShowLaTeX (Matrix m n (Z2 [ω]))
  ShowLaTeXMatrixOmegaZ2 = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixZRootTwo : {m n : ℕ} -> ShowLaTeX (Matrix m n ZRootTwo)
  ShowLaTeXMatrixZRootTwo = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixDRootTwo : {m n : ℕ} -> ShowLaTeX (Matrix m n DRootTwo)
  ShowLaTeXMatrixDRootTwo = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixQRootTwo : {m n : ℕ} -> ShowLaTeX (Matrix m n QRootTwo)
  ShowLaTeXMatrixQRootTwo = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixZComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n ZComplex)
  ShowLaTeXMatrixZComplex = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixDComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n DComplex)
  ShowLaTeXMatrixDComplex = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixQComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n QComplex)
  ShowLaTeXMatrixQComplex = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixCDouble : {m n : ℕ} -> ShowLaTeX (Matrix m n CDouble)
  ShowLaTeXMatrixCDouble = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixZRComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n (ZRootTwo [i]))
  ShowLaTeXMatrixZRComplex = showlatex-instance (showlatex-Matrix showlatex)

  ShowLaTeXMatrixQRComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n QRComplex)
  ShowLaTeXMatrixQRComplex = showlatex-instance (showlatex-Matrix showlatex)

  -- These two pull out a common denominator exponent.
  ShowLaTeXMatrixDOmega : {m n : ℕ} -> ShowLaTeX (Matrix m n DOmega)
  ShowLaTeXMatrixDOmega {m} {n} .showlatex-p = showlatex-denomexp-p {Matrix m n DOmega} {Matrix m n ZOmega}

  ShowLaTeXMatrixDRComplex : {m n : ℕ} -> ShowLaTeX (Matrix m n DRComplex)
  ShowLaTeXMatrixDRComplex {m} {n} .showlatex-p = showlatex-denomexp-p {Matrix m n DRComplex} {Matrix m n (ZRootTwo [i])}
