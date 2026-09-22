{-# OPTIONS --guardedness #-}
-- Compiled test of Quantum.Synthesis.GridProblems: prints one line per
-- test, to be compared textually with the Haskell reference (the same
-- expressions evaluated with ~/nsref/eval.sh). All 47 lines are
-- identical to the Haskell output (Haskell prints the three ConvexSet
-- lines as quoted strings since they were evaluated with show).
module Test.GridProblemsRun where

open import IO
open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Float.Base using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base using (String ; _++_)
import Data.String.Base
open import Codata.Guarded.Stream using (Stream)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.FixedPrec
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.QuadraticEquation
open import Quantum.Synthesis.Random using (mkStdGen)
open import Quantum.Synthesis.GridProblems

P : ℕ -> Set
P = FixedPrec

-- The decimal a/b at precision e (Haskell: a literal).
d : {e : ℕ} -> ℤ -> ℕ -> FixedPrec e
d = fromRat

showL : {A : Set} {{_ : Show A}} -> List A -> String
showL = showList showsPrec

showM : {A : Set} {{_ : Show A}} -> Maybe A -> String
showM nothing = "Nothing"
showM (just x) = "Just " ++ showsPrec 11 x

showP : {A B : Set} {{_ : Show A}} {{_ : Show B}} -> A × B -> String
showP (a , b) = "(" ++ show a ++ "," ++ show b ++ ")"

-- The ε-region of GridSynth.hs (epsilon_region), needed to test
-- gridpoints2-increasing as gridsynth uses it.
module _ {e : ℕ} where
  private
    R = FixedPrec e

  -- The constants zx, zy, d are passed as arguments to mk, so that
  -- they are computed only once (where-bound values are not shared in
  -- compiled Agda code).
  epsilon-region : R -> R -> ConvexSet R
  epsilon-region epsilon theta = mk (cos (- (theta / 2))) (sin (- (theta / 2))) (1 - epsilon ^ 2 / 2)
    where
      ev1 ev2 : R
      ev1 = 4 * (1 / epsilon) ^ 4
      ev2 = (1 / epsilon) ^ 2
      mk : R -> R -> R -> ConvexSet R
      mk zx zy dd = ConvexSet' (Ellipse' mat (dd * zx , dd * zy)) tst int
        where
          bmat : Operator R
          bmat = toOperator ((zx , - zy) , (zy , zx))
          mat : Operator R
          mat = bmat * toOperator ((ev1 , 0) , (0 , ev2)) * special-inverse bmat
          tst : CharFun
          tst (x , y) = (x ^ 2 + y ^ 2 ≤ᵇ 1) ∧ (dd ≤ᵇ zx * fromDRootTwo x + zy * fromDRootTwo y)
          int : LineIntersector R
          int p v = go (quadratic (fromDRootTwo {QRootTwo} a) (fromDRootTwo b) (fromDRootTwo c))
                       (iprod (point-fromDRootTwo v) (zx , zy)) (dd - iprod (point-fromDRootTwo p) (zx , zy))
            where
              a b c : DRootTwo
              a = iprod v v
              b = 2 * iprod v p
              c = iprod p p - 1
              go : Maybe (R × R) -> R -> R -> Maybe (R × R)
              go nothing vz rhs = nothing
              go (just (t0 , t1)) vz rhs =
                if (vz == 0) ∧ (rhs ≤ᵇ 0) then just (t0 , t1)
                else if vz == 0 then nothing
                else if 0 <ᵇ vz then just (max t0 (rhs / vz) , t1)
                else just (t0 , min t1 (rhs / vz))

bracket : List String -> String
bracket xs = "[" ++ Data.String.Base.intersperse "," xs ++ "]"

showKL : ℕ × List DOmega -> String
showKL (k , us) = "(" ++ show k ++ "," ++ showL us ++ ")"

showKN : ℕ × List DOmega -> String
showKN (k , us) = "(" ++ show k ++ "," ++ show (List.length us) ++ ")"

firstNonEmpty : ℕ -> Stream (ℕ × List DOmega) -> String
firstNonEmpty n s = go (stream-take n s)
  where
    go : List (ℕ × List DOmega) -> String
    go [] = "none"
    go ((k , []) ∷ rest) = go rest
    go (kl ∷ rest) = showKL kl

module _ where
  reg1 reg2 : ConvexSet (P 100)
  reg1 = epsilon-region (d 1 100) (pi / 128)
  reg2 = epsilon-region (d 1 10000000000) (pi / 128)

  st1 st2 : Stream (ℕ × List DOmega)
  st1 = gridpoints2-increasing reg1 unitdisk
  st2 = gridpoints2-increasing reg2 unitdisk

lines : List String
lines =
  -- the 1-dimensional grid problems
  showL (gridpoints {Float} (0.0 , 5.0) (-1.0 , 1.0)) ∷
  showL (gridpoints {P 100} (0 , 20) (-3 , 3)) ∷
  showL (gridpoints {P 10} (- d 15 10 , d 10025 100) (- d 1 1000 , d 2 1000)) ∷
  showL (gridpoints {P 10} (- d 1 100 , d 2 100) (-300 , 250)) ∷
  showL (gridpoints {P 10} (d 10005 10 , 1010) (-2 , 2)) ∷
  showL (gridpoints {Float} (-7.0 , -1.0) (3.0 , 4.5)) ∷
  showL (gridpoints-parity {P 100} 1 (0 , 20) (-3 , 3)) ∷
  showL (gridpoints-parity {P 100} 0 (0 , 20) (-3 , 3)) ∷
  showL (gridpoints-scaled {P 100} (0 , 1) (-1 , 1) 4) ∷
  showL (gridpoints-scaled {P 100} (- d 5 10 , d 3 10) (- d 2 10 , d 7 10) 5) ∷
  showL (gridpoints-scaled-parity {P 100} (roothalf ^ 3) (0 , 1) (-1 , 1) 3) ∷
  showL (gridpoints-scaled-parity {P 100} (roothalf ^ 3) (0 , 1) (-1 , 1) 5) ∷
  showM (gridpoint-random {Float} (0.0 , 10.0) (0.0 , 10.0) (mkStdGen 5)) ∷
  showM (gridpoint-random {P 10} (0 , 100) (-2 , 3) (mkStdGen 17)) ∷
  showM (gridpoint-random-parity {P 10} 1 (0 , 100) (-2 , 3) (mkStdGen 17)) ∷
  showM (gridpoint-random {P 10} (0 , d 1 10) (0 , d 1 10) (mkStdGen 17)) ∷
  show (logBase-double {P 100} (1 + roottwo) (d 12345678 1000)) ∷
  show (logBase-double {P 100} (d 3 10) (d 12345678 1000)) ∷
  showP (floorlog {P 100} (1 + roottwo) (d 123 1000000)) ∷
  -- the 2-dimensional grid problems
  showL (gridpoints2 {P 100} unitdisk unitdisk) ∷
  showL (gridpoints2-scaled {P 100} (disk 2) (disk 3) 2) ∷
  showL (gridpoints2-scaled {P 100} unitdisk unitdisk 3) ∷
  showL (gridpoints2 {P 100} (rectangle (0 , 1) (0 , 2)) (rectangle (-1 , 1) (-1 , 1))) ∷
  showL (gridpoints2 {Float} (rectangle (0.0 , 1.0) (0.0 , 2.0)) (rectangle (-1.0 , 1.0) (-1.0 , 1.0))) ∷
  showL (gridpoints2-scaled {P 100} (rectangle (d 1 10 , d 3 10) (- d 5 100 , d 2 100)) (rectangle (-2 , 1) (-1 , 3)) 5) ∷
  show (unitdisk {P 10}) ∷
  show (disk {P 10} (RootTwo 2 1)) ∷
  show (rectangle {P 10} (0 , 1) (0 , 3)) ∷
  show (to-upright {P 100} (operator-from-bz 3 (d 15 10) , operator-from-bz -2 (- d 7 10))) ∷
  show (to-upright {P 100} (toOperator ((100 , d 9999 100) , (d 9999 100 , d 1000001 10000)) , toOperator ((1 , 0) , (0 , 1)))) ∷
  show (to-upright {P 100} (toOperator ((1 , d 99999 100000) , (d 99999 100000 , 1)) , toOperator ((1000 , 0) , (0 , d 1 1000)))) ∷
  show (to-upright {Float} (toOperator ((1.0 , 0.99999) , (0.99999 , 1.0)) , toOperator ((1000.0 , 0.0) , (0.0 , 0.001)))) ∷
  showP (operator-to-bz {P 100} (operator-from-bz 3 (d 15 10))) ∷
  show (uprightness {P 100} (operator-from-bz 3 (d 15 10))) ∷
  show (bias {P 100} (operator-from-bz 3 (d 15 10) , operator-from-bz -2 (- d 7 10))) ∷
  show (lemma-A {P 100} (d 13 10) (d 21 10)) ∷
  show (lemma-B {P 100} (d 13 10) (d 21 10)) ∷
  show (lemma-A-l2 {P 100} (d 1303 10) (d 721 10)) ∷
  show (lemma-B-l2 {P 100} (d 1303 10) (d 721 10)) ∷
  showM (step-lemma {P 100} (operator-from-bz 3 (d 15 10) , operator-from-bz -2 (- d 7 10))) ∷
  showM (step-lemma {P 100} (operator-from-bz 30 (d 1 10) , operator-from-bz 20 (d 2 10))) ∷
  showM (step-lemma {P 100} (operator-from-bz 30 (d 31 10) , operator-from-bz 20 (d 2 10))) ∷
  -- gridpoints2-increasing on ε-regions, as in gridsynth
  show (to-upright-sets reg1 unitdisk) ∷
  bracket (List.map showKL (stream-take 16 st1)) ∷
  show (to-upright-sets reg2 unitdisk) ∷
  firstNonEmpty 200 st2 ∷
  bracket (List.map showKN (stream-take 56 st2)) ∷
  []

main : Main
main = run (List.foldr (λ l io -> putStrLn l >> io) (pure _) lines)
