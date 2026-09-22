{-# OPTIONS --guardedness #-}
-- Compiled test of Quantum.Synthesis.GridSynth and
-- Quantum.Synthesis.Newsynth: prints one line per test, to be compared
-- with the Haskell reference (Test/GridSynthRun.expected, produced
-- with ~/nsref/eval.sh from the expressions in the comments).
module Test.GridSynthRun where

open import IO
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base using (String ; _++_)
import Data.String.Base as String

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.Random using (StdGen ; mkStdGen ; readStdGen)
open import Quantum.Synthesis.GridSynth
open import Quantum.Synthesis.Newsynth

g1 : StdGen
g1 = readStdGen "1"

digits : Float -> Float
digits d = d Float.* logBase 2.0 10.0

showM : {A : Set} {{_ : Show A}} -> Maybe A -> String
showM nothing = "Nothing"
showM (just x) = "Just " ++ showsPrec 11 x

showInfo : CandidateInfo -> String
showInfo xs = "[" ++ String.intersperse "," (List.map (λ { (u , t , s) -> "(" ++ show u ++ "," ++ show t ++ "," ++ show s ++ ")" }) xs) ++ "]"

showStats : GridSynthResult -> String
showStats (m , e , info) = "(" ++ show m ++ "," ++ showM e ++ "," ++ showInfo info ++ ")"

showNS : U2 DOmega × Maybe Float × ℤ -> String
showNS (m , e , n) = "(" ++ show m ++ "," ++ showM e ++ "," ++ show n ++ ")"

lines : List String
lines =
  -- concatMap show (gridsynth_gates (read "1" :: StdGen) (10 * logBase 2 10) (pi/128) 25)
  show-gates' (gridsynth-gates g1 (digits 10.0) (Div Pi (Const 128)) 25) ∷
  -- gridsynth_stats (read "1" :: StdGen) (20 * logBase 2 10) (pi/8) 25
  showStats (gridsynth-stats g1 (digits 20.0) (Div Pi (Const 8)) 25) ∷
  -- gridsynth_phase_stats (read "1" :: StdGen) (20 * logBase 2 10) (pi/8) 25
  showStats (gridsynth-phase-stats g1 (digits 20.0) (Div Pi (Const 8)) 25) ∷
  -- gridsynth_stats (mkStdGen 5) 20 (Decimal 0.3 "0.3") 1
  showStats (gridsynth-stats (mkStdGen 5) 20.0 (Decimal (Data.Rational.Base._/_ 3 10) "0.3") 1) ∷
  -- newsynth_stats 30 (pi/16) (mkStdGen 3)
  showNS (newsynth-stats 30.0 (Div Pi (Const 16)) (mkStdGen 3)) ∷
  -- newsynth_gates 30 (pi/16) (mkStdGen 3)
  show-gates (newsynth-gates 30.0 (Div Pi (Const 16)) (mkStdGen 3)) ∷
  -- newsynth 0 0 (mkStdGen 3)
  show (newsynth 0.0 (Const 0) (mkStdGen 3)) ∷
  []
  where
    show-gates' : List Gate -> String
    show-gates' gs = String.concat (List.map show gs)
    import Data.Rational.Base

main : Main
main = run (List.foldr (λ l io -> putStrLn l >> io) (pure _) lines)
