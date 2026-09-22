{-# OPTIONS --guardedness #-}
-- Compiled tests for Quantum.Synthesis.Diophantine (and StepComp,
-- EuclideanDomain): the results are printed in Haskell's format and
-- compared with the output of the Haskell newsynth reference
-- implementation (with the same random generator), and the solutions
-- of t†t = ξ are checked.
module Test.DiophantineRun where

open import IO using (Main ; run ; putStrLn ; _>>_ ; _>>=_)
import IO.Handle
open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_ ; map ; foldr ; and ; zipWith ; length)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Show as NatS
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_ ; intersperse)
import Data.String.Properties as StrP
open import Function.Base using (_∘_ ; _$_)

open import Instances hiding (show)
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.EuclideanDomain
open import Quantum.Synthesis.StepComp using (StepComp ; run-with-steps ; run-bounded ; with-counter ; subtask)
import Quantum.Synthesis.StepComp as SC
open import Quantum.Synthesis.Random
open import Quantum.Synthesis.Diophantine

-- ----------------------------------------------------------------------
-- Printing in Haskell's format

show : {A : Set} {{_ : Show A}} -> A -> String
show = showsPrec 0

hs-maybe : {A : Set} -> (A -> String) -> Maybe A -> String
hs-maybe s nothing = "Nothing"
hs-maybe s (just a) = "Just " ++ s a

hs-pair : String -> String -> String
hs-pair a b = "(" ++ a ++ "," ++ b ++ ")"

hs-list : List String -> String
hs-list xs = "[" ++ intersperse "," xs ++ "]"

-- A computation run to completion, with its number of steps, as
-- Haskell's run_with_steps (prints TIMEOUT if it does not finish).
steps : {A : Set} -> (A -> String) -> StepComp A -> String
steps s c with run-with-steps c
... | just (a , n) = hs-pair (s a) (NatS.show n)
... | nothing = "TIMEOUT"

-- run_bounded 100000 (with_counter c)
bounded : {A : Set} -> (A -> String) -> StepComp A -> String
bounded s c = hs-maybe (λ (a , n) -> hs-pair (s a) (NatS.show n)) (run-bounded 100000 (with-counter c))

prec11 : {A : Set} {{_ : Show A}} -> A -> String
prec11 = showsPrec 11

-- Haskell's Show instance for Maybe (not in the framework yet).
instance
  ShowMaybe : {A : Set} {{_ : Show A}} -> Show (Maybe A)
  ShowMaybe .showsPrec d nothing = "Nothing"
  ShowMaybe .showsPrec d (just a) = showParen d 10 ("Just " ++ showsPrec 11 a)

-- ----------------------------------------------------------------------
-- Test data

g : StdGen
g = mkStdGen 1

xs : List ZRootTwo
xs = RootTwo 13 0 ∷ RootTwo 2 1 ∷ RootTwo 3 1 ∷ RootTwo 5 0 ∷ RootTwo 7 0 ∷ RootTwo 1 0 ∷
     RootTwo 0 0 ∷ RootTwo -1 0 ∷ RootTwo 1 -1 ∷ RootTwo 3 0 ∷ RootTwo 9 0 ∷ RootTwo 1105 0 ∷
     RootTwo 25 0 ∷ RootTwo 30 13 ∷ RootTwo 1000001 0 ∷ RootTwo 3 -2 ∷ RootTwo 2 0 ∷
     RootTwo 4 2 ∷ RootTwo 12345 6789 ∷ []

ts : List ZOmega
ts = Omega 1 2 3 4 ∷ Omega 123 -45 67 89 ∷ Omega 12345 -6789 1011 -1213 ∷
     Omega 123456789 -987654321 192837465 -564738291 ∷ []

xi-of : ZOmega -> ZRootTwo
xi-of t with zroottwo-of-zomega (adj t * t)
... | just x = x
... | nothing = 0

dyadics : List DRootTwo
dyadics = roothalf ∷ 3 * half * half + roothalf * half ∷ 5 * half ^ 3 ∷ 13 * half * half ∷
          1 - roottwo * half * half ∷ 2 + roothalf ∷ []

take : {A : Set} -> ℕ -> List A -> List A
take ℕ.zero _ = []
take (ℕ.suc n) [] = []
take (ℕ.suc n) (x ∷ xs) = x ∷ take n xs

-- ----------------------------------------------------------------------
-- The tests: (computed, expected from Haskell)

tests : List (String × String)
tests =
  (hs-list (map (λ x -> steps (hs-maybe prec11) (diophantine g x)) xs) ,
   "[(Just (Omega 0 (-3) 0 (-2)),1),(Just (Omega 0 0 1 1),1),(Nothing,0),(Just (Omega 0 1 0 (-2)),1),(Nothing,2),(Just (Omega 0 0 0 1),1),(Just (Omega 0 0 0 0),0),(Nothing,0),(Nothing,0),(Just (Omega 1 0 1 (-1)),1),(Just (Omega 0 0 0 3),5),(Just (Omega 0 23 0 24),11),(Just (Omega 0 0 0 5),5),(Just (Omega 4 2 3 1),2),(Just (Omega 0 1 0 1000),6),(Just (Omega (-1) 0 1 (-1)),1),(Just (Omega (-1) 0 1 0),1),(Just (Omega (-1) 1 1 1),1),(Nothing,0)]") ∷
  (hs-list (map (λ t -> let x = xi-of t in hs-pair (show x) (steps (hs-maybe prec11) (diophantine g x))) ts) ,
   "[(30 + 16*roottwo,(Just (Omega 1 (-4) (-3) (-2)),1)),(29564 - 13534*roottwo,(Just (Omega (-45) 131 (-53) 87),9)),(200983036 - 76925742*roottwo,(Just (Omega (-12345) 6789 (-1011) 1213),1)),(1346818261769388468 - 351571311063236250*roottwo,(Just (Omega 824027115 (-606014641) (-532814671) 129044011),1052))]") ∷
  (hs-list (map (λ x -> steps (hs-maybe prec11) (diophantine-associate g x)) (take 8 xs)) ,
   "[(Just (Omega 0 (-3) 0 (-2)),1),(Just (Omega (-2) 2 5 5),1),(Nothing,0),(Just (Omega 0 1 0 (-2)),1),(Nothing,2),(Just (Omega 0 0 0 1),1),(Just (Omega 0 0 0 0),0),(Just (Omega 0 0 0 1),1)]") ∷
  (hs-list (map (λ x -> steps (hs-maybe prec11) (diophantine-dyadic g x)) dyadics) ,
   "[(Nothing,0),(Nothing,0),(Just (roothalf^3 * Omega 0 1 0 (-2)),1),(Just (roothalf^2 * Omega 0 (-3) 0 (-2)),1),(Nothing,0),(Nothing,0)]") ∷
  (bounded show (find-factor g 91) , "Just (13,2)") ∷
  (bounded show (find-factor g 1000001) , "Just (101,13)") ∷
  (bounded show (find-factor g 100) , "Just (2,0)") ∷
  (show (power-mod 3 100 7) , "4") ∷
  (show (power-mod 12345 6789 1000003) , "644220") ∷
  (show (power-mod 2 0 5) , "1") ∷
  (bounded show (root-of-negative-one g 13) , "Just (5,2)") ∷
  (bounded show (root-of-negative-one g 1000033) , "Just (350504,1)") ∷
  (bounded show (root-mod g 17 2) , "Just (6,1)") ∷
  (bounded show (root-mod g 1000003 5) , "Nothing") ∷
  (show-rpf (relatively-prime-factors (ℤ ∋' 12) 18) , "(1,[(3,3),(2,3)])") ∷
  (show-rpf (relatively-prime-factors (ZRootTwo ∋' RootTwo 7 0) (RootTwo 3 1)) , "(1,[(3 + roottwo,2),(3 - roottwo,1)])") ∷
  (show-rpf (relatively-prime-factors (ℤ ∋' 360) 84) , "(1,[(7,1),(5,1),(2,5),(3,3)])") ∷
  (hs-maybe (λ m -> "(" ++ hs-maybe prec11 m ++ ")") (run-bounded 3 (diophantine g (RootTwo 1000001 0))) , "Nothing") ∷
  (show (subtask 3 (diophantine g (RootTwo 13 0))) , "Incomplete") ∷
  []
  where
    _∋'_ : (A : Set) -> A -> A
    A ∋' x = x
    show-rpf : {A : Set} {{_ : Show A}} -> A × List (A × ℕ) -> String
    show-rpf (u , fs) = hs-pair (show u) (hs-list (map (λ (f , k) -> hs-pair (show f) (NatS.show k)) fs))

-- ----------------------------------------------------------------------
-- Checking the solutions: t†t = ξ.

-- (We use helper functions instead of "with SC.run ...", since the
-- with-abstraction makes the type checker normalize the computation.)
check-zroottwo : ZRootTwo -> Bool
check-zroottwo x = go (SC.run (diophantine g x))
  where
    go : Maybe (Maybe ZOmega) -> Bool
    go (just (just t)) = adj t * t == fromZRootTwo x
    go (just nothing) = true
    go nothing = false

check-drootwo : DRootTwo -> Bool
check-drootwo x = go (SC.run (diophantine-dyadic g x))
  where
    go : Maybe (Maybe DOmega) -> Bool
    go (just (just t)) = adj t * t == fromDRootTwo x
    go (just nothing) = true
    go nothing = false

-- Elements with known solutions (norms t†t), which must be found.
check-known : ZOmega -> Bool
check-known t = go (SC.run (diophantine g (xi-of t)))
  where
    go : Maybe (Maybe ZOmega) -> Bool
    go (just (just t')) = adj t' * t' == adj t * t
    go _ = false

-- Associates: t†t ~ ξ.
check-assoc : ZRootTwo -> Bool
check-assoc x = go (SC.run (diophantine-associate g x))
  where
    go : Maybe (Maybe ZOmega) -> Bool
    go (just (just t)) = euclid-associates (adj t * t) (fromZRootTwo x)
    go (just nothing) = true
    go nothing = false

-- Some expected "no solution" answers: ξ < 0, ξ• < 0, primes ≡ 7
-- (mod 8), and 3·7.
nothings : List ZRootTwo
nothings = RootTwo -1 0 ∷ RootTwo 1 -1 ∷ RootTwo 1 1 ∷ RootTwo 7 0 ∷ RootTwo 3 1 ∷ RootTwo 21 0 ∷ RootTwo 23 0 ∷ []

check-nothing : ZRootTwo -> Bool
check-nothing x = go (SC.run (diophantine g x))
  where
    go : Maybe (Maybe ZOmega) -> Bool
    go (just nothing) = true
    go _ = false

-- More doubly positive elements to solve.
more : List ZOmega
more = Omega 1 0 0 1 ∷ Omega 2 -1 3 5 ∷ Omega 17 23 -29 31 ∷ Omega 1000 -999 998 -997 ∷
       Omega 31415926 27182818 -14142135 17320508 ∷ (1 + ω) ^ 7 * Omega 3 1 4 1 ∷ []

report : String -> Bool -> String
report name b = name ++ ": " ++ (if b then "OK" else "FAILED")

main : Main
main = run do
  IO.Handle.hSetBuffering IO.Handle.stdout IO.Handle.noBuffering
  -- the comparison with Haskell, one line per test
  IO.List.mapM′ (λ (a , b) -> putStrLn ((if a StrP.== b then "  ok   " else "  DIFF ") ++ a ++
                                           (if a StrP.== b then "" else "\n  want " ++ b))) tests
  putStrLn (report "comparison with Haskell" (and (map (λ (a , b) -> a StrP.== b) tests)))
  putStrLn (report "t†t = ξ (ℤ[√2])" (and (map check-zroottwo xs)))
  putStrLn (report "t†t = ξ (known norms)" (and (map check-known (ts Data.List.Base.++ more))))
  putStrLn (report "t†t ~ ξ (associates)" (and (map check-assoc xs)))
  putStrLn (report "t†t = ξ (𝔻[√2])" (and (map check-drootwo dyadics)))
  putStrLn (report "expected Nothing" (and (map check-nothing nothings)))
