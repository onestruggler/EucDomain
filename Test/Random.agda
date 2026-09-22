{-# OPTIONS --guardedness #-}
-- Prints random numbers from the port of random-1.1's StdGen, to be
-- compared with the Haskell reference (see the expected output below).
module Test.Random where
open import IO
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Integer.Base using (ℤ)
open import Data.Float.Base using (Float)
open import Data.String.Base using (String ; unwords)
open import Instances
open import Literals
open import Quantum.Synthesis.Random

draws : {A : Set} {{_ : Random A}} -> ℕ -> A -> A -> StdGen -> List A
draws zero lo hi g = []
draws (suc n) lo hi g with randomR (lo , hi) g
... | x , g' = x ∷ draws n lo hi g'

g1 : StdGen
g1 = readStdGen "1"

main : Main
main = run do
  putStrLn (show g1 String.++ " / " String.++ show (mkStdGen 1) String.++ " / " String.++ show (mkStdGen -12345678901))
  putStrLn (unwords (map show (draws {ℤ} 10 1 1000 g1)))
  putStrLn (unwords (map show (draws {ℤ} 3 -5 100000000000000000000000000000 (mkStdGen 42))))
  putStrLn (show (proj₁ (split g1)) String.++ " / " String.++ show (proj₂ (split g1)))
  putStrLn (show (proj₁ (random {Float} g1)) String.++ " " String.++ show (proj₁ (randomR {Float} (0.0 , 2.0) (proj₂ (split g1)))))
  where import Data.String.Base as String
