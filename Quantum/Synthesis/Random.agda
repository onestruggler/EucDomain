-- A replacement for Haskell's System.Random, as used by newsynth.
--
-- newsynth depends on random < 1.2, whose standard generator StdGen
-- is L'Ecuyer's combined multiplicative linear congruential generator.
-- This module ports exactly the parts of random-1.1 that newsynth
-- uses (StdGen, next, split, mkStdGen, reading a StdGen from a
-- string, and randomR for integers and floating point numbers), so
-- that the Agda port makes the same random choices as the Haskell
-- implementation for the same seed.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Random where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals

-- ----------------------------------------------------------------------
-- * Random number generators

-- Haskell's RandomGen class: next returns a value uniformly
-- distributed in genRange, and split produces two independent
-- generators.
record RandomGen (G : Set) : Set where
  field
    next : G -> ℤ × G
    genRange : G -> ℤ × ℤ
    split : G -> G × G
open RandomGen {{...}} public

-- The standard generator: two seeds s1 ∈ [1, 2147483562] and
-- s2 ∈ [1, 2147483398].
record StdGen : Set where
  constructor StdGen'
  field
    s1 s2 : ℤ

private
  stdNext : StdGen -> ℤ × StdGen
  stdNext (StdGen' s1 s2) = z' , StdGen' s1'' s2''
    where
      k = s1 / 53668
      s1' = s1 * 40014 - k * (53668 * 40014) - k * 12211
      s1'' = if s1' <ᵇ 0 then s1' + 2147483563 else s1'
      k' = s2 / 52774
      s2' = s2 * 40692 - k' * (52774 * 40692) - k' * 3791
      s2'' = if s2' <ᵇ 0 then s2' + 2147483399 else s2'
      z = s1'' - s2''
      z' = if z <ᵇ 1 then z + 2147483562 else z

  stdSplit : StdGen -> StdGen × StdGen
  stdSplit std@(StdGen' s1 s2) with proj₂ (stdNext std)
  ... | StdGen' t1 t2 = StdGen' new-s1 t2 , StdGen' t1 new-s2
    where
      new-s1 = if s1 == 2147483562 then 1 else s1 + 1
      new-s2 = if s2 == 1 then 2147483398 else s2 - 1


instance
  RandomGenStdGen : RandomGen StdGen
  RandomGenStdGen .next = stdNext
  RandomGenStdGen .genRange _ = 1 , 2147483562
  RandomGenStdGen .split = stdSplit

-- Map an integer to a generator (Haskell's mkStdGen on a machine
-- integer: only the lowest 31 bits of the seed matter).
mkStdGen : ℤ -> StdGen
mkStdGen n = StdGen' (s1 + 1) (s2 + 1)
  where
    s = n % 2147483648
    q = s / 2147483562
    s1 = s % 2147483562
    s2 = q % 2147483398

private
  isSpace : Char -> Bool
  isSpace = Char.isSpace

  -- A decimal number at the start of the input, and the rest.
  number : List Char -> Maybe (ℕ × List Char)
  number cs = go cs nothing
    where
      go : List Char -> Maybe ℕ -> Maybe (ℕ × List Char)
      go [] nothing = nothing
      go [] (just n) = just (n , [])
      go (c ∷ cs) acc with Char.isDigit c | acc
      ... | true | nothing = go cs (just (Char.toℕ c Nat.∸ Char.toℕ '0'))
      ... | true | just n = go cs (just (n * 10 + (Char.toℕ c Nat.∸ Char.toℕ '0')))
      ... | false | nothing = nothing
      ... | false | just n = just (n , c ∷ cs)

  -- Two decimal numbers separated by white space.
  decimals : List Char -> Maybe (ℕ × ℕ)
  decimals cs with number (List.dropWhileᵇ isSpace cs)
  ... | nothing = nothing
  ... | just (a , rest) with number (List.dropWhileᵇ isSpace rest)
  ...   | nothing = nothing
  ...   | just (b , _) = just (a , b)

-- Parse a generator from a string, like Haskell's "read s :: StdGen":
-- a string of two decimal numbers "s1 s2" denotes StdGen s1 s2
-- (without range checks), and any other string is hashed from its
-- first 6 characters. E.g. read "1" gives StdGen 53 1.
readStdGen : String -> StdGen
readStdGen str with decimals (String.toList str)
... | just (a , b) = StdGen' (+ a) (+ b)
... | nothing = mkStdGen (+ List.foldl (λ a c -> Char.toℕ c + 3 * a) 1 (List.take 6 (String.toList str)))

instance
  ShowStdGen : Show StdGen
  ShowStdGen .showsPrec d (StdGen' s1 s2) = showsPrec d s1 ++ " " ++ showsPrec d s2

-- ----------------------------------------------------------------------
-- * Random values

-- randomIvalInteger (l, h) g: a random integer in [l, h]. Random
-- values are drawn until their range exceeds 1000 times the size of
-- the interval.
private
  -- ival-loop fuel genlo b magtgt mag v g: draw values in base b until
  -- the magnitude reaches magtgt. mag grows by a factor b ≥ 2 in each
  -- step, so ∣magtgt∣ + 1 steps of fuel always suffice.
  ival-loop : {G : Set} {{_ : RandomGen G}} -> ℕ -> ℤ -> ℤ -> ℤ -> ℤ -> ℤ -> G -> ℤ × G
  ival-loop zero genlo b magtgt mag v g = v , g
  ival-loop (suc fuel) genlo b magtgt mag v g with magtgt ≤ᵇ mag
  ... | true = v , g
  ... | false with next g
  ...   | x , g' = ival-loop fuel genlo b magtgt (mag * b) (v * b + (x - genlo)) g'

  ival : {G : Set} {{_ : RandomGen G}} -> ℤ -> ℤ -> G -> ℤ × G
  ival l h rng with genRange rng
  ... | genlo , genhi with ival-loop (suc Int.∣ k * 1000 ∣) genlo (genhi - genlo + 1) (k * 1000) 1 0 rng
    where k = h - l + 1
  ...   | v , rng' with nonZero? (h - l + 1)
  ...     | yes nz = l + _%_ v (h - l + 1) {{nz}} , rng'
  -- impossible, since l ≤ h
  ...     | no _ = l , rng'

randomIvalInteger : {G : Set} {{_ : RandomGen G}} -> ℤ × ℤ -> G -> ℤ × G
randomIvalInteger (l , h) rng = if h <ᵇ l then ival h l rng else ival l h rng

-- Haskell's Random class.
record Random (A : Set) : Set₁ where
  field
    -- randomR (lo , hi) g returns a value in [lo, hi] (for
    -- continuous types, in [lo, hi)).
    randomR : {G : Set} {{_ : RandomGen G}} -> A × A -> G -> A × G
    -- A value in the default range of the type (for Float: [0, 1)).
    random : {G : Set} {{_ : RandomGen G}} -> G -> A × G
open Random {{...}} public


instance
  Randomℤ : Random ℤ
  Randomℤ .randomR = randomIvalInteger
  Randomℤ .random = randomIvalInteger (-9223372036854775808 , 9223372036854775807)

  Randomℕ : Random ℕ
  Randomℕ .randomR (lo , hi) g with randomIvalInteger (+ lo , + hi) g
  ... | x , g' = Int.∣ x ∣ , g'
  Randomℕ .random g with randomIvalInteger (0 , 9223372036854775807) g
  ... | x , g' = Int.∣ x ∣ , g'

-- Haskell's Double instance: 53 random bits taken from a random
-- 64-bit integer, and randomR (l, h) = l + coef (h - l) computed
-- without overflow.
randomDouble : {G : Set} {{_ : RandomGen G}} -> G -> Float × G
randomDouble g with randomIvalInteger (-9223372036854775808 , 9223372036854775807) g
... | x , g' = Float.fromℤ (x % 9007199254740992) / 9007199254740992.0 , g'

randomRDouble : {G : Set} {{_ : RandomGen G}} -> Float × Float -> G -> Float × G
randomRDouble (l , h) g with randomDouble g
... | coef , g' = (if h <ᵇ l then r h l else r l h) , g'
  where
    r : Float -> Float -> Float
    r l h = 2.0 * (0.5 * l + coef * (0.5 * h - 0.5 * l))


instance
  RandomFloat : Random Float
  RandomFloat .random = randomDouble
  RandomFloat .randomR = randomRDouble
