-- This file defines instances for natural numbers and integers to
-- overload various operations.

{-# OPTIONS --without-K --safe #-}

module Instances where

-- imports from stdlib.
import Data.Nat as Nat
import Data.Integer as Int
import Data.Integer.DivMod as IDM
import Data.Nat.DivMod as NDM

-- imports from local. 
open import Typeclasses public

-- Natural numbers form a semiring.
instance
  SMℕ : SemiRing Nat.ℕ
  SMℕ ._+_ = Nat._+_
  SMℕ ._*_ = Nat._*_
  SMℕ .0# = 0
  SMℕ .1# = 1

-- Integers form a semiring.
instance
  SMℤ : SemiRing Int.ℤ
  SMℤ ._+_ = Int._+_
  SMℤ ._*_ = Int._*_
  SMℤ .0# = Int.0ℤ
  SMℤ .1# = Int.1ℤ

-- The set of intergers is a ring.  
instance
  Ringℤ : Ring Int.ℤ 
  Ringℤ .sra = SMℤ
  Ringℤ .-_ = Int.-_

-- The usual order on ℕ is decidable. 
instance
  DOℕ : DecOrd Nat.ℕ
  DOℕ ._≤_   = Nat._≤_
  DOℕ ._≤?_  = Nat._≤?_
  DOℕ ._<_   = Nat._<_
  DOℕ ._<?_  = Nat._<?_

-- The usual order on ℤ is decidable. 
instance
  DOℤ : DecOrd Int.ℤ
  DOℤ ._≤_   = Int._≤_
  DOℤ ._≤?_  = Int._≤?_
  DOℤ ._<_   = Int._<_
  DOℤ ._<?_  = Int._<?_

-- ℕ has NonZero stucture on it defined in Data.Nat.Base.
instance
  NZTℕ : NonZeroTypeclass Nat.ℕ
  NZTℕ .NonZero = Nat.NonZero

-- ℤ has NonZero stucture on it defined in Data.Integer.Base.
  NZTℤ : NonZeroTypeclass Int.ℤ
  NZTℤ .NonZero = Int.NonZero

-- div and mod function on ℕ. They are defined in Data.Nat.DivMod.
instance
  DMℕ : DivMod Nat.ℕ
  DMℕ .NZT = NZTℕ 
  DMℕ ._/_ = NDM._/_
  DMℕ ._%_ = NDM._%_

-- div and mod function on ℤ. They are defined in Data.Integer.DivMod.
instance
  DMℤ : DivMod Int.ℤ
  DMℤ .NZT = NZTℤ 
  DMℤ ._/_ = IDM._div_
  DMℤ ._%_ n d = Int.+ (n IDM.mod d) 

-- Identity function can be used as the rank function.     
instance
  Rankℕ : Rank Nat.ℕ
  Rankℕ .rank x = x 

-- Absolute value function can be used as the rank function.     
instance
  Rankℤ : Rank Int.ℤ
  Rankℤ .rank = Int.∣_∣
