-- We use instance argument to overload the algebraic operations + and
-- * etc.. For example, Ring record here is like what Num class in
-- Haskell. Also like Haskell, we don't require the operations abide
-- by any laws (we can use the algebraic definitions in stdlib if
-- needed).

{-# OPTIONS --without-K --safe #-}

module Typeclasses where

-- ----------------------------------------------------------------------
-- Type classes for Ring.

-- SemiRing typecalss has two operations + and * and two special
-- numbers 0 and 1.
record SemiRing (A : Set) : Set where
  infixl 6 _+_
  infixl 7 _*_
  infixr 8 _^2
  field
    _+_ : A -> A -> A
    _*_ : A -> A -> A
    0# : A
    1# : A
  -- A useful shot-hand.
  _^2 : A -> A
  x ^2 = x * x

-- A special way to open a module in order to make the fields of the
-- record available as functions taking instance arguments.
open SemiRing {{...}} public

-- Ring typeclass is a subclass of SemiRing typeclass, and has
-- addtitve inverse. Hence we can define subtraction.
record Ring (A : Set) : Set where
  infixl 6 _-_
  infix 8 -_
  field
    {{sra}} : SemiRing A
    -_ : A -> A

  _-_ :  A -> A -> A
  _-_ x y = x + (- y)

open Ring {{...}} public

-- ----------------------------------------------------------------------
-- Type classes decidable order.

-- We will use orders on ℕ and ℤ simultaneously, so we also overload
-- the comparsion operations using typeclass.

-- Decidable order typeclass. Normally DecEq is a super class of
-- DecOrd, here we don't enforce this, since the main purpose is to
-- overload operators.

open import Relation.Binary using (Rel ; Decidable)

record DecOrd (A : Set) : Set₁ where
  infixl 4 _≤_ _<_
  infixl 4 _≤?_ _<?_
  field
    _≤_ : Rel A _
    _≤?_ : Decidable _≤_
    _<_ : Rel A _
    _<?_ : Decidable _<_
open DecOrd {{...}} public


-- ----------------------------------------------------------------------
-- Type classes NonZero and DivMod

-- We will use irrelevant implicit argument to exlude the zero divisor
-- case when defining the partial function "div" and "mod".  

record NonZeroTypeclass (A : Set) : Set₁  where
  field
    NonZero : (a : A) -> Set 

open NonZeroTypeclass {{...}} public

-- DivMod typeclass is used to overload _/_ and _%_.
record DivMod (A : Set) : Set₁ where
  infixl 7 _/_ _%_
  field
    {{NZT}} : NonZeroTypeclass A
    _/_     : (n d : A) .{{_ : NonZero d}} -> A
    _%_     : (n d : A) .{{_ : NonZero d}} -> A
open DivMod {{...}} public


-- ----------------------------------------------------------------------
-- Type classes for Rank (to be used in defining Euclidean structure)

-- Rank record has a rank function that spcifies the rank of the given
-- argument.
import Data.Nat as Nat
record Rank (A : Set) : Set where
  field
    rank : A -> Nat.ℕ
open Rank {{...}} public
