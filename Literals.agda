-- Overloaded numeric literals.
--
-- After "open import Literals", natural number literals such as 0, 1,
-- 2 denote the corresponding element of any ring, and negative
-- literals such as -1, -2 as well, e.g.
--
--   0 : ℕ,   0 : ℤ,   -1 : ℚ,   2 + 3 * i : 𝔾,   1 - √2 : ℤ [√2].
--
-- Every ring type (constructor) has its own Number and Negative
-- instances, defined next to its Ring instance using
-- number-from-semiring and negative-from-ring (see Typeclasses).
-- Generic code over an abstract ring A gets literals from
--
--   module _ {A : Set} {{_ : Ring A}} where
--     open LiteralsFor A
--     double : A -> A
--     double x = 2 * x
--
-- Literal overloading is opt-in, because in a module where it is
-- active, *every* natural number literal is elaborated using the
-- instance search, including those of type ℕ. This is harmless for
-- ordinary code, but ℕ literals whose value is needed during type
-- checking of the same application, such as the arity in the ring
-- solver call "solve 1 (λ x → ...) refl x", are then elaborated too
-- late and the call fails. Modules using the ring solvers in this way
-- should not open Literals (or write the arity as suc zero).

{-# OPTIONS --without-K --safe #-}

module Literals where

open import Agda.Builtin.FromNat public using (Number ; fromNat)
open import Agda.Builtin.FromNeg public using (Negative ; fromNeg)

open import Typeclasses

module LiteralsFor (A : Set) {{_ : Ring A}} where
  instance
    numberA : Number A
    numberA = number-from-semiring

    negativeA : Negative A
    negativeA = negative-from-ring
