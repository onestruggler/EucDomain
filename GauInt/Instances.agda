-- Instances of Gaussian integers.
--
-- The ring structure (SemiRing, Ring, DecEq, Adjoint, NormedRing,
-- ComplexRing, ...) of 𝔾 = ℤ [i] comes from the generic instances of
-- Quantum.Synthesis.Ring. Here we give the instances specific to the
-- Euclidean structure: Rank and NonZero.

{-# OPTIONS --without-K --safe  #-}

module GauInt.Instances where

open import Data.Bool using (true ; false ; not ; T)
open import Data.Empty using (⊥)
open import Data.Integer using (+_ ; -[1+_] ; +[1+_])
open import Data.Nat using (suc )
open import Relation.Nullary using (yes ; no)

open import Instances hiding (i)
open import Quantum.Synthesis.Ring public
  using (_[i] ; Cplx ; SemiRingCplx ; RingCplx ; DecEqCplx ; AdjointCplx ; Adjoint2Cplx ;
         NormedRingCplx ; ComplexRingCplx ; ShowZComplex ; NumberCplx ; NegativeCplx)
open import GauInt.Base renaming (NonZero to NonZero𝔾 ; rank to rank𝔾 ; _==_ to _==𝔾_)

instance
  Rank𝔾 : Rank 𝔾
  Rank𝔾 .rank = rank𝔾

-- This depends on how the boolean equality on 𝔾 is defined. To be
-- precise, it depends on the order of comparing the components.
instance
  nzp : ∀ {n} {y} -> NonZero𝔾 (+ suc n + y i)
  nzp = _

  nzn : ∀ {n} {y} -> NonZero𝔾 (-[1+ n ] + y i)
  nzn = _

  nzpi : ∀ {n} -> NonZero𝔾 (0# + (+ suc n) i)
  nzpi = _

  nzni : ∀ {n} -> NonZero𝔾 (0# + (-[1+ n ]) i)
  nzni = _

instance
  NZT𝔾 : NonZeroTypeclass 𝔾
  NZT𝔾 .NonZero = NonZero𝔾
  NZT𝔾 .nonZero? x with x ==𝔾 0𝔾 in eq
  ... | true = no λ nz -> aux (NonZero𝔾.nonZero nz)
    where
      aux : T (not (x ==𝔾 0𝔾)) -> ⊥
      aux t rewrite eq = t
  ... | false = yes record { nonZero = aux }
    where
      aux : T (not (x ==𝔾 0𝔾))
      aux rewrite eq = _
