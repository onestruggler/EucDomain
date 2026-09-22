-- This module is an Agda port of the module
-- Quantum.Synthesis.Ring.SymReal of the Haskell package newsynth.
--
-- It provides ring instances for Quantum.Synthesis.SymReal. The
-- homomorphisms fromℤ/2^, fromℤ[√2] and fromD[√2] (Haskell's default
-- methods fromDyadic, fromZRootTwo, fromDRootTwo) produce the same
-- symbolic expressions as in Haskell.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.SymReal where

open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Product.Base using (_,_)

open import Instances
open import Literals
import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (ghc-power)
open import Quantum.Synthesis.Ring using (dyadic ; decompose-dyadic)
open import Quantum.Synthesis.SymReal

private
  -- ½ = 0.5 = fromRational (1/2).
  half-SymReal : SymReal
  half-SymReal = Div (Const 1) (Const 2)

  -- Haskell's default fromDyadic: fromInteger a * half^n, where
  -- (a, n) = decompose_dyadic x (and ^ is Haskell's (^)).
  fromDyadic-SymReal : ℤ -> ℕ -> SymReal
  fromDyadic-SymReal a n with decompose-dyadic (dyadic a n)
  ... | a' , n' = Times (Const a') (ghc-power half-SymReal n')

  roottwo-SymReal : SymReal
  roottwo-SymReal = Sqrt (Const 2)

instance
  HalfRingSymReal : HalfRing SymReal
  HalfRingSymReal .half = half-SymReal
  HalfRingSymReal .fromℤ/2^ = fromDyadic-SymReal

  -- roottwo = sqrt 2; fromZRootTwo (RootTwo x y) = fromInteger x + roottwo * fromInteger y.
  RootTwoRingSymReal : RootTwoRing SymReal
  RootTwoRingSymReal .roottwo = roottwo-SymReal
  RootTwoRingSymReal .fromℤ[√2] x y = Plus (Const x) (Times roottwo-SymReal (Const y))

  -- roothalf = sqrt 0.5; fromDRootTwo (RootTwo x y) = fromDyadic x + roottwo * fromDyadic y.
  RootHalfRingSymReal : RootHalfRing SymReal
  RootHalfRingSymReal .roothalf = Sqrt half-SymReal
  RootHalfRingSymReal .fromD[√2] a n b m =
    Plus (fromDyadic-SymReal a n) (Times roottwo-SymReal (fromDyadic-SymReal b m))

  AdjointSymReal : Adjoint SymReal
  AdjointSymReal .adj x = x

  Adjoint2SymReal : Adjoint2 SymReal
  Adjoint2SymReal .adj2 x = x
