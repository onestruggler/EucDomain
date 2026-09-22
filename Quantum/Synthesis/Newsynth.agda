-- This module is an Agda port of the module Quantum.Synthesis.Newsynth
-- of the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It provides backward compatibility with older versions of the
-- newsynth package. Formerly, it contained an implementation of the
-- single-qubit Clifford+T approximation algorithm of
--
-- * Peter Selinger. Efficient Clifford+T approximation of single-qubit
--   operators. http://arxiv.org/abs/1212.6253.
--
-- Since the new algorithm in Quantum.Synthesis.GridSynth is better in
-- all cases, we now simply provide a compatible interface to that
-- algorithm.
--
-- New software should not use this module, and it may eventually be
-- removed.
--
-- Differences from the Haskell version: Double is Float; the number
-- of candidates of newsynth-stats is an ℤ (Haskell: Integer).

{-# OPTIONS --without-K --safe --guardedness #-}

module Quantum.Synthesis.Newsynth where

open import Data.List.Base as List using (List)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.GridSynth
open import Quantum.Synthesis.Random using (RandomGen)

-- Backward compatible interface to the approximate synthesis
-- algorithm. The parameters are:
--
-- * a precision b ≥ 0 in bits, such that ε = 2⁻ᵇ;
-- * an angle θ, to implement a Rz(θ) = exp(-iθZ/2) gate;
-- * a source of randomness g.
--
-- Output a unitary operator in the Clifford+T group that approximates
-- Rz(θ) to within ε in the operator norm. This operator can then be
-- converted to a list of gates with to-gates.
--
-- Note: the argument θ is given as a symbolic real number. It will
-- automatically be expanded to as many digits as are necessary for
-- the internal calculation.
newsynth : {G : Set} {{_ : RandomGen G}} -> Float -> SymReal -> G -> U2 DOmega
newsynth prec theta g = gridsynth g prec theta 25

-- A version of newsynth that also returns some statistics: log₀.₁ of
-- the actual approximation error (or nothing if the error is 0), and
-- the number of candidates tried.
newsynth-stats : {G : Set} {{_ : RandomGen G}} -> Float -> SymReal -> G -> U2 DOmega × Maybe Float × ℤ
newsynth-stats prec theta g = convert-stats (gridsynth-stats g prec theta 25)
  where
    err-d : Maybe Float -> Maybe Float
    err-d nothing = nothing
    err-d (just b) = just (b Float.* logBase 10.0 2.0)

    convert-stats : U2 DOmega × Maybe Float × CandidateInfo -> U2 DOmega × Maybe Float × ℤ
    convert-stats (op , err-b , cinfo) = op , err-d err-b , + List.length cinfo

-- A version of newsynth that returns a list of gates instead of a
-- matrix. The inputs are the same as for newsynth.
--
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
newsynth-gates : {G : Set} {{_ : RandomGen G}} -> Float -> SymReal -> G -> List Gate
newsynth-gates prec theta g = gridsynth-gates g prec theta 25
