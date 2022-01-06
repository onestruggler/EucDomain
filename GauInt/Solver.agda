-- Automatic solvers for equations over Gaussian Integers.
{-# OPTIONS --without-K --safe #-}

module GauInt.Solver where

import Algebra.Solver.Ring.Simple as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import GauInt.Properties

------------------------------------------------------------------------
-- A module for automatically solving propositional equivalences
-- containing _+𝔾_ and _*𝔾_

module +-*-Solver =
  Solver (ACR.fromCommutativeRing +-*-commutativeRing) _≟_
