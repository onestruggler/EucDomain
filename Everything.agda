-- Imports every module of the library, so that
--   agda Everything.agda
-- type checks everything. (--guardedness is needed by the modules
-- using coinduction: StepComp, Diophantine, GridProblems, GridSynth.)

{-# OPTIONS --guardedness #-}

module Everything where

-- The ring framework: type classes, instances, overloaded literals.
import Typeclasses
import Typeclasses.Properties
import Instances
import Literals

-- The Euclidean domain structure of the Gaussian integers (the
-- original content of this repository), now based on the framework.
import EuclideanDomain
import Integer.Properties
import Integer.EucDomain
import Integer.EucDomain2
import GauInt.Base
import GauInt.Instances
import GauInt.Properties
import GauInt.Solver
import GauInt.EucDomain

-- Port of the Haskell package fixedprec.
import Data.Number.FixedPrec

-- Port of the Haskell package newsynth.
import Quantum.Synthesis.ArcTan2
import Quantum.Synthesis.Clifford
import Quantum.Synthesis.CliffordT
import Quantum.Synthesis.Diophantine
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.EulerAngles
import Quantum.Synthesis.GridProblems
import Quantum.Synthesis.GridSynth
import Quantum.Synthesis.LaTeX
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.Newsynth
import Quantum.Synthesis.QuadraticEquation
import Quantum.Synthesis.Random
import Quantum.Synthesis.Ring
import Quantum.Synthesis.Ring.FixedPrec
import Quantum.Synthesis.Ring.SymReal
import Quantum.Synthesis.RotationDecomposition
import Quantum.Synthesis.StepComp
import Quantum.Synthesis.SymReal
import Quantum.Synthesis.ToReal

-- Proofs that the rings of the framework are commutative rings.
import Quantum.Synthesis.Ring.Properties
import Quantum.Synthesis.Ring.Properties.Common
import Quantum.Synthesis.Ring.Properties.Cplx
import Quantum.Synthesis.Ring.Properties.Dyadic
import Quantum.Synthesis.Ring.Properties.Hom
import Quantum.Synthesis.Ring.Properties.Omega
import Quantum.Synthesis.Ring.Properties.Poly
import Quantum.Synthesis.Ring.Properties.RootTwo
import Quantum.Synthesis.Ring.Properties.Z2

-- The gridsynth command line program (not --safe: uses FFI for
-- stderr, time).
import Programs.GetOpt
import Programs.CommandLine
import Programs.Gridsynth

-- Tests (checked by evaluation during type checking; the *Run
-- modules are compiled programs printing results).
import Test.Clifford
import Test.CliffordT
import Test.CliffordTRun
import Test.CliffordTRun2
import Test.Diophantine
import Test.DiophantineRun
import Test.EuclideanDomain
import Test.FixedPrec
import Test.FixedPrecRun
import Test.GridProblems
import Test.GridProblemsRun
import Test.GridSynth
import Test.GridSynthRun
import Test.LaTeX
import Test.LaTeXRun
import Test.Matrix
import Test.MultiQubitSynthesis
import Test.Random
import Test.Ring
import Test.RingProperties
import Test.RotationDecompositionRun
import Test.StepComp

-- Shared scalar arithmetic, congruences, Gaussian units and dyadic embeddings.
import GauInt.Algebra
import GauInt.Algebra.Swap
import GauInt.Gamma
import GauInt.Gamma.Congruence
import GauInt.Gamma.Division
import GauInt.Gamma.ImagCongruence
import GauInt.Gamma.Integer
import GauInt.Gamma.NormCongruence
import GauInt.NormParity
import GauInt.Parity
import GauInt.TwoPower
import GauInt.Units
import Integer.Congruence
import Integer.Parity
import Integer.Residues
import Integer.Squares
import Integer.Sum
import Natural.Sum
import Quantum.Synthesis.Ring.Properties.DyadicComplex
import Finite.Check
import GauInt.Gamma.Residue

-- Shared matrix, residue and finite-search theory used by Kopt.
import Finite.Enumeration
import Finite.BooleanSearch
import Finite.FourSearch
import Finite.FourSearchFirst
import Finite.CachedFourSearch
import Finite.PrefixSearch
import Finite.SuffixSearch
import Finite.ScoreCache
import GauInt.Matrix
import GauInt.Matrix.Gram
import GauInt.Matrix.Euc
import GauInt.Matrix.Integer
import GauInt.Matrix.Clearing
import GauInt.Matrix.Presentation
import GauInt.Matrix.Denominator
import GauInt.Matrix.Normalization
import GauInt.Matrix.Normalization.Minimal
import GauInt.Matrix.Normalization.Gram
import GauInt.Matrix.Normalization.Homogeneous
import GauInt.Matrix.Normalization.Factor
import GauInt.Matrix.Homogeneous
import GauInt.Matrix.Dyadic
import GauInt.Matrix.Congruence
import GauInt.Matrix.Monomial
import GauInt.Matrix.Monomial.Gram
import GauInt.Matrix.Monomial.Unit
import GauInt.Matrix.Exterior
import GauInt.Matrix.Exterior.CauchyBinet
import GauInt.Matrix.Exterior.Minors
import GauInt.Matrix.Integer.Orthogonality
import GauInt.Matrix.Integer.Residues
import GauInt.Matrix.Integer.UnitRows
import GauInt.Matrix.UnitSupport
import GauInt.Matrix.Trace
import GauInt.Matrix.RowColumnGram
import GauInt.Gamma.ParityPairs
import GauInt.Gamma.UnitParity
import GauInt.Matrix.ResidueArithmetic
import GauInt.Matrix.OddCoordinates
import GauInt.Gamma.Residue.Arithmetic
import GauInt.Gamma.TypedResidue
import GauInt.Matrix.RelativePhase
import GauInt.Gamma.Bit
import GauInt.Gamma.Divisibility
import GauInt.Gamma.UnitNormal
import GauInt.Gamma.Residue.Tables
import Finite.BinaryMatrix
import GauInt.Matrix.Integer.Binary
import GauInt.Matrix.Binary
import GauInt.Gamma.Residue.Cases
