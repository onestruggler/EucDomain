-- This module is an Agda port of the module
-- Quantum.Synthesis.RotationDecomposition of the Haskell package
-- newsynth (by N. J. Ross and P. Selinger).
--
-- It provides functions for decomposing a unitary n×n operator into
-- one- and two-level unitaries.
--
-- The algorithm is adapted from Section 4.5.1 of Nielsen and Chuang.
-- In addition to what is described in Nielsen and Chuang, our
-- algorithm produces two-level operators that can be decomposed using
-- only two Euler angles. The algorithm produces at most n(n−1)/2
-- two-level operators of type R_z(δ)R_x(γ), as well as n one-level
-- operators of type [exp iθ]. Therefore, the decomposition of a
-- unitary n×n operator yields n² real parameters, which is optimal.
--
-- The functions are generic over a "real" type A (Haskell: Floating a,
-- ArcTan2 a, Random a, ...); they are meant for Float (Haskell Double)
-- and FixedPrec e. The arithmetic is done in exactly the same order as
-- in Haskell, so that the results agree with Haskell's (Float results
-- agree bit for bit).
--
-- Differences from the Haskell version:
--
-- * Haskell's (Eq a) constraint is replaced by (DecOrd A), and the
--   test "b == 0" in rowop is done as "b ≤ 0 ∧ 0 ≤ b" on both
--   components. For exact types and FixedPrec this is the same as
--   equality; for Float it is IEEE equality as in Haskell (the
--   DecEq Float instance of the framework compares bit patterns, so
--   that it would distinguish 0.0 and -0.0, unlike Haskell's ==).
--
-- * Indices (Haskell: Int) are natural numbers. In random-unitary, the
--   indices are drawn as integers exactly as in Haskell and then
--   converted with ∣_∣ (they are non-negative for n ≥ 2; for n = 1 the
--   converted index is also out of range, so the resulting matrix is
--   the same).
--
-- * Out-of-range matrix indices (impossible here) give 0 instead of an
--   error. Division is the total division _÷_ of EulerAngles.
--
-- * Haskell's test :: IO () uses the global generator (newStdGen); here
--   test takes the generator as an argument and returns the three
--   lines of output as a list of strings (see Test/RotationDecompositionRun
--   for a program printing them).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.RotationDecomposition where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Float.Base using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.MultiQubitSynthesis
open import Quantum.Synthesis.EulerAngles
open import Quantum.Synthesis.ArcTan2
open import Quantum.Synthesis.Random

-- ----------------------------------------------------------------------
-- * Elementary rotations

-- An elementary rotation is either a combined x- and z-rotation,
-- applied at indices j and k, or a phase change applied at index j.
--
-- * ERot-zx δ γ j k represents the operator R_z(δ)R_x(γ), applied to
--   levels j and k.
--
-- * ERot-phase θ j represents the operator [exp iθ] applied to level j.
--
-- Note: when we use a list of ElementaryRots to express a sequence of
-- operators, the operators are meant to be applied right-to-left,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
data ElementaryRot (A : Set) : Set where
  ERot-zx : A -> A -> Index -> Index -> ElementaryRot A
  ERot-phase : A -> Index -> ElementaryRot A

-- Printed as Haskell's derived Show instance, e.g.
-- "ERot_zx 1.5 (-0.25) 0 1".
showsPrec-ElementaryRot : {A : Set} -> (ℕ -> A -> String) -> ℕ -> ElementaryRot A -> String
showsPrec-ElementaryRot sp d (ERot-zx a b j k) =
  showParen d 10 ("ERot_zx " String.++ sp 11 a String.++ " " String.++ sp 11 b
    String.++ " " String.++ showsPrec 11 j String.++ " " String.++ showsPrec 11 k)
showsPrec-ElementaryRot sp d (ERot-phase a j) =
  showParen d 10 ("ERot_phase " String.++ sp 11 a String.++ " " String.++ showsPrec 11 j)

instance
  ShowElementaryRot : {A : Set} {{_ : Show A}} -> Show (ElementaryRot A)
  ShowElementaryRot .showsPrec = showsPrec-ElementaryRot showsPrec

module _ {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : Floating A}} where
  open LiteralsFor A

  -- Convert a symbolic elementary rotation to a concrete matrix.
  private
    -- (Values used more than once are passed as arguments, so that
    -- they are computed only once in compiled code.)
    zx-matrix2 : {n : ℕ} -> Index -> Index -> A [i] -> A [i] -> A [i] -> A [i] -> Matrix n n (A [i])
    zx-matrix2 j k cg sg ed ed' = twolevel-matrix (ed' * cg , - (i * ed' * sg)) (- (i * ed * sg) , ed * cg) j k

    zx-matrix : {n : ℕ} -> Index -> Index -> A -> A -> A -> A -> Matrix n n (A [i])
    zx-matrix j k cd sd cg sg = zx-matrix2 j k (Cplx cg 0) (Cplx sg 0) (Cplx cd sd) (Cplx cd (- sd))

  matrix-of-elementary : {n : ℕ} -> ElementaryRot A -> Matrix n n (A [i])
  matrix-of-elementary (ERot-zx delta gamma j k) =
    zx-matrix j k (cos (delta ÷ 2)) (sin (delta ÷ 2)) (cos (gamma ÷ 2)) (sin (gamma ÷ 2))
  matrix-of-elementary (ERot-phase theta j) = onelevel-matrix (Cplx (cos theta) (sin theta)) j

  -- Convert a sequence of elementary rotations to an n×n-matrix.
  matrix-of-elementaries : {n : ℕ} -> List (ElementaryRot A) -> Matrix n n (A [i])
  matrix-of-elementaries ops = List.foldl _*_ 1 (List.map matrix-of-elementary ops)

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- Construct a two-level n×n-matrix from a given 2×2-matrix and indices
-- j and k.
twolevel-matrix-of-matrix : {A : Set} {{_ : Ring A}} {n : ℕ} -> Matrix Two Two A -> Index -> Index -> Matrix n n A
twolevel-matrix-of-matrix u j k with from-matrix2x2 u
... | (a , b) , (c , d) = twolevel-matrix (a , b) (c , d) j k

private
  -- The (j,k) entry of a matrix, or 0 if out of range.
  index0 : {A : Set} {{_ : SemiRing A}} {m n : ℕ} -> Matrix m n A -> ℕ -> ℕ -> A
  index0 op j k with matrix-index op j k
  ... | just x = x
  ... | nothing = 0#

-- Extract the phase of the jth diagonal entry of the given matrix.
get-phase : {A : Set} {{_ : Ring A}} {{_ : ArcTan2 A}} {n : ℕ} -> Matrix n n (A [i]) -> Index -> ElementaryRot A
get-phase op j with index0 op j j
... | Cplx x y = ERot-phase (arctan2 y x) j

module _ {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : Floating A}}
         {{_ : DecOrd A}} {{_ : Adjoint A}} {{_ : ArcTan2 A}} where
  open LiteralsFor A

  private
    -- Haskell's (==) on complex numbers compared to 0 (IEEE semantics
    -- for Float, see the comment at the top).
    is-zero : A [i] -> Bool
    is-zero (Cplx x y) = (x ≤ᵇ 0) ∧ (0 ≤ᵇ x) ∧ (y ≤ᵇ 0) ∧ (0 ≤ᵇ y)

    -- Haskell's recip on Cplx a: Cplx (a/d) (-b/d), where -b/d
    -- parses as -(b/d).
    -- Haskell's real on Cplx a.
    realpart : A [i] -> A
    realpart (Cplx x _) = x

    cplx-recip : A [i] -> A [i]
    cplx-recip (Cplx a b) = Cplx (a ÷ d) (- (b ÷ d))
      where d = a ^ 2 + b ^ 2

  -- Perform a two-level operation on rows j and k of a matrix U, such
  -- that the resulting matrix has a 0 in the (j,k)-position. Return
  -- the inverse of the two-level operation used, as well as the
  -- updated matrix.
  private
    -- The last step of rowop, given the Euler angles (values used
    -- more than once are passed as arguments, so that they are
    -- computed only once in compiled code).
    rowop-step : {n : ℕ} -> Matrix n n (A [i]) -> Index -> Index -> A × A × A × A -> Matrix n n (A [i]) × List (ElementaryRot A)
    rowop-step op j k (_ , _ , gamma , delta) =
      twolevel-matrix-of-matrix (matrix-of-euler-angles (0 , 0 , gamma , delta)) k j ·*· op
      , ERot-zx (- delta) (- gamma) k j ∷ []

    rowop' : {n : ℕ} -> Matrix n n (A [i]) -> Index -> Index -> A [i] -> A [i] -> Matrix n n (A [i]) × List (ElementaryRot A)
    rowop' op j k a b =
      if is-zero b then (op , [])
      else rowop-step op j k (euler-angles mat)
      where
        -- 1 / Cplx s 0 = 1 * recip (Cplx s 0), as in Haskell.
        mat : Matrix Two Two (A [i])
        mat = (1 * cplx-recip (Cplx (sqrt (realpart (a * adj a + b * adj b))) 0))
                   scalarmult matrix2x2 (adj a , adj b) (b , - a)

  rowop : {n : ℕ} -> Matrix n n (A [i]) -> Index × Index -> Matrix n n (A [i]) × List (ElementaryRot A)
  rowop op (j , k) = rowop' op j k (index0 op k k) (index0 op j k)

  -- ----------------------------------------------------------------------
  -- * Decomposition into elementary rotations

  -- Convert an n×n-matrix to a sequence of elementary rotations.
  --
  -- Note: the list of elementary rotations will be returned in
  -- right-to-left order, i.e., as in the mathematical notation for
  -- matrix multiplication. This is the opposite of the quantum circuit
  -- notation.
  private
    -- [ (i,j) | j <- [0..n-2], i <- [j+1..n-1] ]
    rowop-pairs : ℕ -> List (ℕ × ℕ)
    rowop-pairs n = List.concatMap (λ j -> List.map (λ i -> (suc j Nat.+ i) , j) (List.upTo (n Nat.∸ suc j)))
                                   (List.upTo (n Nat.∸ 1))

    -- mapAccumL rowop.
    accum : {n : ℕ} -> Matrix n n (A [i]) -> List (ℕ × ℕ) -> Matrix n n (A [i]) × List (List (ElementaryRot A))
    accum-step : {n : ℕ} -> Matrix n n (A [i]) × List (ElementaryRot A) -> List (ℕ × ℕ) -> Matrix n n (A [i]) × List (List (ElementaryRot A))
    accum-cons : {n : ℕ} -> List (ElementaryRot A) -> Matrix n n (A [i]) × List (List (ElementaryRot A)) -> Matrix n n (A [i]) × List (List (ElementaryRot A))

    accum op [] = op , []
    accum op (p ∷ ps) = accum-step (rowop op p) ps
    accum-step (op1 , g1) ps = accum-cons g1 (accum op1 ps)
    accum-cons g1 (op2 , gs) = op2 , g1 ∷ gs

  rotation-decomposition : {n : ℕ} -> Matrix n n (A [i]) -> List (ElementaryRot A)
  rotation-decomposition {n} op = finish (accum op (rowop-pairs n))
    where
      finish : Matrix n n (A [i]) × List (List (ElementaryRot A)) -> List (ElementaryRot A)
      finish (op' , gates) = List.concat gates ++ List.reverse (List.map (get-phase op') (List.upTo n))

-- ----------------------------------------------------------------------
-- * Testing

module _ {A : Set} {{_ : Ring A}} {{_ : Fractional A}} {{_ : Floating A}} {{_ : Random A}} where
  open LiteralsFor A

  -- Return a "random" unitary n×n-matrix. These matrices will not
  -- quite be uniformly distributed; this function is primarily meant
  -- to generate test cases.
  random-unitary : {G : Set} {{_ : RandomGen G}} {n : ℕ} -> G -> Matrix n n (A [i])
  random-unitary {G} {n} g = matrix-of-elementaries (random-gates g (20 * n ^ 2))
    where
      nz : ℤ
      nz = + n

      random-gates : G -> ℕ -> List (ElementaryRot A)
      random-gates g zero = []
      random-gates g (suc m) with randomR {A} (0 , 2 * pi) g
      ... | gamma , g1 with randomR {A} (0 , 2 * pi) g1
      ... | delta , g1' with randomR {ℤ} (0 , 1) g1'
      ... | c , g2 with randomR {ℤ} (0 , nz - 2) g2
      ... | j , g3 with randomR {ℤ} (j + 1 , nz - 1) g3
      ... | k , g4 = h ∷ random-gates g4 m
        where
          h : ElementaryRot A
          h = if c == 0 then ERot-zx delta gamma Int.∣ j ∣ Int.∣ k ∣ else ERot-phase delta Int.∣ j ∣

-- Generate a random matrix, decompose it, and then re-calculate the
-- matrix from the decomposition. Haskell prints the three lines
--
--   m = ..., gates = ..., m' = ...
--
-- for a 4×4 matrix over CDouble and a new random generator; here the
-- generator is an argument and the lines are returned.
test : {G : Set} {{_ : RandomGen G}} -> G -> List String
test g = ("m = " String.++ show m) ∷ ("gates = " String.++ showList showsPrec gates)
       ∷ ("m' = " String.++ show m') ∷ []
  where
    m : Matrix Four Four CDouble
    m = random-unitary g
    gates : List (ElementaryRot Float)
    gates = rotation-decomposition m
    m' : Matrix Four Four CDouble
    m' = matrix-of-elementaries gates
