-- This module is an Agda port of the module Quantum.Synthesis.Matrix
-- of the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It provides fixed but arbitrary sized vectors and matrices. The
-- dimensions of the vectors and matrices are determined by the type,
-- for example
--
--   Matrix 2 3 CDouble
--
-- for complex 2×3-matrices. The type system ensures that there are no
-- run-time dimension errors.
--
-- Differences from the Haskell version:
--
-- * Haskell's type-level natural numbers (Zero, Succ, the Nat class,
--   Plus, Times) are replaced by ordinary indices n : ℕ. The names
--   One, Two, ..., Ten and Ten-and are kept as abbreviations, and
--   Plus/Times are ℕ's _+_/_*_. Functions with a (Nat n) constraint
--   take n as an implicit argument, which is inferred from the type.
--
-- * Vector n A is the standard library's Vec A n, with constructors
--   [] and _∷_ (Haskell: Nil and Cons).
--
-- * Matrices are wrapped in a record with constructor Matrix' (Haskell:
--   Matrix) and field unMatrix. As in Haskell, a Matrix m n A consists
--   of n columns of m entries each.
--
-- * Functions that raise an error in Haskell on bad input (vector,
--   matrix-of-columns, matrix-of-rows, matrix, vector-index,
--   matrix-index) return a Maybe.
--
-- * The index type of vector-of-function, matrix-of-function is ℕ
--   (Haskell: any Num type).
--
-- * Haskell has overlapping Show instances for matrices over DRootTwo,
--   DRComplex and DOmega (which pull out a common denominator
--   exponent). Since Agda does not support overlapping instances, we
--   give a Show instance for matrices over each particular entry type
--   (ℤ, ℚ, Float, Z2, Dyadic, ZRootTwo, QRootTwo, ..., DOmega), built
--   from the generic helper showsPrec-Matrix and showsPrec-DenomExp.
--   The printed output is the same as in Haskell.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Matrix where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Maybe.Effectful as MaybeE
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Rational.Base using (ℚ)
open import Data.Float.Base using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; uncurry)
open import Data.String.Base as String using (String ; _++_)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Effect.Monad using (RawMonad)
open import Function.Base using (_∘_ ; const)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring

-- ----------------------------------------------------------------------
-- * Type-level natural numbers

-- In Agda, dimensions are ordinary natural numbers. We keep the
-- Haskell names of the small numbers as abbreviations.
One Two Three Four Five Six Seven Eight Nine Ten : ℕ
One = 1
Two = 2
Three = 3
Four = 4
Five = 5
Six = 6
Seven = 7
Eight = 8
Nine = 9
Ten = 10

-- The 10th successor of a natural number. For example, the natural
-- number 18 is Ten-and Eight.
Ten-and : ℕ -> ℕ
Ten-and a = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc a)))))))))

-- Addition and multiplication of "type-level" natural numbers. These
-- are ℕ's addition and multiplication, which satisfy the same
-- defining equations as in Haskell:
--
--   Plus Zero m = m,       Plus (Succ n) m = Succ (Plus n m),
--   Times Zero m = Zero,   Times (Succ n) m = Plus m (Times n m).
Plus Times : ℕ -> ℕ -> ℕ
Plus = Nat._+_
Times = Nat._*_

-- A singleton type for the natural numbers: NNat n contains only the
-- natural number n.
data NNat : ℕ -> Set where
  Zero : NNat zero
  Succ : {n : ℕ} -> NNat n -> NNat (suc n)

-- Convert an NNat to an integer.
fromNNat : {n : ℕ} -> NNat n -> ℤ
fromNNat Zero = 0
fromNNat (Succ n) = 1 + fromNNat n

-- Return the term-level natural number corresponding to n.
nnat : {n : ℕ} -> NNat n
nnat {zero} = Zero
nnat {suc n} = Succ nnat

-- Return the integer corresponding to n. (In Haskell, the argument is
-- a dummy argument of the type-level number n.)
nat : ℕ -> ℤ
nat n = + n

instance
  ShowNNat : {n : ℕ} -> Show (NNat n)
  ShowNNat .showsPrec d x = showsPrec d (fromNNat x)

-- ----------------------------------------------------------------------
-- * Auxiliary printing functions

-- Print a list as Haskell's show does, e.g. "[1,-2,3]". The elements
-- are printed in a context of precedence 0.
showList : {A : Set} -> (ℕ -> A -> String) -> List A -> String
showList sp xs = "[" ++ String.intersperse "," (List.map (sp 0) xs) ++ "]"

-- ----------------------------------------------------------------------
-- * Fixed-length vectors

-- Vector n A is the type of lists of length n with elements from A.
Vector : ℕ -> Set -> Set
Vector n A = Vec A n

-- Convert a fixed-length list to an ordinary list.
list-of-vector : {n : ℕ} {A : Set} -> Vector n A -> List A
list-of-vector = Vec.toList

showsPrec-Vector : {n : ℕ} {A : Set} -> (ℕ -> A -> String) -> ℕ -> Vector n A -> String
showsPrec-Vector sp d x = showParen d 10 ("vector " ++ showList sp (list-of-vector x))

instance
  DecEqVector : {n : ℕ} {A : Set} {{_ : DecEq A}} -> DecEq (Vector n A)
  DecEqVector ._≟_ = VecP.≡-dec _≟_

  ShowVector : {n : ℕ} {A : Set} {{_ : Show A}} -> Show (Vector n A)
  ShowVector .showsPrec = showsPrec-Vector showsPrec

-- Construct a vector of length 1.
vector-singleton : {A : Set} -> A -> Vector One A
vector-singleton x = x ∷ []

-- Return the length of a vector. Since this information is contained
-- in the type, the vector argument is not used.
vector-length : {n : ℕ} {A : Set} -> Vector n A -> ℕ
vector-length {n} _ = n

-- Zip two equal length lists.
vector-zipwith : {n : ℕ} {A B C : Set} -> (A -> B -> C) -> Vector n A -> Vector n B -> Vector n C
vector-zipwith = Vec.zipWith

-- Map a function over a fixed-length list.
vector-map : {n : ℕ} {A B : Set} -> (A -> B) -> Vector n A -> Vector n B
vector-map = Vec.map

-- Create the vector (0, 1, …, n-1).
vector-enum : {n : ℕ} {A : Set} {{_ : SemiRing A}} -> Vector n A
vector-enum {n} = aux n 0#
  where
    aux : {A : Set} {{_ : SemiRing A}} (k : ℕ) -> A -> Vector k A
    aux zero a = []
    aux (suc k) a = a ∷ aux k (a + 1#)

-- Create the vector (f(0), f(1), …, f(n-1)).
vector-of-function : {n : ℕ} {B : Set} -> (ℕ -> B) -> Vector n B
vector-of-function f = vector-map f vector-enum

-- Construct a vector from a list. The length n of the vector cannot
-- be inferred from the list, it must be given by the context. If the
-- list has the wrong length, return nothing (Haskell: error).
vector : {n : ℕ} {A : Set} -> List A -> Maybe (Vector n A)
vector {zero} [] = just []
vector {suc n} (h ∷ t) with vector {n} t
... | just v = just (h ∷ v)
... | nothing = nothing
vector _ = nothing

-- Return the ith element of the vector. Counting starts from 0.
-- Return nothing if the index is out of range (Haskell: error).
vector-index : {n : ℕ} {A : Set} -> Vector n A -> ℕ -> Maybe A
vector-index [] _ = nothing
vector-index (x ∷ _) zero = just x
vector-index (_ ∷ xs) (suc k) = vector-index xs k

-- Return a fixed-length list consisting of a repetition of the given
-- element. The length is determined by the context.
vector-repeat : {n : ℕ} {A : Set} -> A -> Vector n A
vector-repeat {n} x = Vec.replicate n x

-- Turn a list of columns into a list of rows.
vector-transpose : {n m : ℕ} {A : Set} -> Vector n (Vector m A) -> Vector m (Vector n A)
vector-transpose [] = vector-repeat []
vector-transpose (a ∷ as) = vector-zipwith _∷_ a (vector-transpose as)

-- Left strict fold over a fixed-length list.
vector-foldl : {n : ℕ} {A B : Set} -> (A -> B -> A) -> A -> Vector n B -> A
vector-foldl f x l = List.foldl f x (list-of-vector l)

-- Right fold over a fixed-length list.
vector-foldr : {n : ℕ} {A B : Set} -> (A -> B -> B) -> B -> Vector n A -> B
vector-foldr f x l = List.foldr f x (list-of-vector l)

-- Return the tail of a fixed-length list.
vector-tail : {n : ℕ} {A : Set} -> Vector (suc n) A -> Vector n A
vector-tail (h ∷ t) = t

-- Return the head of a fixed-length list.
vector-head : {n : ℕ} {A : Set} -> Vector (suc n) A -> A
vector-head (h ∷ t) = h

-- Append two fixed-length lists.
vector-append : {n m : ℕ} {A : Set} -> Vector n A -> Vector m A -> Vector (Plus n m) A
vector-append [] v = v
vector-append (h ∷ t) v = h ∷ vector-append t v

-- Version of sequence for fixed-length lists, for any monad.
vector-sequence : {n : ℕ} {M : Set -> Set} {A : Set} {{_ : RawMonad M}} -> Vector n (M A) -> M (Vector n A)
vector-sequence {{mon}} [] = RawMonad.pure mon []
vector-sequence {{mon}} (a ∷ as) =
  a >>= λ a' -> vector-sequence as >>= λ as' -> pure (a' ∷ as')
  where open RawMonad mon

instance
  ToDyadicVector : {n : ℕ} {A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (Vector n A) (Vector n B)
  ToDyadicVector .maybe-dyadic as = vector-sequence {{MaybeE.monad}} (vector-map maybe-dyadic as)

  WholePartVector : {n : ℕ} {A B : Set} {{_ : WholePart A B}} -> WholePart (Vector n A) (Vector n B)
  WholePartVector .from-whole = vector-map from-whole
  WholePartVector .to-whole = vector-map to-whole

  DenomExpVector : {Base : Set} {n : ℕ} {A : Set} {{_ : DenomExp Base A}} -> DenomExp Base (Vector n A)
  DenomExpVector {Base} .DenomExp.denomexp as = denomexpBy Base (list-of-vector as)
  DenomExpVector {Base} .DenomExp.denomexp-factor as k = vector-map (λ a -> denomexp-factorBy Base a k) as

-- ----------------------------------------------------------------------
-- * Matrices

-- An m×n-matrix is a list of n columns, each of which is a list of m
-- scalars. The type of square matrices of any fixed dimension is an
-- instance of the Ring class, and therefore the usual symbols, such
-- as "+" and "*" can be used on them. However, for non-square
-- matrices, the symbols "·+·" and "·*·" (Haskell: ".+." and ".*.") must be used.
record Matrix (m n : ℕ) (A : Set) : Set where
  constructor Matrix'
  field
    -- Decompose a matrix into a list of columns.
    unMatrix : Vector n (Vector m A)
open Matrix public

-- Return the size (m, n) of a matrix, where m is the number of rows,
-- and n is the number of columns. The matrix argument is not used.
matrix-size : {m n : ℕ} {A : Set} -> Matrix m n A -> ℕ × ℕ
matrix-size {m} {n} _ = m , n

-- ----------------------------------------------------------------------
-- ** Basic matrix operations


module _ {A : Set} {{_ : Ring A}} where

  infixl 6 _·+·_ _·-·_

  -- Addition of m×n-matrices.
  _·+·_ : {m n : ℕ} -> Matrix m n A -> Matrix m n A -> Matrix m n A
  Matrix' a ·+· Matrix' b = Matrix' (vector-zipwith (vector-zipwith _+_) a b)

  -- Subtraction of m×n-matrices.
  _·-·_ : {m n : ℕ} -> Matrix m n A -> Matrix m n A -> Matrix m n A
  Matrix' a ·-· Matrix' b = Matrix' (vector-zipwith (vector-zipwith _-_) a b)

-- Map some function over every element of a matrix.
matrix-map : {m n : ℕ} {A B : Set} -> (A -> B) -> Matrix m n A -> Matrix m n B
matrix-map f (Matrix' a) = Matrix' (vector-map (vector-map f) a)

-- Create the matrix whose i,j-entry is (i,j). Here i and j are
-- 0-based, i.e., the top left entry is (0,0).
matrix-enum : {m n : ℕ} {A : Set} {{_ : SemiRing A}} -> Matrix m n (A × A)
matrix-enum {A = A} = Matrix' (vector-map f vector-enum)
  where
    f : {m : ℕ} -> A -> Vector m (A × A)
    f i = vector-map (λ j -> j , i) vector-enum

-- Create the matrix whose i,j-entry is f i j. Here i and j are
-- 0-based, i.e., the top left entry is f 0 0.
matrix-of-function : {m n : ℕ} {B : Set} -> (ℕ -> ℕ -> B) -> Matrix m n B
matrix-of-function f = matrix-map (uncurry f) (matrix-enum {A = ℕ})

module _ {A : Set} {{_ : Ring A}} where

  infixl 7 _·*·_ _scalarmult_

  -- Multiplication of a scalar and an m×n-matrix.
  _scalarmult_ : {m n : ℕ} -> A -> Matrix m n A -> Matrix m n A
  x scalarmult m = matrix-map (x *_) m

  -- Multiplication of m×n-matrices.
  _·*·_ : {m n p : ℕ} -> Matrix m n A -> Matrix n p A -> Matrix m p A
  _·*·_ {m} (Matrix' a) (Matrix' b) = Matrix' (vector-map (mmv a) b)
    where
      msv : {k : ℕ} -> A -> Vector k A -> Vector k A
      msv k h = vector-map (k *_) h

      avv : {k : ℕ} -> Vector k A -> Vector k A -> Vector k A
      avv v w = vector-zipwith _+_ v w

      mmv : {n : ℕ} -> Vector n (Vector m A) -> Vector n A -> Vector m A
      mmv [] [] = vector-repeat 0#
      mmv (h ∷ []) (k ∷ []) = msv k h
      mmv (h ∷ t@(_ ∷ _)) (k ∷ s) = avv (msv k h) (mmv t s)

  -- Return the 0 matrix of the given dimension.
  null-matrix : {m n : ℕ} -> Matrix m n A
  null-matrix = Matrix' (vector-repeat (vector-repeat 0#))

module _ {A : Set} {{_ : Fractional A}} where
  infixl 7 _scalardiv_

  -- Division of an m×n-matrix by a scalar. (The divisor must be
  -- non-zero.)
  _scalardiv_ : {m n : ℕ} -> Matrix m n A -> (x : A) .{{_ : NonZero x}} -> Matrix m n A
  m scalardiv x = matrix-map (λ y -> y / x) m

-- Take the transpose of an m×n-matrix.
matrix-transpose : {m n : ℕ} {A : Set} -> Matrix m n A -> Matrix n m A
matrix-transpose (Matrix' a) = Matrix' (vector-transpose a)

-- Take the adjoint of an m×n-matrix. Unlike adj, this can be applied
-- to non-square matrices.
adjoint : {m n : ℕ} {A : Set} {{_ : Adjoint A}} -> Matrix m n A -> Matrix n m A
adjoint (Matrix' a) = Matrix' (vector-transpose (vector-map (vector-map adj) a))

-- Return the element in the ith row and jth column of the matrix.
-- Counting of rows and columns starts from 0. Return nothing if the
-- index is out of range (Haskell: error).
matrix-index : {m n : ℕ} {A : Set} -> Matrix m n A -> ℕ -> ℕ -> Maybe A
matrix-index (Matrix' a) i j with vector-index a j
... | just c = vector-index c i
... | nothing = nothing

-- Return a list of all the entries of a matrix, in some fixed but
-- unspecified order.
matrix-entries : {m n : ℕ} {A : Set} -> Matrix m n A -> List A
matrix-entries (Matrix' a) = List.concat (List.map list-of-vector (list-of-vector a))

-- Version of sequence for matrices.
matrix-sequence : {m n : ℕ} {M : Set -> Set} {A : Set} {{_ : RawMonad M}} -> Matrix m n (M A) -> M (Matrix m n A)
matrix-sequence {{mon}} (Matrix' a) =
  vector-sequence (vector-map vector-sequence a) >>= λ a' -> pure (Matrix' a')
  where open RawMonad mon

module _ {A : Set} {{_ : Ring A}} where

  -- Return the trace of a square matrix.
  tr : {n : ℕ} -> Matrix n n A -> A
  tr {n} (Matrix' a) = aux n a
    where
      aux : (k : ℕ) -> Vector k (Vector k A) -> A
      aux zero [] = 0#
      aux (suc k) ((h ∷ t) ∷ s) = h + aux k (vector-map vector-tail s)

  -- Return the square of the Hilbert-Schmidt norm of an
  -- m×n-matrix, defined by ‖M‖² = tr M M†.
  hs-sqnorm : {m n : ℕ} {{_ : Adjoint A}} -> Matrix n m A -> A
  hs-sqnorm m = tr (m ·*· adjoint m)

-- ----------------------------------------------------------------------
-- Class instances for matrices

instance
  DecEqMatrix : {m n : ℕ} {A : Set} {{_ : DecEq A}} -> DecEq (Matrix m n A)
  DecEqMatrix ._≟_ (Matrix' a) (Matrix' b) with a ≟ b
  ... | yes refl = yes refl
  ... | no a≠b = no λ { refl -> a≠b refl }

  ToDyadicMatrix : {m n : ℕ} {A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (Matrix m n A) (Matrix m n B)
  ToDyadicMatrix .maybe-dyadic (Matrix' a) with maybe-dyadic a
  ... | just b = just (Matrix' b)
  ... | nothing = nothing

  WholePartMatrix : {m n : ℕ} {A B : Set} {{_ : WholePart A B}} -> WholePart (Matrix m n A) (Matrix m n B)
  WholePartMatrix .from-whole (Matrix' a) = Matrix' (from-whole a)
  WholePartMatrix .to-whole (Matrix' a) = Matrix' (to-whole a)

  DenomExpMatrix : {Base : Set} {m n : ℕ} {A : Set} {{_ : DenomExp Base A}} -> DenomExp Base (Matrix m n A)
  DenomExpMatrix {Base} .DenomExp.denomexp (Matrix' a) = denomexpBy Base a
  DenomExpMatrix {Base} .DenomExp.denomexp-factor (Matrix' a) k = Matrix' (denomexp-factorBy Base a k)

-- The ring of square matrices.
module _ {A : Set} {{_ : Ring A}} {n : ℕ} where

  private
    -- The scalar matrix x·I.
    scalar : A -> Matrix n n A
    scalar x = matrix-of-function (λ i j -> if i Nat.≡ᵇ j then x else 0#)

  instance
    SemiRingMatrix : SemiRing (Matrix n n A)
    SemiRingMatrix ._+_ = _·+·_
    SemiRingMatrix ._*_ = _·*·_
    SemiRingMatrix .0# = null-matrix
    SemiRingMatrix .1# = scalar 1#
    SemiRingMatrix .fromℕ k = scalar (fromℕ k)

    RingMatrix : Ring (Matrix n n A)
    RingMatrix .sra = SemiRingMatrix
    RingMatrix .-_ = _scalarmult_ (- 1#)

    NumberMatrix : Number (Matrix n n A)
    NumberMatrix = number-from-semiring

    NegativeMatrix : Negative (Matrix n n A)
    NegativeMatrix = negative-from-ring

    AdjointMatrix : {{_ : Adjoint A}} -> Adjoint (Matrix n n A)
    AdjointMatrix .adj = adjoint

    Adjoint2Matrix : {{_ : Adjoint2 A}} -> Adjoint2 (Matrix n n A)
    Adjoint2Matrix .adj2 = matrix-map adj2

    HalfRingMatrix : {{_ : HalfRing A}} -> HalfRing (Matrix n n A)
    HalfRingMatrix .half = half scalarmult 1#
    HalfRingMatrix .fromℤ/2^ a k = fromℤ/2^ a k scalarmult 1#

    RootHalfRingMatrix : {{_ : RootHalfRing A}} -> RootHalfRing (Matrix n n A)
    RootHalfRingMatrix .roothalf = roothalf scalarmult 1#
    RootHalfRingMatrix .fromD[√2] a k b l = fromD[√2] a k b l scalarmult 1#

    RootTwoRingMatrix : {{_ : RootTwoRing A}} -> RootTwoRing (Matrix n n A)
    RootTwoRingMatrix .roottwo = roottwo scalarmult 1#
    RootTwoRingMatrix .fromℤ[√2] a b = fromℤ[√2] a b scalarmult 1#

    ComplexRingMatrix : {{_ : ComplexRing A}} -> ComplexRing (Matrix n n A)
    ComplexRingMatrix .i = i scalarmult 1#

    OmegaRingMatrix : {{_ : OmegaRing A}} -> OmegaRing (Matrix n n A)
    OmegaRingMatrix .omega = omega scalarmult 1#

-- ----------------------------------------------------------------------
-- ** Operations on block matrices

-- Stack matrices vertically.
stack-vertical : {m n p : ℕ} {A : Set} -> Matrix m n A -> Matrix p n A -> Matrix (Plus m p) n A
stack-vertical (Matrix' a) (Matrix' b) = Matrix' (vector-zipwith vector-append a b)

-- Stack matrices horizontally.
stack-horizontal : {m n p : ℕ} {A : Set} -> Matrix m n A -> Matrix m p A -> Matrix m (Plus n p) A
stack-horizontal (Matrix' a) (Matrix' b) = Matrix' (vector-append a b)

module _ {A : Set} {{_ : Ring A}} where

  -- Vertically concatenate a vector of matrices.
  concat-vertical : {m n p : ℕ} -> Vector p (Matrix m n A) -> Matrix (Times p m) n A
  concat-vertical [] = null-matrix
  concat-vertical (h ∷ t) = stack-vertical h (concat-vertical t)

  -- Repeat a matrix vertically, according to some vector of scalars.
  tensor-vertical : {m n p : ℕ} -> Vector p A -> Matrix m n A -> Matrix (Times p m) n A
  tensor-vertical v m = concat-vertical (vector-map (_scalarmult m) v)

  -- Horizontally concatenate a vector of matrices.
  concat-horizontal : {m n p : ℕ} -> Vector p (Matrix m n A) -> Matrix m (Times p n) A
  concat-horizontal [] = null-matrix
  concat-horizontal (h ∷ t) = stack-horizontal h (concat-horizontal t)

  -- Repeat a matrix horizontally, according to some vector of scalars.
  tensor-horizontal : {m n p : ℕ} -> Vector p A -> Matrix m n A -> Matrix m (Times p n) A
  tensor-horizontal v m = concat-horizontal (vector-map (_scalarmult m) v)

  -- Kronecker tensor of two matrices.
  tensor : {p q m n : ℕ} -> Matrix p q A -> Matrix m n A -> Matrix (Times p m) (Times q n) A
  tensor a b = concat-horizontal (vector-map concat-vertical (unMatrix (matrix-map (_scalarmult b) a)))

  -- Form a diagonal block matrix.
  oplus : {p q m n : ℕ} -> Matrix p q A -> Matrix m n A -> Matrix (Plus p m) (Plus q n) A
  oplus a b = stack-horizontal (stack-vertical a null-matrix) (stack-vertical null-matrix b)

  -- Form a controlled gate.
  matrix-controlled : {n : ℕ} -> Matrix n n A -> Matrix (Plus n n) (Plus n n) A
  matrix-controlled m = oplus 1# m

-- ----------------------------------------------------------------------
-- ** Constructors and destructors

-- A convenient abbreviation for the type of 2×2-matrices.
U2 : Set -> Set
U2 A = Matrix Two Two A

-- A convenient abbreviation for the type of 3×3-matrices.
SO3 : Set -> Set
SO3 A = Matrix Three Three A

-- A convenience constructor for matrices: turn a list of columns into
-- a matrix. The dimensions are determined by the context. Return
-- nothing if the input has the wrong dimensions (Haskell: error).
matrix-of-columns : {n m : ℕ} {A : Set} -> List (List A) -> Maybe (Matrix n m A)
matrix-of-columns {n} {m} cs with vector {m} cs
... | nothing = nothing
... | just v with vector-sequence {{MaybeE.monad}} (vector-map (vector {n}) v)
...   | just w = just (Matrix' w)
...   | nothing = nothing

-- A convenience constructor for matrices: turn a list of rows into a
-- matrix.
matrix-of-rows : {n m : ℕ} {A : Set} -> List (List A) -> Maybe (Matrix n m A)
matrix-of-rows rs with matrix-of-columns rs
... | just x = just (matrix-transpose x)
... | nothing = nothing

-- A synonym for matrix-of-rows.
matrix : {n m : ℕ} {A : Set} -> List (List A) -> Maybe (Matrix n m A)
matrix = matrix-of-rows

-- Turn a matrix into a list of columns.
columns-of-matrix : {n m : ℕ} {A : Set} -> Matrix n m A -> List (List A)
columns-of-matrix (Matrix' a) = List.map list-of-vector (list-of-vector a)

-- Turn a matrix into a list of rows.
rows-of-matrix : {n m : ℕ} {A : Set} -> Matrix n m A -> List (List A)
rows-of-matrix = columns-of-matrix ∘ matrix-transpose

-- A convenience constructor for 2×2-matrices. The arguments are by
-- rows.
matrix2x2 : {A : Set} -> A × A -> A × A -> Matrix Two Two A
matrix2x2 (a , b) (c , d) = Matrix' ((a ∷ c ∷ []) ∷ (b ∷ d ∷ []) ∷ [])

-- A convenience destructor for 2×2-matrices. The result is by rows.
from-matrix2x2 : {A : Set} -> Matrix Two Two A -> (A × A) × (A × A)
from-matrix2x2 (Matrix' ((a ∷ c ∷ []) ∷ (b ∷ d ∷ []) ∷ [])) = (a , b) , (c , d)

-- A convenience constructor for 3×3-matrices. The arguments are by
-- rows.
matrix3x3 : {A : Set} -> A × A × A -> A × A × A -> A × A × A -> Matrix Three Three A
matrix3x3 (a0 , a1 , a2) (b0 , b1 , b2) (c0 , c1 , c2) =
  Matrix' ((a0 ∷ b0 ∷ c0 ∷ []) ∷ (a1 ∷ b1 ∷ c1 ∷ []) ∷ (a2 ∷ b2 ∷ c2 ∷ []) ∷ [])

-- A convenience constructor for 4×4-matrices. The arguments are by
-- rows.
matrix4x4 : {A : Set} -> A × A × A × A -> A × A × A × A -> A × A × A × A -> A × A × A × A -> Matrix Four Four A
matrix4x4 (a0 , a1 , a2 , a3) (b0 , b1 , b2 , b3) (c0 , c1 , c2 , c3) (d0 , d1 , d2 , d3) =
  Matrix' ((a0 ∷ b0 ∷ c0 ∷ d0 ∷ []) ∷ (a1 ∷ b1 ∷ c1 ∷ d1 ∷ []) ∷
           (a2 ∷ b2 ∷ c2 ∷ d2 ∷ []) ∷ (a3 ∷ b3 ∷ c3 ∷ d3 ∷ []) ∷ [])

-- A convenience constructor for 3-dimensional column vectors.
column3 : {A : Set} -> A × A × A -> Matrix Three One A
column3 (a , b , c) = Matrix' ((a ∷ b ∷ c ∷ []) ∷ [])

-- A convenience destructor for 3-dimensional column vectors. This is
-- the inverse of column3.
from-column3 : {A : Set} -> Matrix Three One A -> A × A × A
from-column3 (Matrix' ((a ∷ b ∷ c ∷ []) ∷ [])) = a , b , c

-- A convenience constructor for turning a vector into a column matrix.
column-matrix : {n : ℕ} {A : Set} -> Vector n A -> Matrix n One A
column-matrix v = Matrix' (vector-singleton v)

-- ----------------------------------------------------------------------
-- ** Particular matrices

module _ {A : Set} {{_ : Ring A}} where

  -- Controlled-not gate.
  cnot : Matrix Four Four A
  cnot = matrix4x4 (1# , 0# , 0# , 0#)
                   (0# , 1# , 0# , 0#)
                   (0# , 0# , 0# , 1#)
                   (0# , 0# , 1# , 0#)

  -- Swap gate.
  swap : Matrix Four Four A
  swap = matrix4x4 (1# , 0# , 0# , 0#)
                   (0# , 0# , 1# , 0#)
                   (0# , 1# , 0# , 0#)
                   (0# , 0# , 0# , 1#)

-- A z-rotation gate, Rz(θ) = exp(-iθZ/2). We compute θ/2 as θ·½, so
-- we require a HalfRing instance instead of division.
zrot : {R : Set} {{_ : Ring R}} {{_ : HalfRing R}} {{_ : Floating R}} {{_ : Adjoint R}} -> R -> Matrix Two Two (R [i])
zrot theta = matrix2x2 (u , 0#) (0# , adj u)
  where
    u = Cplx (cos (theta * half)) (- sin (theta * half))

-- ----------------------------------------------------------------------
-- Printing

-- Print a matrix as newsynth does, e.g. "matrix [[1,0],[0,1]]", given
-- a printing function for the entries.
showsPrec-Matrix : {m n : ℕ} {A : Set} -> (ℕ -> A -> String) -> ℕ -> Matrix m n A -> String
showsPrec-Matrix sp d a = showParen d 10 ("matrix " ++ showList (λ _ -> showList sp) (rows-of-matrix a))

-- Show instances for matrices over the particular rings. Matrices
-- over DRootTwo, DRComplex and DOmega are printed with a common
-- denominator exponent pulled out, e.g.
-- "roothalf * matrix [[1,1],[1,-1]]".
instance
  ShowMatrixℕ : {m n : ℕ} -> Show (Matrix m n ℕ)
  ShowMatrixℕ .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixℤ : {m n : ℕ} -> Show (Matrix m n ℤ)
  ShowMatrixℤ .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixℚ : {m n : ℕ} -> Show (Matrix m n ℚ)
  ShowMatrixℚ .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixFloat : {m n : ℕ} -> Show (Matrix m n Float)
  ShowMatrixFloat .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixZ2 : {m n : ℕ} -> Show (Matrix m n Z2)
  ShowMatrixZ2 .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixDyadic : {m n : ℕ} -> Show (Matrix m n Dyadic)
  ShowMatrixDyadic .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixZRootTwo : {m n : ℕ} -> Show (Matrix m n ZRootTwo)
  ShowMatrixZRootTwo .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixQRootTwo : {m n : ℕ} -> Show (Matrix m n QRootTwo)
  ShowMatrixQRootTwo .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixZComplex : {m n : ℕ} -> Show (Matrix m n ZComplex)
  ShowMatrixZComplex .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixDComplex : {m n : ℕ} -> Show (Matrix m n DComplex)
  ShowMatrixDComplex .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixQComplex : {m n : ℕ} -> Show (Matrix m n QComplex)
  ShowMatrixQComplex .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixZRComplex : {m n : ℕ} -> Show (Matrix m n (ZRootTwo [i]))
  ShowMatrixZRComplex .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixQRComplex : {m n : ℕ} -> Show (Matrix m n QRComplex)
  ShowMatrixQRComplex .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixCDouble : {m n : ℕ} -> Show (Matrix m n CDouble)
  ShowMatrixCDouble .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixZOmega : {m n : ℕ} -> Show (Matrix m n ZOmega)
  ShowMatrixZOmega .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixQOmega : {m n : ℕ} -> Show (Matrix m n QOmega)
  ShowMatrixQOmega .showsPrec = showsPrec-Matrix showsPrec

  ShowMatrixDRootTwo : {m n : ℕ} -> Show (Matrix m n DRootTwo)
  ShowMatrixDRootTwo {m} {n} .showsPrec = showsPrec-DenomExp {Matrix m n DRootTwo} {Matrix m n ZRootTwo}

  ShowMatrixDRComplex : {m n : ℕ} -> Show (Matrix m n DRComplex)
  ShowMatrixDRComplex {m} {n} .showsPrec = showsPrec-DenomExp {Matrix m n DRComplex} {Matrix m n (ZRootTwo [i])}

  ShowMatrixDOmega : {m n : ℕ} -> Show (Matrix m n DOmega)
  ShowMatrixDOmega {m} {n} .showsPrec = showsPrec-DenomExp {Matrix m n DOmega} {Matrix m n ZOmega}
