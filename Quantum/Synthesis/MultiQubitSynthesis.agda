-- This module is an Agda port of the module
-- Quantum.Synthesis.MultiQubitSynthesis of the Haskell package
-- newsynth (by N. J. Ross and P. Selinger).
--
-- It provides functions for the representation and exact synthesis of
-- multi-qubit Clifford+T operators. The multi-qubit Clifford+T exact
-- synthesis algorithm is described in the paper:
--
-- * Brett Giles, Peter Selinger. Exact synthesis of multiqubit
--   Clifford+T circuits. Physical Review A 87, 032332 (7 pages), 2013.
--   Available from http://arxiv.org/abs/1212.0506.
--
-- It generalizes the single-qubit exact synthesis algorithm of
-- Kliuchnikov, Maslov, and Mosca.
--
-- Differences from the Haskell version:
--
-- * Indices (Haskell: Int) are natural numbers; exponents of T and ω
--   (Haskell: Int) are integers.
--
-- * Haskell raises errors on invalid inputs (e.g. non-unitary
--   matrices, elements not divisible by √2, list indices out of
--   range). Here all functions are total; on such invalid inputs the
--   result is unspecified (the functions compute with documented
--   default values instead). On valid inputs, the results are those
--   of Haskell.
--
-- * The loop in row-step and row-step-alt is bounded by a fuel
--   parameter (default row-step-fuel = 16; the actual number of
--   iterations is at most 4). The loops in reduce-column and
--   synthesis-nqubit are structural (on the denominator exponent
--   resp. the number of columns).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.MultiQubitSynthesis where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.DivMod as IDM
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix

-- ----------------------------------------------------------------------
-- * Residues

-- A type class for things that have residues. In a typical instance,
-- A is a ring whose elements are expressed with coefficients in ℤ,
-- and B is a corresponding ring whose elements are expressed with
-- coefficients in ℤ₂. (In Haskell, B is functionally determined by
-- A.)
record Residue (A B : Set) : Set where
  field
    -- Return the residue of something.
    residue : A -> B
open Residue {{...}} public

instance
  Residueℤ : Residue ℤ Z2
  Residueℤ .residue = parity

  ResidueOmega : {A B : Set} {{_ : Residue A B}} -> Residue (A [ω]) (B [ω])
  ResidueOmega .residue (Omega a b c d) = Omega (residue a) (residue b) (residue c) (residue d)

  ResidueRootTwo : {A B : Set} {{_ : Residue A B}} -> Residue (A [√2]) (B [√2])
  ResidueRootTwo .residue (RootTwo a b) = RootTwo (residue a) (residue b)

  ResiduePair : {A A' B B' : Set} {{_ : Residue A A'}} {{_ : Residue B B'}} -> Residue (A × B) (A' × B')
  ResiduePair .residue (x , y) = residue x , residue y

  ResidueUnit : Residue ⊤ ⊤
  ResidueUnit .residue _ = _

  ResidueList : {A B : Set} {{_ : Residue A B}} -> Residue (List A) (List B)
  ResidueList .residue = List.map residue

  ResidueCplx : {A B : Set} {{_ : Residue A B}} -> Residue (A [i]) (B [i])
  ResidueCplx .residue (Cplx a b) = Cplx (residue a) (residue b)

  ResidueVector : {n : ℕ} {A B : Set} {{_ : Residue A B}} -> Residue (Vector n A) (Vector n B)
  ResidueVector .residue = vector-map residue

  ResidueMatrix : {m n : ℕ} {A B : Set} {{_ : Residue A B}} -> Residue (Matrix m n A) (Matrix m n B)
  ResidueMatrix .residue (Matrix' a) = Matrix' (residue a)

-- ----------------------------------------------------------------------
-- * One- and two-level operators

-- ----------------------------------------------------------------------
-- ** Symbolic representation

-- An index for a row or column of a matrix.
Index : Set
Index = ℕ

-- Symbolic representation of one- and two-level operators. Note that
-- the power k in the TL-T and TL-omega constructors can be positive
-- or negative, and should be regarded modulo 8.
--
-- Note: when we use a list of TwoLevel operators to express a
-- sequence of operators, the operators are meant to be applied
-- right-to-left, i.e., as in the mathematical notation for matrix
-- multiplication. This is the opposite of the quantum circuit
-- notation.
data TwoLevel : Set where
  -- X_{i,j}.
  TL-X : Index -> Index -> TwoLevel
  -- H_{i,j}.
  TL-H : Index -> Index -> TwoLevel
  -- (T_{i,j})^k.
  TL-T : ℤ -> Index -> Index -> TwoLevel
  -- (ω_i)^k.
  TL-omega : ℤ -> Index -> TwoLevel

private
  -- Helper for decidable equality of constructors with arguments.
  dec2 : {A B C : Set} {{_ : DecEq A}} {{_ : DecEq B}} (f : A -> B -> C) ->
         (∀ {a b a' b'} -> f a b ≡ f a' b' -> (a ≡ a') × (b ≡ b')) ->
         (a a' : A) (b b' : B) -> Relation.Nullary.Dec (f a b ≡ f a' b')
  dec2 f inj a a' b b' with a ≟ a' | b ≟ b'
  ... | yes refl | yes refl = yes refl
  ... | no p | _ = no λ eq -> p (proj₁ (inj eq))
  ... | yes _ | no p = no λ eq -> p (proj₂ (inj eq))

instance
  DecEqTwoLevel : DecEq TwoLevel
  DecEqTwoLevel ._≟_ (TL-X i j) (TL-X i' j') = dec2 TL-X (λ { refl -> refl , refl }) i i' j j'
  DecEqTwoLevel ._≟_ (TL-H i j) (TL-H i' j') = dec2 TL-H (λ { refl -> refl , refl }) i i' j j'
  DecEqTwoLevel ._≟_ (TL-T k i j) (TL-T k' i' j') with k ≟ k' | i ≟ i' | j ≟ j'
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no p | _ | _ = no λ { refl -> p refl }
  ... | yes _ | no p | _ = no λ { refl -> p refl }
  ... | yes _ | yes _ | no p = no λ { refl -> p refl }
  DecEqTwoLevel ._≟_ (TL-omega k i) (TL-omega k' i') = dec2 TL-omega (λ { refl -> refl , refl }) k k' i i'
  DecEqTwoLevel ._≟_ (TL-X _ _) (TL-H _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-X _ _) (TL-T _ _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-X _ _) (TL-omega _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-H _ _) (TL-X _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-H _ _) (TL-T _ _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-H _ _) (TL-omega _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-T _ _ _) (TL-X _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-T _ _ _) (TL-H _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-T _ _ _) (TL-omega _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-omega _ _) (TL-X _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-omega _ _) (TL-H _ _) = no λ ()
  DecEqTwoLevel ._≟_ (TL-omega _ _) (TL-T _ _ _) = no λ ()

  -- Printed as Haskell's derived Show instance, e.g. "TL_T (-1) 0 1".
  ShowTwoLevel : Show TwoLevel
  ShowTwoLevel .showsPrec d (TL-X i j) = showParen d 10 ("TL_X " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevel .showsPrec d (TL-H i j) = showParen d 10 ("TL_H " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevel .showsPrec d (TL-T k i j) = showParen d 10 ("TL_T " String.++ showsPrec 11 k String.++ " " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevel .showsPrec d (TL-omega k i) = showParen d 10 ("TL_omega " String.++ showsPrec 11 k String.++ " " String.++ showsPrec 11 i)

-- Invert a TwoLevel operator.
invert-twolevel : TwoLevel -> TwoLevel
invert-twolevel (TL-X i j) = TL-X i j
invert-twolevel (TL-H i j) = TL-H i j
invert-twolevel (TL-T m i j) = TL-T (- m) i j
invert-twolevel (TL-omega m j) = TL-omega (- m) j

-- Invert a list of TwoLevel operators.
invert-twolevels : List TwoLevel -> List TwoLevel
invert-twolevels gs = List.reverse (List.map invert-twolevel gs)

-- ----------------------------------------------------------------------
-- ** Constructors for two-level matrices

-- k mod 8, as a natural number.
mod8 : ℤ -> ℕ
mod8 k = k IDM.% (+ 8)

module _ {A : Set} {{_ : Ring A}} where

  -- Construct a two-level matrix with the given entries.
  twolevel-matrix : {n : ℕ} -> A × A -> A × A -> Index -> Index -> Matrix n n A
  twolevel-matrix (a , b) (c , d) i j = matrix-of-function f
    where
      f : ℕ -> ℕ -> A
      f x y =
        if (x == i) ∧ (y == i) then a
        else if (x == i) ∧ (y == j) then b
        else if (x == j) ∧ (y == i) then c
        else if (x == j) ∧ (y == j) then d
        else if x == y then 1#
        else 0#

  -- Construct a one-level matrix with the given entry.
  onelevel-matrix : {n : ℕ} -> A -> Index -> Matrix n n A
  onelevel-matrix a i = matrix-of-function f
    where
      f : ℕ -> ℕ -> A
      f x y =
        if (x == i) ∧ (y == i) then a
        else if x == y then 1#
        else 0#

  private
    -- Apply f to the ith entry of a vector (unchanged if i is out of
    -- range).
    vector-update : {n : ℕ} -> Index -> (A -> A) -> Vector n A -> Vector n A
    vector-update _ f [] = []
    vector-update zero f (x ∷ xs) = f x ∷ xs
    vector-update (suc i) f (x ∷ xs) = x ∷ vector-update i f xs

    -- Multiply a vector by twolevel-matrix (a , b) (c , d) i j. The
    -- function fast computes the new entries i and j from the old
    -- ones x and y (it must agree with (a x + b y , c x + d y)).
    apply2 : {n : ℕ} -> A × A -> A × A -> (A -> A -> A × A) -> Index -> Index -> Vector n A -> Vector n A
    apply2 {n} (a , b) (c , d) fast i j v =
      if i == j then vector-update i (a *_) v
      else go (vector-index v i) (vector-index v j)
      where
        go : Maybe A -> Maybe A -> Vector n A
        go (just x) (just y) with fast x y
        ... | x' , y' = vector-update i (λ _ -> x') (vector-update j (λ _ -> y') v)
        go (just x) nothing = vector-update i (λ _ -> a * x) v
        go nothing (just y) = vector-update j (λ _ -> d * y) v
        go nothing nothing = v

  module _ {{_ : OmegaRing A}} {{_ : RootHalfRing A}} where

    -- Convert a symbolic one- or two-level operator into a matrix.
    matrix-of-twolevel : {n : ℕ} -> TwoLevel -> Matrix n n A
    matrix-of-twolevel (TL-X i j) = twolevel-matrix (0# , 1#) (1# , 0#) i j
    matrix-of-twolevel (TL-H i j) = twolevel-matrix (s , s) (s , - s) i j
      where s = roothalf
    matrix-of-twolevel (TL-T k i j) = twolevel-matrix (1# , 0#) (0# , omega ^ mod8 k) i j
    matrix-of-twolevel (TL-omega k i) = onelevel-matrix (omega ^ mod8 k) i

    -- Convert a list of symbolic one- or two-level operators into a
    -- matrix. Note that the operators are to be applied right-to-left,
    -- exactly as in mathematical notation.
    matrix-of-twolevels : {n : ℕ} -> List TwoLevel -> Matrix n n A
    matrix-of-twolevels gs = List.foldl _*_ 1# (List.map matrix-of-twolevel gs)

    -- Multiply a vector by the matrix of a two-level operator, i.e.,
    -- apply-twolevel g v = matrix-of-twolevel g · v. (This is not in
    -- the Haskell library; it is used to speed up synthesis-nqubit,
    -- where it replaces a matrix product. In an exact ring such as
    -- 𝔻[ω] the results are identical.) For two distinct indices in
    -- range, only the two entries concerned are computed, with as few
    -- multiplications as possible; in the other cases the entries of
    -- the matrix are used as they are.
    apply-twolevel : {n : ℕ} -> TwoLevel -> Vector n A -> Vector n A
    apply-twolevel (TL-X i j) = apply2 (0# , 1#) (1# , 0#) (λ x y -> y , x) i j
    apply-twolevel (TL-H i j) = apply2 (s , s) (s , - s) (λ x y -> s * (x + y) , s * (x - y)) i j
      where s = roothalf
    apply-twolevel (TL-T k i j) = with-w (omega ^ mod8 k)
      where
        with-w : {n : ℕ} -> A -> Vector n A -> Vector n A
        with-w w = apply2 (1# , 0#) (0# , w) (λ x y -> x , w * y) i j
    apply-twolevel (TL-omega k i) = with-w (omega ^ mod8 k)
      where
        with-w : {n : ℕ} -> A -> Vector n A -> Vector n A
        with-w w = vector-update i (w *_)

    -- Multiply a vector by the matrix of a list of two-level operators,
    -- i.e., apply-twolevels gs v = matrix-of-twolevels gs · v.
    apply-twolevels : {n : ℕ} -> List TwoLevel -> Vector n A -> Vector n A
    apply-twolevels gs v = List.foldr apply-twolevel v gs

-- ----------------------------------------------------------------------
-- * Auxiliary list functions

-- Replace the ith element of a list by x.
list-insert : {A : Set} -> Index -> A -> List A -> List A
list-insert zero x (h ∷ t) = x ∷ t
list-insert (suc n) x (h ∷ t) = h ∷ list-insert n x t
list-insert n x [] = []

private
  -- The ith element of a list, or nothing.
  list-index : {A : Set} -> List A -> ℕ -> Maybe A
  list-index [] _ = nothing
  list-index (x ∷ _) zero = just x
  list-index (_ ∷ xs) (suc n) = list-index xs n

-- Apply a unary operator to element i of a list. (If i is out of
-- range, the list is returned unchanged; Haskell: error.)
transform-at : {A : Set} -> (A -> A) -> Index -> List A -> List A
transform-at op i lst with list-index lst i
... | just x = list-insert i (op x) lst
... | nothing = lst

-- Apply a binary operator to elements i and j of a list. (If i or j
-- is out of range, the list is returned unchanged; Haskell: error.)
transform-at2 : {A : Set} -> (A × A -> A × A) -> Index -> Index -> List A -> List A
transform-at2 op i j lst with list-index lst i | list-index lst j
... | just x | just y with op (x , y)
...   | x' , y' = list-insert i x' (list-insert j y' lst)
transform-at2 op i j lst | _ | _ = lst

-- Split a list into pairs. Return a list of pairs, and a final
-- element if the length of the list was odd.
list-pairs : {A : Set} -> List A -> List (A × A) × Maybe A
list-pairs [] = [] , nothing
list-pairs (h ∷ []) = [] , just h
list-pairs (h ∷ k ∷ t) with list-pairs t
... | t' , r' = (h , k) ∷ t' , r'

-- ----------------------------------------------------------------------
-- * Functions on ℤ[ω]

-- Given an element of the form ω^m, return m ∈ {0,…,7}, or nothing if
-- not of that form.
log-omega : ZOmega -> Maybe ℕ
log-omega x =
  if x == Omega 0 0 0 1 then just 0
  else if x == Omega 0 0 1 0 then just 1
  else if x == Omega 0 1 0 0 then just 2
  else if x == Omega 1 0 0 0 then just 3
  else if x == Omega 0 0 0 -1 then just 4
  else if x == Omega 0 0 -1 0 then just 5
  else if x == Omega 0 -1 0 0 then just 6
  else if x == Omega -1 0 0 0 then just 7
  else nothing

-- Multiply a scalar by ω^n.
omega-power : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} -> ℤ -> A -> A
omega-power n x = x * omega ^ mod8 n

-- Divide an element of ZOmega by √2. (If it is not divisible, the
-- result is unspecified; Haskell: error.)
reduce-ZOmega : ZOmega -> ZOmega
reduce-ZOmega (Omega a b c d) = Omega a' b' c' d'
  where
    a' = (b - d) / 2
    b' = (c + a) / 2
    c' = (b + d) / 2
    d' = (c - a) / 2

-- Apply the X operator to a 2-dimensional vector over ZOmega.
opX-zomega : ZOmega × ZOmega -> ZOmega × ZOmega
opX-zomega (x , y) = y , x

-- Apply the H operator to a 2-dimensional vector over ZOmega. (If the
-- result is not well-defined over ZOmega, it is unspecified.)
opH-zomega : ZOmega × ZOmega -> ZOmega × ZOmega
opH-zomega (x , y) = reduce-ZOmega (x + y) , reduce-ZOmega (x - y)

-- Apply a TwoLevel operator to a ZOmega-vector, represented as a
-- list.
apply-twolevel-zomega : TwoLevel -> List ZOmega -> List ZOmega
apply-twolevel-zomega (TL-X i j) w = transform-at2 opX-zomega i j w
apply-twolevel-zomega (TL-H i j) w = transform-at2 opH-zomega i j w
apply-twolevel-zomega (TL-T k i j) w = transform-at (omega-power k) j w
apply-twolevel-zomega (TL-omega k i) w = transform-at (omega-power k) i w

-- Apply a list of TwoLevel operators to a ZOmega-vector, represented
-- as a list.
apply-twolevels-zomega : List TwoLevel -> List ZOmega -> List ZOmega
apply-twolevels-zomega gs w = List.foldr apply-twolevel-zomega w gs

-- ----------------------------------------------------------------------
-- * Functions on residues

-- The residue type of t ∈ ℤ[ω] is the residue of t†t. It is 0000,
-- 0001, or 1010.
data ResidueType : Set where
  RT-0000 RT-0001 RT-1010 : ResidueType

private
  rt-code : ResidueType -> ℕ
  rt-code RT-0000 = 0
  rt-code RT-0001 = 1
  rt-code RT-1010 = 2

instance
  DecEqResidueType : DecEq ResidueType
  DecEqResidueType ._≟_ RT-0000 RT-0000 = yes refl
  DecEqResidueType ._≟_ RT-0000 RT-0001 = no λ ()
  DecEqResidueType ._≟_ RT-0000 RT-1010 = no λ ()
  DecEqResidueType ._≟_ RT-0001 RT-0000 = no λ ()
  DecEqResidueType ._≟_ RT-0001 RT-0001 = yes refl
  DecEqResidueType ._≟_ RT-0001 RT-1010 = no λ ()
  DecEqResidueType ._≟_ RT-1010 RT-0000 = no λ ()
  DecEqResidueType ._≟_ RT-1010 RT-0001 = no λ ()
  DecEqResidueType ._≟_ RT-1010 RT-1010 = yes refl

  -- The order RT-0000 < RT-0001 < RT-1010 (Haskell: deriving Ord).
  DecOrdResidueType : DecOrd ResidueType
  DecOrdResidueType = decOrd-from-bool (λ x y -> rt-code x Nat.≤ᵇ rt-code y) (λ x y -> rt-code x Nat.<ᵇ rt-code y)

-- Return the residue's ResidueType and the shift.
residue-type-shift : Z2 [ω] -> ResidueType × ℕ
residue-type-shift (Omega Even Even Even Even) = RT-0000 , 0
residue-type-shift (Omega Even Even Even Odd) = RT-0001 , 0
residue-type-shift (Omega Even Even Odd Even) = RT-0001 , 1
residue-type-shift (Omega Even Even Odd Odd) = RT-1010 , 0
residue-type-shift (Omega Even Odd Even Even) = RT-0001 , 2
residue-type-shift (Omega Even Odd Even Odd) = RT-0000 , 0
residue-type-shift (Omega Even Odd Odd Even) = RT-1010 , 1
residue-type-shift (Omega Even Odd Odd Odd) = RT-0001 , 3
residue-type-shift (Omega Odd Even Even Even) = RT-0001 , 3
residue-type-shift (Omega Odd Even Even Odd) = RT-1010 , 3
residue-type-shift (Omega Odd Even Odd Even) = RT-0000 , 0
residue-type-shift (Omega Odd Even Odd Odd) = RT-0001 , 2
residue-type-shift (Omega Odd Odd Even Even) = RT-1010 , 2
residue-type-shift (Omega Odd Odd Even Odd) = RT-0001 , 1
residue-type-shift (Omega Odd Odd Odd Even) = RT-0001 , 0
residue-type-shift (Omega Odd Odd Odd Odd) = RT-0000 , 0

-- Return the residue's ResidueType.
residue-type : Z2 [ω] -> ResidueType
residue-type r = proj₁ (residue-type-shift r)

-- Return the residue's shift. The shift is defined so that:
--
-- * 0001, 1110, 0011 have shift 0,
-- * 0010, 1101, 0110 have shift 1,
-- * 0100, 1011, 1100 have shift 2, and
-- * 1000, 0111, 1001 have shift 3.
--
-- Residues of type RT-0000 have shift 0.
residue-shift : Z2 [ω] -> ℕ
residue-shift r = proj₂ (residue-type-shift r)

-- Given two irreducible residues a and b of the same type, find an
-- index m such that a + ω^m b = 0000. If no such index exists, find
-- an index m such that a + ω^m b = 1111.
residue-offset : Z2 [ω] -> Z2 [ω] -> ℕ
residue-offset a b = (residue-shift a + 4 Nat.∸ residue-shift b) % 4

-- Check whether a residue is reducible. A residue r is called
-- reducible if it is of the form r = √2 ⋅ r', i.e., r ∈ {0000, 0101,
-- 1010, 1111}.
reducible : Z2 [ω] -> Bool
reducible (Omega a b c d) = (a == c) ∧ (b == d)

-- ----------------------------------------------------------------------
-- * Exact synthesis

-- The fuel for the loops in row-step and row-step-alt.
row-step-fuel : ℕ
row-step-fuel = 16

private
  -- Take a list of (index, residue, value) triples of the given
  -- residue type.
  select-type : ResidueType -> List (Index × Z2 [ω] × ZOmega) -> List (Index × Z2 [ω] × ZOmega)
  select-type t = List.filterᵇ (λ { (_ , a , _) -> residue-type a == t })

  -- zip3 [0..] xs ys.
  zip-idx : {A B : Set} -> ℕ -> List A -> List B -> List (ℕ × A × B)
  zip-idx k (x ∷ xs) (y ∷ ys) = (k , x , y) ∷ zip-idx (suc k) xs ys
  zip-idx _ _ _ = []

  -- findIndices (/= 0).
  nonzero-indices : List ZOmega -> List ℕ
  nonzero-indices w = List.map proj₁ (List.filterᵇ (λ p -> proj₂ p /= 0) (zip-idx' 0 w))
    where
      zip-idx' : ℕ -> List ZOmega -> List (ℕ × ZOmega)
      zip-idx' k [] = []
      zip-idx' k (x ∷ xs) = (k , x) ∷ zip-idx' (suc k) xs

  -- The pairs of a list of even length (odd lengths are invalid
  -- inputs; the last element is then dropped).
  pairs : {A : Set} -> List A -> List (A × A)
  pairs l = proj₁ (list-pairs l)

  lookup0 : List ZOmega -> ℕ -> ZOmega
  lookup0 w j with list-index w j
  ... | just x = x
  ... | nothing = 0

  fromMaybe : {A : Set} -> A -> Maybe A -> A
  fromMaybe a (just x) = x
  fromMaybe a nothing = a

-- Perform a single row operation as in Lemma 4, applied to rows i and
-- j. The entries at rows i and j are x and y, respectively, with
-- respective residues a and b. A precondition is that x and y are of
-- the same residue type. Returns a list of two-level operations that
-- decreases the denominator exponent.
--
-- (Performance: where-bound values are not shared in compiled Agda
-- code, so the intermediate values offs, y' and (x1, y1) are passed
-- as arguments of helper functions, which computes each only once.)
row-step : (Index × Z2 [ω] × ZOmega) × (Index × Z2 [ω] × ZOmega) -> List TwoLevel
row-step = go row-step-fuel
  where
    go : ℕ -> (Index × Z2 [ω] × ZOmega) × (Index × Z2 [ω] × ZOmega) -> List TwoLevel
    go zero _ = []
    go (suc f) ((i , a , x) , (j , b , y)) =
      if reducible a ∧ reducible b then []
      else step (residue-offset b a)
      where
        -- the step for offs = residue-offset b a.
        with-T : ℕ -> ZOmega -> List TwoLevel
        with-T offs y' = TL-T (+ offs) i j ∷ go f ((i , a , x) , (j , residue y' , y'))
        with-H : ZOmega × ZOmega -> List TwoLevel
        with-H (x1 , y1) = TL-H i j ∷ go f ((i , residue x1 , x1) , (j , residue y1 , y1))
        step : ℕ -> List TwoLevel
        step offs =
          if offs /= 0 then with-T offs (omega-power (- (+ offs)) y)
          else with-H (opH-zomega (x , y))

private
  -- The index j of the only non-zero entry of w (0 if there is not
  -- exactly one).
  single-index : List ZOmega -> ℕ
  single-index w with nonzero-indices w
  ... | j ∷ [] = j
  ... | _ = 0

  -- The row operations of one step of reduce-column-aux, given the
  -- (index, residue, value) triples of the column: the row steps for
  -- the pairs of residue type 1010, then those of type 0001.
  row-steps : List (Index × Z2 [ω] × ZOmega) -> List TwoLevel
  row-steps idx-res =
    List.concatMap row-step (pairs (select-type RT-1010 idx-res)) ++
    List.concatMap row-step (pairs (select-type RT-0001 idx-res))

  -- (Intermediate results are passed as arguments of helper
  -- functions, since where-bound values are not shared in compiled
  -- Agda code.)
  reduce-column-aux : Index -> List ZOmega -> ℕ -> List TwoLevel
  reduce-column-aux i w zero = final (single-index w)
    where
      final : ℕ -> List TwoLevel
      final j = m1 ++ TL-omega (+ fromMaybe 0 (log-omega (lookup0 w j))) i ∷ []
        where
          m1 : List TwoLevel
          m1 = if i == j then [] else TL-X i j ∷ []
  reduce-column-aux i w (suc k) = with-gates (row-steps (zip-idx 0 (residue w) w))
    where
      with-gates : List TwoLevel -> List TwoLevel
      with-gates gates =
        gates ++ reduce-column-aux i (List.map reduce-ZOmega (apply-twolevels-zomega (invert-twolevels gates) w)) k

-- Row reduction: Given a unit column vector v, generate a sequence of
-- two-level operators that reduces the ith standard basis vector e_i
-- to v. Any rows that are already 0 in both vectors are guaranteed
-- not to be touched.
reduce-column : {n : ℕ} -> Matrix n One DOmega -> Index -> List TwoLevel
reduce-column v i = reduce-column-aux i (proj₁ wk) (proj₂ wk)
  where
    wk : List ZOmega × ℕ
    wk = denomexp-decompose {List DOmega} {List ZOmega} (list-of-vector (vector-head (unMatrix v)))

-- Input an exact n×n unitary operator with coefficients in 𝔻[ω], and
-- output an equivalent sequence of two-level operators. This is the
-- algorithm from the Giles-Selinger paper. It has superexponential
-- complexity.
--
-- Note: the list of TwoLevel operators will be returned in
-- right-to-left order, i.e., as in the mathematical notation for
-- matrix multiplication. This is the opposite of the quantum circuit
-- notation.
synthesis-nqubit : {n : ℕ} -> Matrix n n DOmega -> List TwoLevel
synthesis-nqubit {n} m = aux n (unMatrix m) 0
  where
    aux : (k : ℕ) -> Vector k (Vector n DOmega) -> Index -> List TwoLevel
    aux zero [] i = []
    aux (suc k) (c ∷ cs) i = with-gates (reduce-column (column-matrix c) i)
      where
        -- (gates is an argument, so that it is computed only once. The
        -- remaining columns are multiplied by the matrix of the
        -- inverted gates, gates-matrix ·*· Matrix' cs in Haskell; we
        -- apply the two-level operators to each column directly, which
        -- gives the same result much faster.)
        with-gates : List TwoLevel -> List TwoLevel
        with-gates gates =
          gates ++ aux k (vector-map (apply-twolevels (invert-twolevels gates)) cs) (suc i)

-- ----------------------------------------------------------------------
-- * Alternative algorithm

-- Section 6 of the Giles-Selinger paper mentions an alternate version
-- of the decomposition algorithm. It requires no ancillas, provided
-- that the determinant of the operator permits this.

-- Symbolic representation of one- and two-level operators, with an
-- alternate set of generators.
--
-- Note: when we use a list of TwoLevelAlt operators to express a
-- sequence of operators, the operators are meant to be applied
-- right-to-left, i.e., as in the mathematical notation for matrix
-- multiplication. This is the opposite of the quantum circuit
-- notation.
data TwoLevelAlt : Set where
  -- iX_{i,j}.
  TL-iX : Index -> Index -> TwoLevelAlt
  -- (T^{-m} (iH) T^m)_{i,j}.
  TL-TiHT : ℤ -> Index -> Index -> TwoLevelAlt
  -- W^m_{i,j}.
  TL-W : ℤ -> Index -> Index -> TwoLevelAlt
  -- (ω_i)^m.
  TL-omega-alt : ℤ -> Index -> TwoLevelAlt

instance
  DecEqTwoLevelAlt : DecEq TwoLevelAlt
  DecEqTwoLevelAlt ._≟_ (TL-iX i j) (TL-iX i' j') = dec2 TL-iX (λ { refl -> refl , refl }) i i' j j'
  DecEqTwoLevelAlt ._≟_ (TL-TiHT k i j) (TL-TiHT k' i' j') with k ≟ k' | i ≟ i' | j ≟ j'
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no p | _ | _ = no λ { refl -> p refl }
  ... | yes _ | no p | _ = no λ { refl -> p refl }
  ... | yes _ | yes _ | no p = no λ { refl -> p refl }
  DecEqTwoLevelAlt ._≟_ (TL-W k i j) (TL-W k' i' j') with k ≟ k' | i ≟ i' | j ≟ j'
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no p | _ | _ = no λ { refl -> p refl }
  ... | yes _ | no p | _ = no λ { refl -> p refl }
  ... | yes _ | yes _ | no p = no λ { refl -> p refl }
  DecEqTwoLevelAlt ._≟_ (TL-omega-alt k i) (TL-omega-alt k' i') = dec2 TL-omega-alt (λ { refl -> refl , refl }) k k' i i'
  DecEqTwoLevelAlt ._≟_ (TL-iX _ _) (TL-TiHT _ _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-iX _ _) (TL-W _ _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-iX _ _) (TL-omega-alt _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-TiHT _ _ _) (TL-iX _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-TiHT _ _ _) (TL-W _ _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-TiHT _ _ _) (TL-omega-alt _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-W _ _ _) (TL-iX _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-W _ _ _) (TL-TiHT _ _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-W _ _ _) (TL-omega-alt _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-omega-alt _ _) (TL-iX _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-omega-alt _ _) (TL-TiHT _ _ _) = no λ ()
  DecEqTwoLevelAlt ._≟_ (TL-omega-alt _ _) (TL-W _ _ _) = no λ ()

  -- Printed as Haskell's derived Show instance, e.g. "TL_W 2 0 1".
  ShowTwoLevelAlt : Show TwoLevelAlt
  ShowTwoLevelAlt .showsPrec d (TL-iX i j) = showParen d 10 ("TL_iX " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevelAlt .showsPrec d (TL-TiHT k i j) = showParen d 10 ("TL_TiHT " String.++ showsPrec 11 k String.++ " " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevelAlt .showsPrec d (TL-W k i j) = showParen d 10 ("TL_W " String.++ showsPrec 11 k String.++ " " String.++ showsPrec 11 i String.++ " " String.++ showsPrec 11 j)
  ShowTwoLevelAlt .showsPrec d (TL-omega-alt k i) = showParen d 10 ("TL_omega_alt " String.++ showsPrec 11 k String.++ " " String.++ showsPrec 11 i)

-- Convert from the alternate generators to the original generators.
twolevels-of-twolevelalts : List TwoLevelAlt -> List TwoLevel
twolevels-of-twolevelalts [] = []
twolevels-of-twolevelalts (TL-iX j l ∷ t) =
  TL-X j l ∷ TL-omega 2 j ∷ TL-omega 2 l ∷ twolevels-of-twolevelalts t
twolevels-of-twolevelalts (TL-TiHT m j l ∷ t) =
  TL-T (- m) j l ∷ TL-H j l ∷ TL-omega 2 j ∷ TL-omega 2 l ∷ TL-T m j l ∷ twolevels-of-twolevelalts t
twolevels-of-twolevelalts (TL-W m j l ∷ t) =
  TL-omega m j ∷ TL-omega (- m) l ∷ twolevels-of-twolevelalts t
twolevels-of-twolevelalts (TL-omega-alt m j ∷ t) =
  TL-omega m j ∷ twolevels-of-twolevelalts t

-- Invert a list of TwoLevelAlt operators, and convert the output to a
-- list of TwoLevel operators.
invert-twolevels-alt : List TwoLevelAlt -> List TwoLevel
invert-twolevels-alt gs = invert-twolevels (twolevels-of-twolevelalts gs)

-- Perform a single row operation as in Lemma 4, applied to rows i and
-- j, using the generators of Section 6. The entries at rows i and j
-- are x and y, respectively, with respective residues a and b. A
-- precondition is that x and y are of the same residue type. Returns
-- a list of two-level operations that decreases the denominator
-- exponent.
row-step-alt : (Index × Z2 [ω] × ZOmega) × (Index × Z2 [ω] × ZOmega) -> List TwoLevelAlt
row-step-alt = go row-step-fuel
  where
    go : ℕ -> (Index × Z2 [ω] × ZOmega) × (Index × Z2 [ω] × ZOmega) -> List TwoLevelAlt
    go zero _ = []
    go (suc f) ((j , a , x) , (l , b , y)) =
      if reducible a ∧ reducible b then []
      else step (residue-offset a b)
      where
        -- (Intermediate values are passed as arguments, since
        -- where-bound values are not shared in compiled code.)
        next : ℕ -> ZOmega -> ZOmega -> List TwoLevelAlt
        next m x1 y1 = TL-TiHT (+ m) j l ∷ go f ((j , residue x1 , x1) , (l , residue y1 , y1))
        with-xy1' : ℕ -> ZOmega × ZOmega -> List TwoLevelAlt
        with-xy1' m (x1 , y1') = next m x1 (omega-power (- (+ m)) y1')
        step : ℕ -> List TwoLevelAlt
        step m = with-xy1' m (opH-zomega (- i * x , - i * omega-power (+ m) y))

private
  -- The row operations of one step of reduce-column-alt-aux (see
  -- row-steps).
  row-steps-alt : List (Index × Z2 [ω] × ZOmega) -> List TwoLevelAlt
  row-steps-alt idx-res =
    List.concatMap row-step-alt (pairs (select-type RT-1010 idx-res)) ++
    List.concatMap row-step-alt (pairs (select-type RT-0001 idx-res))

  -- The first argument is the length n of the column. (Intermediate
  -- results are passed as arguments of helper functions, since
  -- where-bound values are not shared in compiled Agda code.)
  reduce-column-alt-aux : ℕ -> Index -> List ZOmega -> ℕ -> List TwoLevelAlt
  reduce-column-alt-aux n j w zero = final (single-index w)
    where
      final : ℕ -> List TwoLevelAlt
      final l = m1 ++ m2
        where
          wl : ZOmega
          wl = if j == l then lookup0 w j else - i * lookup0 w l
          m1 m2 : List TwoLevelAlt
          m1 = if j == l then [] else TL-iX j l ∷ []
          m2 = if j == n Nat.∸ 1 then TL-omega-alt (+ fromMaybe 0 (log-omega wl)) j ∷ []
               else TL-W (+ fromMaybe 0 (log-omega wl)) j (suc j) ∷ []
  reduce-column-alt-aux n j w (suc k) = with-gates (row-steps-alt (zip-idx 0 (residue w) w))
    where
      with-gates : List TwoLevelAlt -> List TwoLevelAlt
      with-gates gates =
        gates ++ reduce-column-alt-aux n j (List.map reduce-ZOmega (apply-twolevels-zomega (invert-twolevels-alt gates) w)) k

-- Row reduction: Given a unit column vector v, generate a sequence of
-- two-level operators that reduces the ith standard basis vector e_i
-- to v. Any rows that are already 0 in both vectors are guaranteed
-- not to be touched, except possibly row i+1 may be multiplied by a
-- scalar.
reduce-column-alt : {n : ℕ} -> Matrix n One DOmega -> Index -> List TwoLevelAlt
reduce-column-alt {n} v j = reduce-column-alt-aux n j (proj₁ wk) (proj₂ wk)
  where
    wk : List ZOmega × ℕ
    wk = denomexp-decompose {List DOmega} {List ZOmega} (list-of-vector (vector-head (unMatrix v)))

-- Input an exact n×n unitary operator with coefficients in 𝔻[ω], and
-- output an equivalent sequence of two-level operators (in the
-- alternative generators, where all but at most one of the generators
-- has determinant 1). This is the algorithm from the Giles-Selinger
-- paper, Section 6. It has superexponential complexity.
--
-- Note: the list of TwoLevelAlt operators will be returned in
-- right-to-left order, i.e., as in the mathematical notation for
-- matrix multiplication. This is the opposite of the quantum circuit
-- notation.
synthesis-nqubit-alt : {n : ℕ} -> Matrix n n DOmega -> List TwoLevelAlt
synthesis-nqubit-alt {n} m = aux n (unMatrix m) 0
  where
    aux : (k : ℕ) -> Vector k (Vector n DOmega) -> Index -> List TwoLevelAlt
    aux zero [] i = []
    aux (suc k) (c ∷ cs) i = with-gates (reduce-column-alt (column-matrix c) i)
      where
        -- (gates is an argument, so that it is computed only once. As
        -- in synthesis-nqubit, the two-level operators are applied to
        -- the remaining columns directly.)
        with-gates : List TwoLevelAlt -> List TwoLevelAlt
        with-gates gates =
          gates ++ aux k (vector-map (apply-twolevels (invert-twolevels-alt gates)) cs) (suc i)
