-- This module is an Agda port of the module Quantum.Synthesis.CliffordT
-- of the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It provides a representation of the single-qubit Clifford+T
-- operators, Matsumoto-Amano normal forms, and functions for the
-- exact synthesis of single-qubit Clifford+T operators.
--
-- Matsumoto-Amano normal forms and the Matsumoto-Amano exact
-- synthesis algorithm are described in the paper:
--
-- * Ken Matsumoto, Kazuyuki Amano. Representation of Quantum Circuits
--   with Clifford and π/8 Gates. http://arxiv.org/abs/0806.3834.
--
-- Differences from the Haskell version:
--
-- * Haskell raises errors on invalid inputs (non-unitary or
--   non-Clifford matrices, unknown gate characters, ...). Here all
--   functions are total, with documented default results on invalid
--   inputs; on valid inputs, the results are those of Haskell. The
--   decoding functions normalform-unpack and clifford-unpack return a
--   Maybe instead.
--
-- * Since String is not a list of characters in Agda, there are
--   ToGates and FromGates instances for String in addition to those
--   for lists.
--
-- * The (non-structural) recursion in clifford-of-so3 is bounded by a
--   fuel parameter (at most 3 steps are needed for valid inputs).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.CliffordT where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.Clifford
open import Quantum.Synthesis.MultiQubitSynthesis

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- Convert a "rational" value to a "dyadic" value (Haskell:
-- to_dyadic). If the denominator is not a power of 2, return the
-- given default value (Haskell: error).
to-dyadic-or : {A B : Set} {{_ : ToDyadic A B}} -> B -> A -> B
to-dyadic-or d x with maybe-dyadic x
... | just y = y
... | nothing = d

private
  replicate : {A : Set} -> ℕ -> A -> List A
  replicate n x = List.replicate n x

-- ----------------------------------------------------------------------
-- * Clifford+T interchange format

-- It is convenient to have a simple but exact "interchange format"
-- for operators in the single-qubit Clifford+T group. Different
-- operator representations can be converted to and from this format.
--
-- Our format is simply a list of gates from X, Y, Z, H, S, T, and
-- E = H S³ ω³, with the obvious interpretation as a matrix product. We
-- also include the global phase gate W = ω = exp(iπ/4). The W gate is
-- ignored when converting to or from representations that cannot
-- represent global phase (such as the Bloch sphere representation).

-- An enumeration type to represent symbolic basic gates (X, Y, Z, H,
-- S, T, W, E).
--
-- Note: when we use a list of Gates to express a sequence of
-- operators, the operators are meant to be applied right-to-left,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
data Gate : Set where
  X Y Z H S T E W : Gate

private
  gate-code : Gate -> ℕ
  gate-code X = 0
  gate-code Y = 1
  gate-code Z = 2
  gate-code H = 3
  gate-code S = 4
  gate-code T = 5
  gate-code E = 6
  gate-code W = 7

  gate-decode : ℕ -> Gate
  gate-decode 0 = X
  gate-decode 1 = Y
  gate-decode 2 = Z
  gate-decode 3 = H
  gate-decode 4 = S
  gate-decode 5 = T
  gate-decode 6 = E
  gate-decode _ = W

  gate-inv : ∀ g -> gate-decode (gate-code g) ≡ g
  gate-inv X = refl
  gate-inv Y = refl
  gate-inv Z = refl
  gate-inv H = refl
  gate-inv S = refl
  gate-inv T = refl
  gate-inv E = refl
  gate-inv W = refl

  gate-code-inj : ∀ {g h} -> gate-code g ≡ gate-code h -> g ≡ h
  gate-code-inj {g} {h} p = trans (sym (gate-inv g)) (trans (cong gate-decode p) (gate-inv h))

instance
  DecEqGate : DecEq Gate
  DecEqGate ._≟_ g h with gate-code g ≟ gate-code h
  ... | yes p = yes (gate-code-inj p)
  ... | no p = no λ { refl -> p refl }

  ShowGate : Show Gate
  ShowGate .showsPrec _ X = "X"
  ShowGate .showsPrec _ Y = "Y"
  ShowGate .showsPrec _ Z = "Z"
  ShowGate .showsPrec _ H = "H"
  ShowGate .showsPrec _ S = "S"
  ShowGate .showsPrec _ T = "T"
  ShowGate .showsPrec _ E = "E"
  ShowGate .showsPrec _ W = "W"

-- Print a list of gates as Haskell's show does, e.g. "[H,T,H]".
show-gates : List Gate -> String
show-gates = showList showsPrec

-- A type class for all things that can be exactly converted to a
-- list of gates. These are the exact representations of the
-- single-qubit Clifford+T group.
record ToGates (A : Set) : Set where
  field
    -- Convert any suitable thing to a list of gates.
    to-gates : A -> List Gate
open ToGates {{...}} public

private
  -- Gates for characters. Unknown characters are ignored (Haskell:
  -- error).
  gates-of-char : Char -> List Gate
  gates-of-char 'X' = X ∷ []
  gates-of-char 'Y' = Y ∷ []
  gates-of-char 'Z' = Z ∷ []
  gates-of-char 'H' = H ∷ []
  gates-of-char 'S' = S ∷ []
  gates-of-char 'T' = T ∷ []
  gates-of-char 'E' = E ∷ []
  gates-of-char 'W' = W ∷ []
  gates-of-char 'I' = []
  gates-of-char '-' = W ∷ W ∷ W ∷ W ∷ []
  gates-of-char 'i' = W ∷ W ∷ []
  gates-of-char _ = []

instance
  ToGatesGate : ToGates Gate
  ToGatesGate .to-gates x = x ∷ []

  ToGatesList : {A : Set} {{_ : ToGates A}} -> ToGates (List A)
  ToGatesList .to-gates xs = List.concatMap to-gates xs

  ToGatesChar : ToGates Char
  ToGatesChar .to-gates = gates-of-char

  ToGatesString : ToGates String
  ToGatesString .to-gates s = List.concatMap gates-of-char (String.toList s)

  ToGatesAxis : ToGates Axis
  ToGatesAxis .to-gates Axis-I = []
  ToGatesAxis .to-gates Axis-H = H ∷ []
  ToGatesAxis .to-gates Axis-SH = S ∷ H ∷ []

  ToGatesClifford : ToGates Clifford
  ToGatesClifford .to-gates op with clifford-decompose-coset op
  ... | k , b , c , d = to-gates k ++ replicate b X ++ replicate c S ++ replicate d W

-- A type class for all things that a list of gates can be converted
-- to. For example, a list of gates can be converted to an element of
-- U(2) or an element of SO(3), using various (exact or approximate)
-- representations of the matrix entries.
record FromGates (A : Set) : Set where
  field
    -- Convert a list of gates to any suitable type.
    from-gates : List Gate -> A
open FromGates {{...}} public

instance
  FromGatesString : FromGates String
  FromGatesString .from-gates gs = String.concat (List.map show gs)

  FromGatesList : FromGates (List Gate)
  FromGatesList .from-gates gs = gs

-- Invert a gate list.
invert-gates : List Gate -> List Gate
invert-gates gs = aux [] gs
  where
    aux : List Gate -> List Gate -> List Gate
    aux acc [] = acc
    aux acc (X ∷ t) = aux (X ∷ acc) t
    aux acc (Y ∷ t) = aux (Y ∷ acc) t
    aux acc (Z ∷ t) = aux (Z ∷ acc) t
    aux acc (H ∷ t) = aux (H ∷ acc) t
    aux acc (S ∷ t) = aux (Z ∷ S ∷ acc) t
    aux acc (T ∷ t) = aux (Z ∷ S ∷ T ∷ acc) t
    aux acc (E ∷ t) = aux (E ∷ E ∷ acc) t
    aux acc (W ∷ t) = aux (W ∷ W ∷ W ∷ W ∷ W ∷ W ∷ W ∷ acc) t

-- Convert any precise format to any format.
convert : {A B : Set} {{_ : ToGates A}} {{_ : FromGates B}} -> A -> B
convert x = from-gates (to-gates x)

-- ----------------------------------------------------------------------
-- * Matrices in U(2) and SO(3)

-- ----------------------------------------------------------------------
-- ** Matrices in U(2)

module _ {A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  -- The Pauli X operator.
  u2-X : U2 A
  u2-X = matrix2x2 (0 , 1)
                   (1 , 0)

  -- The Pauli Y operator.
  u2-Y : {{_ : ComplexRing A}} -> U2 A
  u2-Y = matrix2x2 (0 , - i)
                   (i , 0)

  -- The Pauli Z operator.
  u2-Z : U2 A
  u2-Z = matrix2x2 (1 , 0)
                   (0 , -1)

  -- The Hadamard operator.
  u2-H : {{_ : RootHalfRing A}} -> U2 A
  u2-H = roothalf * matrix2x2 (1 , 1)
                              (1 , -1)

  -- The S operator.
  u2-S : {{_ : ComplexRing A}} -> U2 A
  u2-S = matrix2x2 (1 , 0)
                   (0 , i)

  -- The T operator.
  u2-T : {{_ : OmegaRing A}} -> U2 A
  u2-T = matrix2x2 (1 , 0)
                   (0 , omega)

  -- The E operator.
  u2-E : {{_ : OmegaRing A}} {{_ : RootHalfRing A}} -> U2 A
  u2-E = roothalf * matrix2x2 (omega ^ 3 , omega)
                              (omega ^ 3 , - omega)

  -- The W = exp(iπ/4) global phase operator.
  u2-W : {{_ : OmegaRing A}} -> U2 A
  u2-W = matrix2x2 (omega , 0)
                   (0 , omega)

  -- Convert a symbolic gate to the corresponding operator.
  u2-of-gate : {{_ : RootHalfRing A}} {{_ : ComplexRing A}} {{_ : OmegaRing A}} -> Gate -> U2 A
  u2-of-gate X = u2-X
  u2-of-gate Y = u2-Y
  u2-of-gate Z = u2-Z
  u2-of-gate H = u2-H
  u2-of-gate S = u2-S
  u2-of-gate T = u2-T
  u2-of-gate E = u2-E
  u2-of-gate W = u2-W

  instance
    FromGatesU2 : {{_ : RootHalfRing A}} {{_ : ComplexRing A}} {{_ : OmegaRing A}} -> FromGates (U2 A)
    FromGatesU2 .from-gates gs = List.foldl _*_ 1 (List.map u2-of-gate gs)

-- ----------------------------------------------------------------------
-- ** Matrices in SO(3)

-- This is the Bloch sphere representation of single qubit operators.

module _ {A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  -- The Pauli X operator.
  so3-X : SO3 A
  so3-X = matrix3x3 (1 , 0 , 0)
                    (0 , -1 , 0)
                    (0 , 0 , -1)

  -- The Pauli Y operator.
  so3-Y : SO3 A
  so3-Y = matrix3x3 (-1 , 0 , 0)
                    (0 , 1 , 0)
                    (0 , 0 , -1)

  -- The Pauli Z operator.
  so3-Z : SO3 A
  so3-Z = matrix3x3 (-1 , 0 , 0)
                    (0 , -1 , 0)
                    (0 , 0 , 1)

  -- The Hadamard operator.
  so3-H : SO3 A
  so3-H = matrix3x3 (0 , 0 , 1)
                    (0 , -1 , 0)
                    (1 , 0 , 0)

  -- The operator S.
  so3-S : SO3 A
  so3-S = matrix3x3 (0 , -1 , 0)
                    (1 , 0 , 0)
                    (0 , 0 , 1)

  -- The operator E.
  so3-E : SO3 A
  so3-E = matrix3x3 (0 , 0 , 1)
                    (1 , 0 , 0)
                    (0 , 1 , 0)

  -- The T operator.
  so3-T : {{_ : RootHalfRing A}} -> SO3 A
  so3-T = matrix3x3 (r , - r , 0)
                    (r , r , 0)
                    (0 , 0 , 1)
    where r = roothalf

  -- Convert a symbolic gate to the corresponding Bloch sphere
  -- operator.
  so3-of-gate : {{_ : RootHalfRing A}} -> Gate -> SO3 A
  so3-of-gate X = so3-X
  so3-of-gate Y = so3-Y
  so3-of-gate Z = so3-Z
  so3-of-gate H = so3-H
  so3-of-gate S = so3-S
  so3-of-gate T = so3-T
  so3-of-gate E = so3-E
  so3-of-gate W = 1

  instance
    FromGatesSO3 : {{_ : RootHalfRing A}} -> FromGates (SO3 A)
    FromGatesSO3 .from-gates gs = List.foldl _*_ 1 (List.map so3-of-gate gs)

-- ----------------------------------------------------------------------
-- ** Conversions

-- Conversion from U(2) to SO(3).
so3-of-u2 : {A B : Set} {{_ : Ring A}} {{_ : Adjoint A}} {{_ : ComplexRing A}} {{_ : RealPart A B}}
            {{_ : Ring B}} {{_ : HalfRing B}} -> U2 A -> SO3 B
so3-of-u2 {A} u = matrix-of-function f
  where
    sigma : ℕ -> U2 A
    sigma 0 = u2-X
    sigma 1 = u2-Y
    sigma _ = u2-Z
    f = λ i j -> half * real (tr (sigma i * u * sigma j * adj u))

-- Convert a Clifford operator to a matrix in SO(3).
so3-of-clifford : {A B : Set} {{_ : ToClifford A}} {{_ : Ring B}} -> A -> SO3 B
so3-of-clifford m with clifford-decompose m
... | a , b , c , d = so3-E ^ a * so3-X ^ b * so3-S ^ c

-- Fuel for clifford-of-so3.
clifford-of-so3-fuel : ℕ
clifford-of-so3-fuel = 8

-- Convert a matrix in SO(3) to a Clifford gate. If the matrix isn't
-- Clifford, the result is unspecified (Haskell: error).
clifford-of-so3 : {A : Set} {{_ : Ring A}} {{_ : DecEq A}} {{_ : Adjoint A}} -> SO3 A -> Clifford
clifford-of-so3 {A} = go clifford-of-so3-fuel
  where
    open LiteralsFor A

    v3 : A -> A -> A -> Vec A 3
    v3 a b c = a ∷ b ∷ c ∷ []

    go : ℕ -> SO3 A -> Clifford
    go zero m = clifford-id
    go (suc f) m@(Matrix' (c0 ∷ c1 ∷ c2 ∷ [])) =
      if c2 == v3 1 0 0 then with' "H"
      else if c2 == v3 -1 0 0 then with' "HX"
      else if c2 == v3 0 1 0 then with' "SH"
      else if c2 == v3 0 -1 0 then with' "SHX"
      else if c2 == v3 0 0 -1 then with' "X"
      else if c1 == v3 -1 0 0 then with' "S"
      else if c1 == v3 0 -1 0 then with' "SS"
      else if c1 == v3 1 0 0 then with' "SSS"
      else clifford-id
      where
        with' : String -> Clifford
        with' s = clifford-mult op (go f (adj (so3-of-clifford op) * m))
          where op = to-clifford s

instance
  ToCliffordSO3 : {A : Set} {{_ : Ring A}} {{_ : DecEq A}} {{_ : Adjoint A}} -> ToClifford (SO3 A)
  ToCliffordSO3 .to-clifford = clifford-of-so3

-- ----------------------------------------------------------------------
-- * Matsumoto-Amano normal forms

-- A Matsumoto-Amano normal form is a sequence of Clifford+T operators
-- that is of the form
--
-- * (ε | T) (HT | SHT)* C.
--
-- Here, ε is the empty sequence, C is any Clifford operator, and the
-- meanings of "|" and "*" are as for regular expressions. Every
-- single-qubit Clifford+T operator has a unique Matsumoto-Amano
-- normal form.

-- ----------------------------------------------------------------------
-- ** Representation of normal forms

-- Syllables is a circuit of the form (ε|T) (HT|SHT)*.
data Syllables : Set where
  -- The empty sequence ε.
  S-I : Syllables
  -- The sequence T.
  S-T : Syllables
  -- A sequence of the form …HT.
  SApp-HT : Syllables -> Syllables
  -- A sequence of the form …SHT.
  SApp-SHT : Syllables -> Syllables

-- A representation of normal forms, optimized for right
-- multiplication. (Haskell: constructor NormalForm.)
record NormalForm : Set where
  constructor NormalForm'
  field
    nf-syllables : Syllables
    nf-clifford : Clifford

private
  decEqSyllables : (x y : Syllables) -> Relation.Nullary.Dec (x ≡ y)
  decEqSyllables S-I S-I = yes refl
  decEqSyllables S-T S-T = yes refl
  decEqSyllables (SApp-HT x) (SApp-HT y) with decEqSyllables x y
  ... | yes refl = yes refl
  ... | no p = no λ { refl -> p refl }
  decEqSyllables (SApp-SHT x) (SApp-SHT y) with decEqSyllables x y
  ... | yes refl = yes refl
  ... | no p = no λ { refl -> p refl }
  decEqSyllables S-I S-T = no λ ()
  decEqSyllables S-I (SApp-HT _) = no λ ()
  decEqSyllables S-I (SApp-SHT _) = no λ ()
  decEqSyllables S-T S-I = no λ ()
  decEqSyllables S-T (SApp-HT _) = no λ ()
  decEqSyllables S-T (SApp-SHT _) = no λ ()
  decEqSyllables (SApp-HT _) S-I = no λ ()
  decEqSyllables (SApp-HT _) S-T = no λ ()
  decEqSyllables (SApp-HT _) (SApp-SHT _) = no λ ()
  decEqSyllables (SApp-SHT _) S-I = no λ ()
  decEqSyllables (SApp-SHT _) S-T = no λ ()
  decEqSyllables (SApp-SHT _) (SApp-HT _) = no λ ()

  showsPrec-Syllables : ℕ -> Syllables -> String
  showsPrec-Syllables d S-I = "S_I"
  showsPrec-Syllables d S-T = "S_T"
  showsPrec-Syllables d (SApp-HT s) = showParen d 10 ("SApp_HT " String.++ showsPrec-Syllables 11 s)
  showsPrec-Syllables d (SApp-SHT s) = showParen d 10 ("SApp_SHT " String.++ showsPrec-Syllables 11 s)

  -- (Haskell: to_gates (SApp_HT ts) = to_gates ts ++ [H,T], etc.; we
  -- use an accumulator, gates-acc ts acc = gates-of-syllables ts ++
  -- acc, to avoid the quadratic cost of the left-nested appends.)
  gates-acc : Syllables -> List Gate -> List Gate
  gates-acc S-I acc = acc
  gates-acc S-T acc = T ∷ acc
  gates-acc (SApp-HT ts) acc = gates-acc ts (H ∷ T ∷ acc)
  gates-acc (SApp-SHT ts) acc = gates-acc ts (S ∷ H ∷ T ∷ acc)

  gates-of-syllables : Syllables -> List Gate
  gates-of-syllables ts = gates-acc ts []

instance
  DecEqSyllables : DecEq Syllables
  DecEqSyllables ._≟_ = decEqSyllables

  ShowSyllables : Show Syllables
  ShowSyllables .showsPrec = showsPrec-Syllables

  DecEqNormalForm : DecEq NormalForm
  DecEqNormalForm ._≟_ (NormalForm' s c) (NormalForm' s' c') with s ≟ s' | c ≟ c'
  ... | yes refl | yes refl = yes refl
  ... | no p | _ = no λ { refl -> p refl }
  ... | yes _ | no p = no λ { refl -> p refl }

  ToGatesSyllables : ToGates Syllables
  ToGatesSyllables .to-gates = gates-of-syllables

  ToGatesNormalForm : ToGates NormalForm
  ToGatesNormalForm .to-gates (NormalForm' ts c) = to-gates ts ++ to-gates c

  ShowNormalForm : Show NormalForm
  ShowNormalForm .showsPrec _ x with to-gates x
  ... | [] = "I"
  ... | gs@(_ ∷ _) = String.concat (List.map show gs)

private
  -- The Clifford operators HS and SHS, as top-level constants (so
  -- that in compiled code the strings are parsed only once, not for
  -- every T gate).
  clifford-HS clifford-SHS : Clifford
  clifford-HS = to-clifford "HS"
  clifford-SHS = to-clifford "SHS"

-- Right-multiply the given normal form by a gate.
normalform-append : NormalForm -> Gate -> NormalForm
normalform-append (NormalForm' ts c) X = NormalForm' ts (clifford-mult c clifford-X)
normalform-append (NormalForm' ts c) Y = NormalForm' ts (clifford-mult c clifford-Y)
normalform-append (NormalForm' ts c) Z = NormalForm' ts (clifford-mult c clifford-Z)
normalform-append (NormalForm' ts c) H = NormalForm' ts (clifford-mult c clifford-H)
normalform-append (NormalForm' ts c) S = NormalForm' ts (clifford-mult c clifford-S)
normalform-append (NormalForm' ts c) E = NormalForm' ts (clifford-mult c clifford-E)
normalform-append (NormalForm' ts c) W = NormalForm' ts (clifford-mult c clifford-W)
normalform-append (NormalForm' ts c) T with clifford-tconj c
... | Axis-H , c' = NormalForm' (SApp-HT ts) c'
... | Axis-SH , c' = NormalForm' (SApp-SHT ts) c'
... | Axis-I , c' = aux ts
  where
    aux : Syllables -> NormalForm
    aux S-I = NormalForm' S-T c'
    aux S-T = NormalForm' S-I (clifford-mult clifford-S c')
    aux (SApp-HT ts') = NormalForm' ts' (clifford-mult clifford-HS c')
    aux (SApp-SHT ts') = NormalForm' ts' (clifford-mult clifford-SHS c')

-- ----------------------------------------------------------------------
-- ** Group operations on normal forms

-- The identity as a normal form.
nf-id : NormalForm
nf-id = NormalForm' S-I clifford-id

-- Multiply two normal forms. The right factor can be any ToGates.
nf-mult : {B : Set} {{_ : ToGates B}} -> NormalForm -> B -> NormalForm
nf-mult a b = List.foldl normalform-append a (to-gates b)

-- ----------------------------------------------------------------------
-- ** Conversion to normal form

-- Convert any ToGates list to a NormalForm, thereby normalizing it.
normalize : {A : Set} {{_ : ToGates A}} -> A -> NormalForm
normalize = nf-mult nf-id

instance
  FromGatesNormalForm : FromGates NormalForm
  FromGatesNormalForm .from-gates = normalize

-- Invert a normal form. The input can be any ToGates.
nf-inv : {A : Set} {{_ : ToGates A}} -> A -> NormalForm
nf-inv x = from-gates (invert-gates (to-gates x))

-- ----------------------------------------------------------------------
-- * Exact synthesis

-- ----------------------------------------------------------------------
-- ** Synthesis from SO(3)

-- Input an exact matrix in SO(3), and output the corresponding
-- Clifford+T normal form. If the given matrix is not an element of
-- SO(3), i.e., orthogonal with determinant 1, the result is
-- unspecified (Haskell: error).
--
-- This implementation uses the Matsumoto-Amano algorithm.
--
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
synthesis-bloch : SO3 DRootTwo -> List Gate
synthesis-bloch m = aux (proj₁ mk) (proj₂ mk)
  where
    mk : SO3 ZRootTwo × ℕ
    mk = denomexp-decompose {SO3 DRootTwo} {SO3 ZRootTwo} m

    sqrt2T : SO3 ZRootTwo
    sqrt2T = matrix3x3 (1 , -1 , 0) (1 , 1 , 0) (0 , 0 , roottwo)

    -- Divide a ZRootTwo of the form 2a + 2b√2 by 2 (for other
    -- inputs, the coefficients are rounded down; Haskell: error).
    half-ZRootTwo : ZRootTwo -> ZRootTwo
    half-ZRootTwo (RootTwo a b) = RootTwo (a / 2) (b / 2)

    -- The axis for a residue pattern (Haskell: error for other
    -- patterns).
    axis-of : List Z2 -> Axis
    axis-of (Odd ∷ Odd ∷ Even ∷ []) = Axis-I
    axis-of (Even ∷ Odd ∷ Odd ∷ []) = Axis-H
    axis-of (Odd ∷ Even ∷ Odd ∷ []) = Axis-SH
    axis-of _ = Axis-I

    aux : SO3 ZRootTwo -> ℕ -> List Gate
    aux m zero = to-gates (clifford-of-so3 m)
    aux m (suc k) = to-gates axis ++ T ∷ aux m4 k
      where
        p : Vec (Vec Z2 3) 3
        p = unMatrix (matrix-map parity m)
        v : List Z2
        v = list-of-vector (vector-zipwith (λ x y -> x + y - x * y) (vector-head p) (vector-head (vector-tail p)))
        axis : Axis
        axis = axis-of v
        m4 : SO3 ZRootTwo
        m4 = matrix-map half-ZRootTwo (adj sqrt2T * (adj (so3-of-clifford axis) * m))

instance
  -- (If the entries are not real, the imaginary parts are ignored; if
  -- they are not dyadic, they are replaced by 0; Haskell: error.)
  ToGatesSO3 : {A : Set} {{_ : ToQOmega A}} -> ToGates (SO3 A)
  ToGatesSO3 .to-gates m = synthesis-bloch (matrix-map (λ x -> to-dyadic-or 0 (to-real (toQOmega x))) m)
    where
      to-real : QOmega -> QRootTwo
      to-real x = real x

-- ----------------------------------------------------------------------
-- ** Synthesis from U(2)

private
  -- Gates for (T_{0,1})^k, where k is taken modulo 8.
  gates-of-tpower : ℕ -> List Gate
  gates-of-tpower 0 = []
  gates-of-tpower 1 = T ∷ []
  gates-of-tpower 2 = S ∷ []
  gates-of-tpower 3 = T ∷ S ∷ []
  gates-of-tpower 4 = Z ∷ []
  gates-of-tpower 5 = T ∷ Z ∷ []
  gates-of-tpower 6 = S ∷ Z ∷ []
  gates-of-tpower 7 = T ∷ S ∷ Z ∷ []
  gates-of-tpower _ = []

instance
  -- Only two-level operators on indices 0 and 1 are valid; other
  -- operators are converted to the empty list (Haskell: error).
  ToGatesTwoLevel : ToGates TwoLevel
  ToGatesTwoLevel .to-gates (TL-X 0 1) = X ∷ []
  ToGatesTwoLevel .to-gates (TL-X 1 0) = X ∷ []
  ToGatesTwoLevel .to-gates (TL-H 0 1) = H ∷ []
  ToGatesTwoLevel .to-gates (TL-H 1 0) = X ∷ H ∷ X ∷ []
  ToGatesTwoLevel .to-gates (TL-T k 0 1) = gates-of-tpower (mod8 k)
  ToGatesTwoLevel .to-gates (TL-T k 1 0) = X ∷ gates-of-tpower (mod8 k) ++ X ∷ []
  ToGatesTwoLevel .to-gates (TL-omega k 1) = gates-of-tpower (mod8 k)
  ToGatesTwoLevel .to-gates (TL-omega k 0) = X ∷ gates-of-tpower (mod8 k) ++ X ∷ []
  ToGatesTwoLevel .to-gates _ = []

-- Input an exact matrix in U(2), and output the corresponding
-- Clifford+T normal form. The behavior is undefined if the given
-- matrix is not an element of U(2), i.e., unitary.
--
-- We use a variant of the Kliuchnikov-Maslov-Mosca algorithm, as
-- implemented in Quantum.Synthesis.MultiQubitSynthesis.
--
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
synthesis-u2 : U2 DOmega -> List Gate
synthesis-u2 m = to-gates (normalize (synthesis-nqubit m))

instance
  -- (Entries that are not dyadic are replaced by 0; Haskell: error.)
  ToGatesU2 : {A : Set} {{_ : ToQOmega A}} -> ToGates (U2 A)
  ToGatesU2 .to-gates m = synthesis-u2 (matrix-map (λ x -> fromDOmega {DOmega} (to-dyadic-or 0 (toQOmega x))) m)

-- ----------------------------------------------------------------------
-- * Compact representation of normal forms

-- It is sometimes useful to store Clifford+T operators in a file; for
-- this purpose, we provide a very succinct encoding of Clifford+T
-- operators as bit strings, which are in turns represented as
-- integers.
--
-- Our bitwise encoding is as follows. The first regular expression
-- represents the set of Matsumoto-Amano normal forms (with a
-- particular presentation of the rightmost Clifford operator). The
-- second regular expression, which has the same form, defines the
-- corresponding bit string encoding.
--
-- * (ε|T) (HT|SHT)* (ε|H|SH) (ε|X) (ε|S²) (ε|S) (ε|ω⁴) (ε|ω²) (ε|ω)
--
-- * (10|11) (0|1)* (00|01|10) (0|1) (0|1) (0|1) (0|1) (0|1) (0|1)
--
-- As a special case, the leading bits 10 are omitted in case the
-- encoded operator is a Clifford operator. This ensures that the
-- encoding of a Clifford operator is an integer from 0 to 191.
--
-- See the Haskell documentation for the hexadecimal decoding table.
-- For example, the hexadecimal integer 6bf723e31 encodes the
-- Clifford+T operator
--
--   THT SHTHTSHTSHT SHTSHTSHTSHT HTSHTSHTSHT HTHTSHTHT HTHTSHTSHT SHTSHTSHTHT XSS ω.

-- Encode a Clifford operator as an integer in the range 0−191.
clifford-pack : Clifford -> ℤ
clifford-pack op with clifford-decompose-coset op
... | k , b , c , d = + (64 Nat.* encode k Nat.+ 32 Nat.* b Nat.+ 8 Nat.* c Nat.+ d)
  where
    encode : Axis -> ℕ
    encode Axis-I = 0
    encode Axis-H = 1
    encode Axis-SH = 2

-- Compactly encode a NormalForm as an integer.
normalform-pack : NormalForm -> ℤ
normalform-pack (NormalForm' S-I op) = clifford-pack op
normalform-pack (NormalForm' s op) = + (256 Nat.* syllables-pack s) + clifford-pack op
  where
    syllables-pack : Syllables -> ℕ
    syllables-pack S-I = 2
    syllables-pack S-T = 3
    syllables-pack (SApp-HT s) = 2 Nat.* syllables-pack s
    syllables-pack (SApp-SHT s) = 2 Nat.* syllables-pack s Nat.+ 1

-- Decode a Clifford operator from its integer encoding. This is the
-- inverse of clifford-pack. Return nothing if the input is not in the
-- range 0−191 (Haskell: error).
clifford-unpack : ℤ -> Maybe Clifford
clifford-unpack -[1+ _ ] = nothing
clifford-unpack (+ n) =
  if 191 Nat.<ᵇ n then nothing
  else just (decode k ⊙ (clifford-X ^' b) ⊙ (clifford-S ^' c) ⊙ (clifford-W ^' d))
  where
    d = n % 8
    c = (n / 8) % 4
    b = (n / 32) % 2
    k = (n / 64) % 4

    decode : ℕ -> Clifford
    decode 0 = clifford-id
    decode 1 = clifford-H
    decode _ = clifford-SH

    infixl 7 _⊙_
    _⊙_ : Clifford -> Clifford -> Clifford
    _⊙_ = clifford-mult

    _^'_ : Clifford -> ℕ -> Clifford
    x ^' n = List.foldl _⊙_ clifford-id (List.replicate n x)

-- Decode a NormalForm from its integer encoding. This is the inverse
-- of normalform-pack. Return nothing if the input is not a valid
-- encoding (Haskell: error).
normalform-unpack : ℤ -> Maybe NormalForm
normalform-unpack -[1+ _ ] = nothing
normalform-unpack (+ n) =
  if n Nat.<ᵇ 192 then (clifford-unpack (+ n) >>= λ op -> just (NormalForm' S-I op))
  else if n Nat.<ᵇ 768 then nothing
  else (syllables-unpack (n / 256) (n / 256) >>= λ s ->
        clifford-unpack (+ (n % 256)) >>= λ op -> just (NormalForm' s op))
  where
    _>>=_ : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
    just x >>= f = f x
    nothing >>= f = nothing

    -- The first argument is fuel (the number of bits suffices).
    syllables-unpack : ℕ -> ℕ -> Maybe Syllables
    syllables-unpack _ 0 = nothing
    syllables-unpack _ 1 = nothing
    syllables-unpack _ 2 = just S-I
    syllables-unpack _ 3 = just S-T
    syllables-unpack zero _ = nothing
    syllables-unpack (suc f) m =
      syllables-unpack f (m / 2) >>= λ s ->
      just (if m % 2 == 0 then SApp-HT s else SApp-SHT s)

instance
  -- Invalid encodings are converted to the empty list (Haskell:
  -- error).
  ToGatesℤ : ToGates ℤ
  ToGatesℤ .to-gates n with normalform-unpack n
  ... | just nf = to-gates nf
  ... | nothing = []

  FromGatesℤ : FromGates ℤ
  FromGatesℤ .from-gates gs = normalform-pack (from-gates gs)
