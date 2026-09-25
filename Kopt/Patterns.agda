-- Section IV A and the refinements of Section IV B of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the six patterns of Lemma IV.1, the function lemma-six that brings
-- an operator into one of them by permutations, and the refinement
-- functions of Sections IV B 1-6, which bring the (2,l)-residue of an
-- operator into the normal form used by the transition of Lemma IV.4.
--
-- This is a port of the authors' Haskell module Kopt.hs (lemma_six,
-- cof, refine_ii, refine_iii, refine_iv, refine_ivt, refine_v,
-- refine_vi, refine, and the normal forms pii2, piii2, case_iv_2,
-- pv2, pvi2, ...). Two things are computed differently, for speed;
-- both give exactly the same results, because ρₙ : ℤ[i] → ℤ[i]/(γⁿ)
-- is a ring homomorphism and permutation matrices have entries 0 and
-- 1 only:
--
--  * lemma_six searches all 24·24·7 combinations of a left
--    permutation L, a right permutation R and a pattern p for one
--    with ρˡ₁(L·A·R) = p. We compute the 4×4 matrix ρˡ₁(A) over ℤ₂
--    once, and then obtain ρˡ₁(L·A·R) by permuting its rows and
--    columns. The search order is the authors' one, so the L, R and p
--    found are the same.
--
--  * likewise the refinements use ρˡ₂(L·A·R), which we get from
--    ρˡ₂(A) by permuting rows and columns rather than by multiplying
--    4×4 matrices over 𝔻[i].
--
-- Partiality: the authors' functions raise errors on inputs that are
-- not two-qubit Clifford+CS operators (lemma_six: no pattern found;
-- refine_xx: wrong pattern). Here lemma-six returns a Maybe, and the
-- refinement functions return the pair of empty circuits.

{-# OPTIONS --without-K --safe #-}

module Kopt.Patterns where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base using (String)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations

-- ----------------------------------------------------------------------
-- * The six patterns (Lemma IV.1)

-- The seven cases of Lemma IV.1: the six patterns (i)-(vi), plus the
-- transpose of (iv). (The transpose of (v) is (v) again, up to row
-- and column permutations, and the other patterns are symmetric.)
data SixCases : Set where
  I II III IV IVt V VI : SixCases

-- The order in which the authors' lemma_six tries the seven cases.
six-cases : List SixCases
six-cases = I ∷ II ∷ III ∷ IV ∷ V ∷ VI ∷ IVt ∷ []

-- The pattern matrices of Lemma IV.1, as 4×4 matrices over ℤ₂:
--
--   (i)   the identity,
--   (ii)  a 2×2 block of 1s in the top left corner,
--   (iii) two diagonal 2×2 blocks of 1s,
--   (iv)  the two top rows all 1s,
--   (iv)ᵀ the two left columns all 1s,
--   (v)   (ii) together with the bottom half all 1s,
--   (vi)  all 1s.
pattern-matrix : SixCases -> Matrix 4 4 Z2
pattern-matrix I =
  matrix4x4 (Odd  , Even , Even , Even)
            (Even , Odd  , Even , Even)
            (Even , Even , Odd  , Even)
            (Even , Even , Even , Odd)
pattern-matrix II =
  matrix4x4 (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
            (Even , Even , Even , Even)
            (Even , Even , Even , Even)
pattern-matrix III =
  matrix4x4 (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
            (Even , Even , Odd  , Odd)
            (Even , Even , Odd  , Odd)
pattern-matrix IV =
  matrix4x4 (Odd  , Odd  , Odd  , Odd)
            (Odd  , Odd  , Odd  , Odd)
            (Even , Even , Even , Even)
            (Even , Even , Even , Even)
pattern-matrix IVt =
  matrix4x4 (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
pattern-matrix V =
  matrix4x4 (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Even , Even)
            (Odd  , Odd  , Odd  , Odd)
            (Odd  , Odd  , Odd  , Odd)
pattern-matrix VI =
  matrix4x4 (Odd , Odd , Odd , Odd)
            (Odd , Odd , Odd , Odd)
            (Odd , Odd , Odd , Odd)
            (Odd , Odd , Odd , Odd)

-- ----------------------------------------------------------------------
-- ** Decidable equality and printing

private
  case-code : SixCases -> ℕ
  case-code I = 0
  case-code II = 1
  case-code III = 2
  case-code IV = 3
  case-code IVt = 4
  case-code V = 5
  case-code VI = 6

  case-decode : ℕ -> SixCases
  case-decode 0 = I
  case-decode 1 = II
  case-decode 2 = III
  case-decode 3 = IV
  case-decode 4 = IVt
  case-decode 5 = V
  case-decode _ = VI

  case-decode-code : (p : SixCases) -> case-decode (case-code p) ≡ p
  case-decode-code I = refl
  case-decode-code II = refl
  case-decode-code III = refl
  case-decode-code IV = refl
  case-decode-code IVt = refl
  case-decode-code V = refl
  case-decode-code VI = refl

case-≟ : DecidableEquality SixCases
case-≟ p q with case-code p ≟ case-code q
... | yes e = yes (trans (sym (case-decode-code p)) (trans (cong case-decode e) (case-decode-code q)))
... | no ¬e = no λ { refl -> ¬e refl }

-- The cases are printed as in the authors' Haskell code (a derived
-- Show instance): "I", "II", ..., "IVt".
show-case : SixCases -> String
show-case I = "I"
show-case II = "II"
show-case III = "III"
show-case IV = "IV"
show-case IVt = "IVt"
show-case V = "V"
show-case VI = "VI"

instance
  DecEqSixCases : DecEq SixCases
  DecEqSixCases ._≟_ = case-≟

  ShowSixCases : Show SixCases
  ShowSixCases .showsPrec _ = show-case

-- ----------------------------------------------------------------------
-- * Small helpers on 4-vectors and 4×4 matrices

-- The jth entry of a 4-vector (total: out-of-range indices give the
-- last entry).
vsel4 : {A : Set} -> Vector 4 A -> ℕ -> A
vsel4 (a ∷ b ∷ c ∷ d ∷ []) 0 = a
vsel4 (a ∷ b ∷ c ∷ d ∷ []) 1 = b
vsel4 (a ∷ b ∷ c ∷ d ∷ []) 2 = c
vsel4 (a ∷ b ∷ c ∷ d ∷ []) _ = d

-- The rows of a 4×4-matrix (the framework stores the columns).
rows-4 : {A : Set} -> Matrix 4 4 A -> Vector 4 (Vector 4 A)
rows-4 (Matrix' cs) = vector-transpose cs

-- The entry in row i and column j of a 4×4-matrix (total; the
-- authors' matrix_index, which raises an error out of range).
index-4 : {A : Set} -> Matrix 4 4 A -> ℕ -> ℕ -> A
index-4 (Matrix' cs) i j = vsel4 (vsel4 cs j) i

-- ----------------------------------------------------------------------
-- * Arithmetic in ℤ[i]/(γ²) (Section II B)

-- A residue modulo γ², written b₀b₁. Addition is bitwise xor, 10 is
-- the unit, 00 is zero, multiplication by 01 is a right shift, and
-- 11·b₀b₁ = b₀(b₁⊕b₀). This is the authors' "instance Num [Z2]".
R2 : Set
R2 = Residue 2

r2-zero r2-one r2-i r2-shift : R2
r2-zero = Even ∷ Even ∷ []   -- 00, zero
r2-one = Odd ∷ Even ∷ []     -- 10, one, ρ₂(±1)
r2-i = Odd ∷ Odd ∷ []        -- 11, ρ₂(±i)
r2-shift = Even ∷ Odd ∷ []   -- 01, ρ₂(γ)

infixl 6 _r2+_
infixl 7 _r2*_

_r2+_ : R2 -> R2 -> R2
(a ∷ b ∷ []) r2+ (c ∷ d ∷ []) = (a + c) ∷ (b + d) ∷ []

_r2*_ : R2 -> R2 -> R2
(Odd ∷ Even ∷ []) r2* y = y
(Odd ∷ Odd ∷ []) r2* (y₁ ∷ y₂ ∷ []) = y₁ ∷ (y₂ + y₁) ∷ []
(Even ∷ Odd ∷ []) r2* (y₁ ∷ y₂ ∷ []) = Even ∷ y₁ ∷ []
(Even ∷ Even ∷ []) r2* y = r2-zero

private
  r2-scale : R2 -> Vector 4 R2 -> Vector 4 R2
  r2-scale x v = vector-map (x r2*_) v

  r2-vadd : Vector 4 R2 -> Vector 4 R2 -> Vector 4 R2
  r2-vadd = vector-zipwith _r2+_

  r2-mmv : Vector 4 (Vector 4 R2) -> Vector 4 R2 -> Vector 4 R2
  r2-mmv (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) =
    r2-vadd (r2-vadd (r2-scale b₀ a₀) (r2-scale b₁ a₁))
            (r2-vadd (r2-scale b₂ a₂) (r2-scale b₃ a₃))

-- Multiplication of 4×4-matrices over ℤ[i]/(γ²).
infixl 7 _r2∙_
_r2∙_ : Matrix 4 4 R2 -> Matrix 4 4 R2 -> Matrix 4 4 R2
(Matrix' a) r2∙ (Matrix' b) = Matrix' (vector-map (r2-mmv a) b)

-- The (2,0)-residue of an integral matrix over 𝔻[i], i.e. the
-- authors' rho 0 2.
r2-of : Matrix 4 4 DComplex -> Matrix 4 4 R2
r2-of m = matrix-map (ρ 2) (to-whole m)

-- The (2,0)-residue of the operator of a circuit of lde 0.
r2-of-circuit : Circuit -> Matrix 4 4 R2
r2-of-circuit c = r2-of ⟦ c ⟧

-- ----------------------------------------------------------------------
-- * Residues of the current operator

private
  scale-to-whole : DComplex -> DComplex -> ZComplex
  scale-to-whole g x = to-whole (x * g)

-- γˡ·A, as a matrix over ℤ[i]. This is to-whole (lde-factor A l) of
-- Kopt.Base, but γˡ is computed once instead of once per entry.
integral-matrix : ℕ -> Matrix 4 4 DComplex -> Matrix 4 4 ZComplex
integral-matrix l m = matrix-map (scale-to-whole (γ ^ l)) m

-- ρˡ₁(A) and ρˡ₂(A) from γˡ·A.
rho1-of : Matrix 4 4 ZComplex -> Matrix 4 4 Z2
rho1-of = matrix-map parityℤ[i]

rho2-of : Matrix 4 4 ZComplex -> Matrix 4 4 R2
rho2-of = matrix-map (ρ 2)

-- ----------------------------------------------------------------------
-- * Permuting rows and columns
--
-- ρₙ is a ring homomorphism and the entries of a permutation matrix
-- are 0 and 1, so ρₙ(P_x·M·P_y) = P_x·ρₙ(M)·P_y, and the latter is
-- the matrix N with N[i][j] = ρₙ(M)[x⁻¹(i)][y(j)].

-- Reorder a 4-vector along a 4-tuple: select4 σ v = (v_{σ0},…,v_{σ3}).
select4 : {A : Set} -> Tuple4 -> Vector 4 A -> Vector 4 A
select4 s c = vsel4 c (sel s 0) ∷ vsel4 c (sel s 1) ∷ vsel4 c (sel s 2) ∷ vsel4 c (sel s 3) ∷ []

private
  permute-aux : {A : Set} -> Tuple4 -> Tuple4 -> Vector 4 (Vector 4 A) -> Matrix 4 4 A
  permute-aux xi y cs =
      Matrix' ( select4 xi (vsel4 cs (sel y 0))
              ∷ select4 xi (vsel4 cs (sel y 1))
              ∷ select4 xi (vsel4 cs (sel y 2))
              ∷ select4 xi (vsel4 cs (sel y 3)) ∷ [])

-- P_x · M · P_y, for permutation matrices P_x and P_y.
permute-matrix : {A : Set} -> Tuple4 -> Tuple4 -> Matrix 4 4 A -> Matrix 4 4 A
permute-matrix x y (Matrix' cs) = permute-aux (perm-inverse x) y cs

-- ----------------------------------------------------------------------
-- * Lemma IV.1: the search for the permutations and the pattern
--
-- A 4×4 matrix over ℤ₂ is encoded as a natural number < 2¹⁶: each row
-- becomes a 4-bit number (bit j is the entry in column j), and the
-- four rows are packed into a 16-bit number. Comparing a candidate
-- with the seven patterns is then a comparison of two numbers.

private
  z2-bit : Z2 -> ℕ
  z2-bit Even = 0
  z2-bit Odd = 1

  -- A row, encoded as a 4-bit number.
  encode-row : Vector 4 Z2 -> ℕ
  encode-row (a ∷ b ∷ c ∷ d ∷ []) =
    z2-bit a Nat.+ z2-bit b Nat.* 2 Nat.+ z2-bit c Nat.* 4 Nat.+ z2-bit d Nat.* 8

  -- The four rows of a matrix, each encoded as a 4-bit number.
  Enc4 : Set
  Enc4 = ℕ × ℕ × ℕ × ℕ

  sel-enc : Enc4 -> ℕ -> ℕ
  sel-enc (a , b , c , d) 0 = a
  sel-enc (a , b , c , d) 1 = b
  sel-enc (a , b , c , d) 2 = c
  sel-enc (a , b , c , d) _ = d

  encode-rows : Vector 4 (Vector 4 Z2) -> Enc4
  encode-rows (r₀ ∷ r₁ ∷ r₂ ∷ r₃ ∷ []) =
    encode-row r₀ , encode-row r₁ , encode-row r₂ , encode-row r₃

  encode-enc : Enc4 -> ℕ
  encode-enc (a , b , c , d) = a Nat.+ b Nat.* 16 Nat.+ c Nat.* 256 Nat.+ d Nat.* 4096

  encode-matrix : Matrix 4 4 Z2 -> ℕ
  encode-matrix m = encode-enc (encode-rows (rows-4 m))

  -- The rows of M·P_y, encoded.
  cols-perm : Tuple4 -> Vector 4 (Vector 4 Z2) -> Enc4
  cols-perm y (r₀ ∷ r₁ ∷ r₂ ∷ r₃ ∷ []) =
      encode-row (select4 y r₀) , encode-row (select4 y r₁)
    , encode-row (select4 y r₂) , encode-row (select4 y r₃)

  -- For each of the 24 right permutations y, the encoded rows of
  -- M·P_y. The list is built lazily and shared over the outer loop.
  cols-table : Vector 4 (Vector 4 Z2) -> List (Tuple4 × Enc4)
  cols-table rs = List.map (λ y -> y , cols-perm y rs) all-perms

  -- The code of P_x·M·P_y, given the encoded rows of M·P_y and x⁻¹.
  lar-code : Enc4 -> Tuple4 -> ℕ
  lar-code e xi =
    encode-enc (sel-enc e (sel xi 0) , sel-enc e (sel xi 1) , sel-enc e (sel xi 2) , sel-enc e (sel xi 3))

  -- The codes of the seven patterns, in the authors' search order.
  -- This is a top-level constant, so it is computed only once.
  pattern-codes : List (ℕ × SixCases)
  pattern-codes = List.map (λ p -> encode-matrix (pattern-matrix p) , p) six-cases

  code-i : ℕ
  code-i = encode-matrix (pattern-matrix I)

  case-of-code : ℕ -> List (ℕ × SixCases) -> Maybe SixCases
  case-of-code c [] = nothing
  case-of-code c ((c' , p) ∷ ps) = if c Nat.≡ᵇ c' then just p else case-of-code c ps

  -- The inner loop of lemma_six: for a fixed left permutation x (with
  -- inverse xi), find the first right permutation y and pattern p
  -- with ρˡ₁(P_x·A·P_y) = p.
  search-y : Tuple4 -> Tuple4 -> List (Tuple4 × Enc4) -> Maybe (SixCases × Tuple4 × Tuple4)
  search-y x xi [] = nothing
  search-y x xi ((y , e) ∷ rest) with case-of-code (lar-code e xi) pattern-codes
  ... | just p = just (p , x , y)
  ... | nothing = search-y x xi rest

  search-x : List Tuple4 -> List (Tuple4 × Enc4) -> Maybe (SixCases × Tuple4 × Tuple4)
  search-x [] tbl = nothing
  search-x (x ∷ xs) tbl with search-y x (perm-inverse x) tbl
  ... | just r = just r
  ... | nothing = search-x xs tbl

  -- The lde-0 branch of lemma_six: find the first permutation x with
  -- ρ⁰₁(P_x·A) the identity pattern.
  search-i : List Tuple4 -> Enc4 -> Maybe Tuple4
  search-i [] e = nothing
  search-i (x ∷ xs) e =
    if lar-code e (perm-inverse x) Nat.≡ᵇ code-i then just x else search-i xs e

-- ----------------------------------------------------------------------
-- * The data of one level of the algorithm

-- Everything that lemma-six computes about an operator A: its lde l,
-- its pattern, the two permutations x, y of Lemma IV.1, and the
-- residue matrix ρˡ₂(P_x·A·P_y) that the refinements work on.
record LevelData : Set where
  constructor level-data
  field
    lev-lde : ℕ
    lev-pat : SixCases
    lev-x : Tuple4
    lev-y : Tuple4
    lev-res : Matrix 4 4 R2
open LevelData public

-- The left and right permutation circuits of Lemma IV.1 (the
-- authors' l and r).
lev-lcir lev-rcir : LevelData -> Circuit
lev-lcir ld = perm-circuit-of (lev-x ld)
lev-rcir ld = perm-circuit-of (lev-y ld)

private
  identity-perm : Tuple4
  identity-perm = 0 , 1 , 2 , 3

  level-from : ℕ -> Matrix 4 4 ZComplex -> Maybe LevelData
  level-from zero w with search-i all-perms (encode-rows (rows-4 (rho1-of w)))
  ... | nothing = nothing
  ... | just x = just (level-data 0 I x identity-perm (permute-matrix x identity-perm (rho2-of w)))
  level-from l@(suc _) w with search-x all-perms (cols-table (rows-4 (rho1-of w)))
  ... | nothing = nothing
  ... | just (p , x , y) = just (level-data l p x y (permute-matrix x y (rho2-of w)))

-- The level data of an operator whose lde is known to be l.
level-at : ℕ -> Matrix 4 4 DComplex -> Maybe LevelData
level-at l m = level-from l (integral-matrix l m)

-- The level data of an operator.
level-of : Matrix 4 4 DComplex -> Maybe LevelData
level-of m = level-at (lde m) m

-- ----------------------------------------------------------------------
-- * Lemma IV.1

-- Given an operator A, return its pattern p and permutation circuits
-- L and R with ρˡ₁(⟦L⟧·A·⟦R⟧) = p, where l = lde A. If lde A = 0 the
-- pattern is (i), R is empty and L is the permutation circuit that
-- makes ρ⁰₁ the identity (this is the authors' lemma_six). Returns
-- nothing if A is not a two-qubit Clifford+CS operator (the authors'
-- code raises an error).
lemma-six : Matrix 4 4 DComplex -> Maybe (SixCases × Circuit × Circuit)
lemma-six m with level-of m
... | nothing = nothing
... | just ld = just (lev-pat ld , lev-lcir ld , lev-rcir ld)

-- The pattern of an operator (the authors' cof; U4Di's patof returns
-- the pattern matrix instead).
patof : Matrix 4 4 DComplex -> Maybe SixCases
patof m with level-of m
... | nothing = nothing
... | just ld = just (lev-pat ld)

-- The authors' name for patof.
cof : Matrix 4 4 DComplex -> Maybe SixCases
cof = patof

-- ----------------------------------------------------------------------
-- * The one-level phase corrections
--
-- The authors' im v j is the one-level matrix diag(1,...,i,...,1)
-- with the i in position j when the residue v is ρ₂(i) = 11, and the
-- identity otherwise; the refinements multiply four such matrices,
-- giving a diagonal generalized permutation diag(i^{e₀},...,i^{e₃}).
-- We represent it by its exponent vector.

-- The exponent of the authors' im v j.
im-exp : R2 -> ℕ
im-exp v = if v == r2-i then 1 else 0

-- The diagonal matrix and the diagonal circuit of an exponent vector
-- (the authors' product of im's, and dcir of it). The circuit has at
-- most one CS gate and no K gate.
im-matrix : Tuple4 -> Matrix 4 4 DComplex
im-matrix = diag-matrix-of

im-circuit : Tuple4 -> Circuit
im-circuit = diag-circuit-of

-- Its (2,0)-residue (the authors' rho 0 2 of it).
im-res : Tuple4 -> Matrix 4 4 R2
im-res e = r2-of (im-matrix e)

-- ----------------------------------------------------------------------
-- * The target normal forms of Section IV B
--
-- These are the residue matrices ρˡ₂(⟦L⟧·A·⟦R⟧) that the refinements
-- produce, as documented in the comments of the authors' code. They
-- are stated here so that they can be checked (see normal-forms and
-- refine-normal-form? below, Test.KoptSynth and Test.KoptNormRun).

private
  -- A 4×4 matrix over ℤ[i]/(γ²), by rows.
  r2-matrix : (R2 × R2 × R2 × R2) -> (R2 × R2 × R2 × R2)
            -> (R2 × R2 × R2 × R2) -> (R2 × R2 × R2 × R2) -> Matrix 4 4 R2
  r2-matrix = matrix4x4

-- Pattern (ii), lde > 1.
pii2 : Z2 -> Matrix 4 4 R2
pii2 d =
  r2-matrix (r2-one    , r2-one    , r2-shift  , r2-zero)
            (r2-one    , r2-one    , r2-shift  , r2-zero)
            (r2-shift  , r2-shift  , (Even ∷ d ∷ []) , (Even ∷ d ∷ []))
            (r2-zero   , r2-zero   , (Even ∷ d ∷ []) , (Even ∷ d ∷ []))

-- Pattern (ii), lde = 1.
pii2k1 : Z2 -> Z2 -> Z2 -> Z2 -> Matrix 4 4 R2
pii2k1 d e f g =
  r2-matrix (r2-one  , r2-one  , r2-zero , r2-zero)
            (r2-one  , r2-one  , r2-zero , r2-zero)
            (r2-zero , r2-zero , (Even ∷ d ∷ []) , (Even ∷ e ∷ []))
            (r2-zero , r2-zero , (Even ∷ f ∷ []) , (Even ∷ g ∷ []))

-- Pattern (iii), lde > 1.
piii2 : Matrix 4 4 R2
piii2 =
  r2-matrix (r2-one   , r2-one   , r2-shift , r2-zero)
            (r2-one   , r2-one   , r2-zero  , r2-shift)
            (r2-shift , r2-zero  , r2-one   , r2-one)
            (r2-zero  , r2-shift , r2-one   , r2-one)

-- Pattern (iii), lde = 1.
piii2k1 : Matrix 4 4 R2
piii2k1 =
  r2-matrix (r2-one  , r2-one  , r2-zero , r2-zero)
            (r2-one  , r2-one  , r2-zero , r2-zero)
            (r2-zero , r2-zero , r2-one  , r2-one)
            (r2-zero , r2-zero , r2-one  , r2-one)

-- Pattern (iv): e is an indeterminate and f = e+1.
case-iv-2 : Z2 -> Matrix 4 4 R2
case-iv-2 e =
  r2-matrix (r2-one   , r2-one   , r2-one          , r2-one)
            (r2-one   , r2-one   , r2-one          , r2-one)
            (r2-shift , r2-shift , (Even ∷ e ∷ []) , (Even ∷ e ∷ []))
            (r2-zero  , r2-zero  , (Even ∷ (e + Odd) ∷ []) , (Even ∷ (e + Odd) ∷ []))

-- Pattern (iv)ᵀ: the transpose of case-iv-2.
case-ivt-2 : Z2 -> Matrix 4 4 R2
case-ivt-2 e = matrix-transpose (case-iv-2 e)

-- Pattern (v).
pv2 : Matrix 4 4 R2
pv2 =
  r2-matrix (r2-one , r2-one   , r2-shift , r2-zero)
            (r2-one , r2-one   , r2-zero  , r2-shift)
            (r2-one , r2-i     , r2-one   , r2-i)
            (r2-one , r2-i     , r2-i     , r2-one)

-- Pattern (vi): e is an indeterminate.
pvi2 : Z2 -> Matrix 4 4 R2
pvi2 e =
  r2-matrix (r2-one , r2-one , r2-one          , r2-one)
            (r2-one , r2-one , r2-one          , r2-one)
            (r2-one , r2-one , (Odd ∷ e ∷ [])  , (Odd ∷ e ∷ []))
            (r2-one , r2-one , (Odd ∷ e ∷ [])  , (Odd ∷ e ∷ []))

-- ----------------------------------------------------------------------
-- * The refinements (Sections IV B 1-6)
--
-- Each refinement takes the level data of an operator A (so that
-- lemma-six is computed once) and returns circuits L, R such that
-- ρˡ₂(⟦L⟧·A·⟦R⟧) is the normal form above. The circuits L and R
-- contain no K gate.

-- Pattern (iv): ρˡ₂(⟦L⟧·A·⟦R⟧) = case-iv-2 e.
refine-iv-at : LevelData -> Circuit × Circuit
refine-iv-at ld
  with lev-res ld
... | m2
  with im-exp (index-4 m2 0 0) , im-exp (index-4 m2 0 1) , im-exp (index-4 m2 0 2) , im-exp (index-4 m2 0 3)
... | rc
  with m2 r2∙ im-res rc
... | m2'
  with (if index-4 m2' 1 0 == r2-one then (0 , 0 , 0 , 0) else (0 , im-exp (index-4 m2' 1 0) , 1 , 0))
... | lc
  with im-res lc r2∙ m2'
... | m2''
  with (if index-4 m2'' 2 0 == r2-shift then [] else CX ∷ [])
... | lp
  with r2-of-circuit lp r2∙ m2''
... | m2''' = (lp ++ im-circuit lc ++ lev-lcir ld) , (lev-rcir ld ++ im-circuit rc ++ rp)
  where
    rp : Circuit
    rp = if index-4 m2''' 2 1 == r2-shift then []
         else if index-4 m2''' 2 2 == r2-shift then Ex ∷ [] else CX ∷ Ex ∷ []

-- Pattern (ii): ρˡ₂(⟦L⟧·A·⟦R⟧) = pii2 d if lde A > 1, pii2k1 d e f g if
-- lde A = 1.
refine-ii-at : LevelData -> Circuit × Circuit
refine-ii-at ld
  with lev-res ld
... | mres
  with (if index-4 mres 0 0 r2+ index-4 mres 0 1 == r2-zero
        then (im-exp (index-4 mres 0 0) , im-exp (index-4 mres 0 1) , 0 , 0)
        else (im-exp (index-4 mres 0 0) , im-exp (index-4 mres 0 1) , 0 , 1))
... | rc
  with mres r2∙ im-res rc
... | mres'
  with (if index-4 mres' 1 0 == r2-one then (0 , 0 , 0 , 0) else (0 , im-exp (index-4 mres' 1 0) , 0 , 1))
... | lc
  with im-res lc r2∙ mres'
... | mres''
  with (if index-4 mres'' 2 0 == r2-shift then [] else CX ∷ [])
... | l''
  with r2-of-circuit l'' r2∙ mres''
... | mres''' = body
  where
    r'' : Circuit
    r'' = if index-4 mres''' 0 2 == r2-shift then [] else CX ∷ []

    body : Circuit × Circuit
    body = if lev-lde ld Nat.≡ᵇ 1
           then ((im-circuit lc ++ lev-lcir ld) , (lev-rcir ld ++ im-circuit rc))
           else ((l'' ++ im-circuit lc ++ lev-lcir ld) , (lev-rcir ld ++ im-circuit rc ++ r''))

-- Pattern (iii): ρˡ₂(⟦L⟧·A·⟦R⟧) = piii2 if lde A > 1, piii2k1 if lde A = 1.
refine-iii-at : LevelData -> Circuit × Circuit
refine-iii-at ld
  with lev-res ld
... | mres
  with im-exp (index-4 mres 0 0) , im-exp (index-4 mres 0 1) , im-exp (index-4 mres 2 2) , im-exp (index-4 mres 2 3)
... | rc
  with mres r2∙ im-res rc
... | mres'
  with im-exp (index-4 mres' 0 0) , im-exp (index-4 mres' 1 0) , 0 , im-exp (index-4 mres' 3 2)
... | lc
  with im-res lc r2∙ mres'
... | mres''
  with (if index-4 mres'' 2 0 == r2-shift then [] else CX ∷ [])
... | l''
  with r2-of-circuit l'' r2∙ mres''
... | mres''' = body
  where
    r'' : Circuit
    r'' = if index-4 mres''' 0 2 == r2-shift then [] else CX ∷ []

    body : Circuit × Circuit
    body = if lev-lde ld Nat.≡ᵇ 1
           then ((im-circuit lc ++ lev-lcir ld) , (lev-rcir ld ++ im-circuit rc))
           else ((l'' ++ im-circuit lc ++ lev-lcir ld) , (lev-rcir ld ++ im-circuit rc ++ r''))

-- Pattern (v): ρˡ₂(⟦L⟧·A·⟦R⟧) = pv2.
refine-v-at : LevelData -> Circuit × Circuit
refine-v-at ld
  with lev-res ld
... | mres
  with im-exp (index-4 mres 0 0) , im-exp (index-4 mres 1 0) , im-exp (index-4 mres 2 0) , im-exp (index-4 mres 3 0)
... | lc
  with im-res lc r2∙ mres
... | mres'
  with (0 , im-exp (index-4 mres' 0 1) , 0 , 0)
... | rc
  with mres' r2∙ im-res rc
... | mres''
  with (if index-4 mres'' 0 2 == r2-shift then [] else CX ∷ [])
... | r''
  with mres'' r2∙ r2-of-circuit r''
... | mres''' = (im-circuit lc ++ lev-lcir ld)
              , (lev-rcir ld ++ im-circuit rc ++ r'' ++ im-circuit rc')
  where
    rc' : Tuple4
    rc' = 0 , 0 , im-exp (index-4 mres''' 2 2) , im-exp (index-4 mres''' 3 3)

-- Pattern (vi): ρˡ₂(⟦L⟧·A·⟦R⟧) = pvi2 e.
refine-vi-at : LevelData -> Circuit × Circuit
refine-vi-at ld
  with lev-res ld
... | mres
  with im-exp (index-4 mres 0 0) , im-exp (index-4 mres 1 0) , im-exp (index-4 mres 2 0) , im-exp (index-4 mres 3 0)
... | lc
  with im-res lc r2∙ mres
... | mres'
  with (0 , im-exp (index-4 mres' 0 1) , im-exp (index-4 mres' 0 2) , im-exp (index-4 mres' 0 3))
... | rc
  with mres' r2∙ im-res rc
... | mres''
  with (if index-4 mres'' 1 1 == r2-one then []
        else if index-4 mres'' 2 1 == r2-one then Ex ∷ [] else Ex ∷ CX ∷ [])
... | l''
  with r2-of-circuit l'' r2∙ mres''
... | mres''' = (l''' ++ l'' ++ im-circuit lc ++ lev-lcir ld)
              , (lev-rcir ld ++ im-circuit rc ++ r''')
  where
    l''' : Circuit
    l''' = if index-4 mres''' 1 2 == r2-one then []
           else if index-4 mres''' 2 2 == r2-one then Ex ∷ [] else Ex ∷ CX ∷ []

    r''' : Circuit
    r''' = if index-4 mres''' 2 1 == r2-one then []
           else if index-4 mres''' 2 2 == r2-one then Ex ∷ [] else CX ∷ Ex ∷ []

-- Pattern (iv)ᵀ: refine the adjoint, which has pattern (iv), and
-- invert the two circuits.
refine-ivt-of : Matrix 4 4 DComplex -> Circuit × Circuit
refine-ivt-of m with level-of (adjoint m)
... | nothing = [] , []
... | just ld with refine-iv-at ld
...   | (l , r) = inv-circuit r , inv-circuit l

-- The dispatcher. Pattern (i) needs no refinement (the authors' code
-- has no case for it and fails at run time).
refine-at : LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit
refine-at ld m with lev-pat ld
... | I = [] , []
... | II = refine-ii-at ld
... | III = refine-iii-at ld
... | IV = refine-iv-at ld
... | IVt = refine-ivt-of m
... | V = refine-v-at ld
... | VI = refine-vi-at ld

-- ----------------------------------------------------------------------
-- * The refinements, as functions of the operator
--
-- These are the authors' refine_xx: they compute lemma-six
-- themselves. If the pattern of the operator is not the expected one,
-- the refinement is applied anyway (the authors' code raises an
-- error); if the operator has no pattern at all, the result is the
-- pair of empty circuits.

private
  refine-by : (LevelData -> Circuit × Circuit) -> Matrix 4 4 DComplex -> Circuit × Circuit
  refine-by f m with level-of m
  ... | nothing = [] , []
  ... | just ld = f ld

refine-ii refine-iii refine-iv refine-v refine-vi : Matrix 4 4 DComplex -> Circuit × Circuit
refine-ii = refine-by refine-ii-at
refine-iii = refine-by refine-iii-at
refine-iv = refine-by refine-iv-at
refine-v = refine-by refine-v-at
refine-vi = refine-by refine-vi-at

refine-ivt : Matrix 4 4 DComplex -> Circuit × Circuit
refine-ivt = refine-ivt-of

refine : Matrix 4 4 DComplex -> Circuit × Circuit
refine m with level-of m
... | nothing = [] , []
... | just ld = refine-at ld m

-- ----------------------------------------------------------------------
-- * Checking the refinements
--
-- The normal forms that ρˡ₂(⟦L⟧·A·⟦R⟧) may take, for each pattern
-- and lde. This is what the authors' test_refine_ii, ...,
-- test_refine_vi check. For pattern (ii) at lde 1 the bottom right
-- 2×2 block is unconstrained, so all 16 possibilities are listed;
-- for pattern (iv)ᵀ at odd lde there is an extra factor of i, see
-- ivt-forms. With these two amendments, refine-normal-form? holds
-- for all 12000 operators of the authors' data file.

private
  z2s : List Z2
  z2s = Even ∷ Odd ∷ []

  all-pii2k1 : List (Matrix 4 4 R2)
  all-pii2k1 =
    List.concatMap (λ d ->
      List.concatMap (λ e ->
        List.concatMap (λ f ->
          List.map (λ g -> pii2k1 d e f g) z2s) z2s) z2s) z2s

  even-ℕ : ℕ -> Bool
  even-ℕ zero = true
  even-ℕ (suc zero) = false
  even-ℕ (suc (suc n)) = even-ℕ n

  r2-scale-matrix : R2 -> Matrix 4 4 R2 -> Matrix 4 4 R2
  r2-scale-matrix x = matrix-map (x r2*_)

  -- ρˡ₂ is not quite invariant under adjoints: γ† = -iγ, so
  -- (γˡA)† = (-i)ˡ γˡA† and therefore
  --
  --   ρˡ₂(A†) = ρ₂(iˡ) · ρˡ₂(A)ᵀ,
  --
  -- with ρ₂(iˡ) = 11 for odd l and 10 for even l. The refinement of
  -- pattern (iv)ᵀ is the refinement of the adjoint, so for odd l its
  -- normal form is the transpose of the one of case (iv) multiplied
  -- by 11. (The comment of the authors' refine_ivt and their
  -- test_refine_ivt only list the unmultiplied form; their test
  -- prints its outcome rather than asserting it, so the omission is
  -- invisible there.)
  ivt-forms : ℕ -> List (Matrix 4 4 R2)
  ivt-forms l =
    List.map (r2-scale-matrix (if even-ℕ l then r2-one else r2-i))
             (case-ivt-2 Even ∷ case-ivt-2 Odd ∷ [])

normal-forms : SixCases -> ℕ -> List (Matrix 4 4 R2)
normal-forms I l = []
normal-forms II 1 = all-pii2k1
normal-forms II l = pii2 Even ∷ pii2 Odd ∷ []
normal-forms III 1 = piii2k1 ∷ []
normal-forms III l = piii2 ∷ []
normal-forms IV l = case-iv-2 Even ∷ case-iv-2 Odd ∷ []
normal-forms IVt l = ivt-forms l
normal-forms V l = pv2 ∷ []
normal-forms VI l = pvi2 Even ∷ pvi2 Odd ∷ []

-- ----------------------------------------------------------------------
-- ** The unitary normal forms of pattern (ii) at lde 1
--
-- normal-forms II 1 lists all 16 values of pii2k1 d e f g, because
-- the comment of the authors' refine_ii leaves the bottom right 2×2
-- block of ρ¹₂(⟦L⟧·A·⟦R⟧) unconstrained. Unitarity cuts the 16 down
-- to 2. Indeed, write B = γ·⟦L⟧·A·⟦R⟧, which is integral because the
-- lde is 1; B is γ times a unitary, so every row and every column of
-- B has ∥·∥² = |γ|² = 2. In column 2 the entries in rows 0 and 1 have
-- residue 00, i.e. are divisible by γ² and so have norm divisible by
-- 4: they must vanish. The entry in row 2 has residue 0d, which is 00
-- (norm divisible by 4, hence 0) when d = Even and 01 = ρ₂(γ·odd)
-- (norm 2·odd) when d = Odd, and likewise for the entry in row 3 and
-- f. As the column norm is 2, exactly one of d and f is Odd. The same
-- argument for column 3 makes exactly one of e and g Odd, and for
-- rows 2 and 3 exactly one of d, e and exactly one of f, g. Hence
-- (d,e,f,g) is (Odd,Even,Even,Odd) or (Even,Odd,Odd,Even): the
-- bottom right block of B is γ·(a permutation matrix of size 2 with
-- unit entries).
pii2k1-unitary : List (Matrix 4 4 R2)
pii2k1-unitary = pii2k1 Odd Even Even Odd ∷ pii2k1 Even Odd Odd Even ∷ []

-- normal-forms with the 16 combinations of pattern (ii) at lde 1
-- replaced by the two that a unitary operator can have. This is a
-- sublist of normal-forms, so refine-normal-form-unitary? implies
-- refine-normal-form?; it holds for all 12000 operators of the
-- authors' data file (check (i) of Test.KoptSynthRun).
normal-forms-unitary : SixCases -> ℕ -> List (Matrix 4 4 R2)
normal-forms-unitary II 1 = pii2k1-unitary
normal-forms-unitary p l = normal-forms p l

private
  r2-elem : Matrix 4 4 R2 -> List (Matrix 4 4 R2) -> Bool
  r2-elem m [] = false
  r2-elem m (x ∷ xs) = if m == x then true else r2-elem m xs

  normal-form-at : LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit -> Bool
  normal-form-at ld m (lcir , rcir) =
    r2-elem (residue-matrix (lev-lde ld) 2 (⟦ lcir ⟧ * m * ⟦ rcir ⟧))
            (normal-forms (lev-pat ld) (lev-lde ld))

  normal-form-unitary-at : LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit -> Bool
  normal-form-unitary-at ld m (lcir , rcir) =
    r2-elem (residue-matrix (lev-lde ld) 2 (⟦ lcir ⟧ * m * ⟦ rcir ⟧))
            (normal-forms-unitary (lev-pat ld) (lev-lde ld))

-- Does the refinement of A bring ρˡ₂(⟦L⟧·A·⟦R⟧) into the documented
-- normal form? (True for pattern (i), which needs no refinement.)
refine-normal-form? : Matrix 4 4 DComplex -> Bool
refine-normal-form? m with level-of m
... | nothing = false
... | just ld = if lev-pat ld == I then true else normal-form-at ld m (refine-at ld m)

-- The same with the unitarity-restricted list of normal forms.
refine-normal-form-unitary? : Matrix 4 4 DComplex -> Bool
refine-normal-form-unitary? m with level-of m
... | nothing = false
... | just ld = if lev-pat ld == I then true else normal-form-unitary-at ld m (refine-at ld m)
