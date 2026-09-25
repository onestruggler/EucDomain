-- Section III of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the special unitaries of the paper -- permutation matrices,
-- diagonal unitaries, and generalized permutations -- and circuits
-- implementing them.
--
-- * A permutation matrix P_{a₀a₁a₂a₃} maps eⱼ ↦ e_{aⱼ}. All 24 of
--   them are Clifford operators, implementable by ≤ 3 gates; the
--   circuits are those of Table I of the paper (perm-circuit).
--
-- * Every diagonal 4×4 unitary over 𝔻[i] is diag(i^a,i^b,i^c,i^d),
--   and equals Z₀^{b₀}Z₁^{b₁}S₀^{b₂}S₁^{b₃}CZ^{b₄}CS^{b₅}·i^k for a
--   unique choice of bⱼ ∈ {0,1} and k ∈ {0,1,2,3} (diag-circuit):
--   ≤ 6 gates and ≤ 1 CS gate, up to the global phase i^k.
--
-- * A generalized permutation is a unitary over 𝔻[i] whose nonzero
--   pattern is that of a permutation matrix and whose nonzero entries
--   are powers of i. Every one is a product (permutation)·(diagonal),
--   and gperm-of produces a circuit for it with ≤ 9 gates, ≤ 1 CS
--   gate and no K gate -- exactly, i.e. including the global phase,
--   which is what the scalar gate Ii is for. The lde-0 Clifford+CS
--   operators are exactly the generalized permutations.
--
-- Where the authors' Haskell code looks the circuit up in a
-- precomputed table of all 6144 generalized permutations, we read off
-- the permutation and the phases and compute the circuit directly.

{-# OPTIONS --without-K --safe #-}

module Kopt.Permutations where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; is-just)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; _∸_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates

-- ----------------------------------------------------------------------
-- * Small arithmetic helpers

-- A 4-tuple of natural numbers. It is used both for permutations of
-- {0,1,2,3} (the tuple a₀a₁a₂a₃ denotes j ↦ aⱼ) and for the exponent
-- vectors of diagonal unitaries (the tuple abcd denotes
-- diag(i^a,i^b,i^c,i^d)).
Tuple4 : Set
Tuple4 = ℕ × ℕ × ℕ × ℕ

-- Reduction modulo 4 (the exponents of i only matter modulo 4).
mod4 : ℕ -> ℕ
mod4 0 = 0
mod4 1 = 1
mod4 2 = 2
mod4 3 = 3
mod4 (suc (suc (suc (suc n)))) = mod4 n

-- Subtraction modulo 4.
sub4 : ℕ -> ℕ -> ℕ
sub4 a b = mod4 (a + (4 ∸ mod4 b))

-- The powers of i in 𝔻[i].
pow-i : ℕ -> DComplex
pow-i n with mod4 n
... | 0 = 1
... | 1 = i
... | 2 = - 1
... | _ = - i

-- The jth component of a 4-tuple (the 4th and later components are
-- the last one).
sel : Tuple4 -> ℕ -> ℕ
sel (a₀ , a₁ , a₂ , a₃) 0 = a₀
sel (a₀ , a₁ , a₂ , a₃) 1 = a₁
sel (a₀ , a₁ , a₂ , a₃) 2 = a₂
sel (a₀ , a₁ , a₂ , a₃) _ = a₃

-- Composition of 4-tuples: (f ∘₄ σ) j = f (σ j).
infixr 9 _∘₄_
_∘₄_ : Tuple4 -> Tuple4 -> Tuple4
f ∘₄ σ = sel f (sel σ 0) , sel f (sel σ 1) , sel f (sel σ 2) , sel f (sel σ 3)

-- The inverse of a permutation of {0,1,2,3}. (For a tuple that is not
-- a permutation the result is meaningless but harmless.)
perm-inverse : Tuple4 -> Tuple4
perm-inverse a = idx 0 , idx 1 , idx 2 , idx 3
  where
    idx : ℕ -> ℕ
    idx j = if sel a 0 == j then 0 else
            if sel a 1 == j then 1 else
            if sel a 2 == j then 2 else 3

-- Are the four entries pairwise distinct?
distinct4 : Tuple4 -> Bool
distinct4 (a₀ , a₁ , a₂ , a₃) =
  (a₀ /= a₁) ∧ (a₀ /= a₂) ∧ (a₀ /= a₃) ∧ (a₁ /= a₂) ∧ (a₁ /= a₃) ∧ (a₂ /= a₃)

-- ----------------------------------------------------------------------
-- * The matrices

-- The column i^k·e_r of a 4×4-matrix.
unit-column : (r k : ℕ) -> Vector 4 DComplex
unit-column r k = entry 0 ∷ entry 1 ∷ entry 2 ∷ entry 3 ∷ []
  where
    entry : ℕ -> DComplex
    entry j = if r == j then pow-i k else 0

-- The generalized permutation matrix whose jth column is i^{pⱼ}·e_{aⱼ}.
gperm-matrix : (a₀ a₁ a₂ a₃ p₀ p₁ p₂ p₃ : ℕ) -> Matrix 4 4 DComplex
gperm-matrix a₀ a₁ a₂ a₃ p₀ p₁ p₂ p₃ =
  Matrix' (unit-column a₀ p₀ ∷ unit-column a₁ p₁ ∷ unit-column a₂ p₂ ∷ unit-column a₃ p₃ ∷ [])

-- The permutation matrix P_{a₀a₁a₂a₃}, which maps eⱼ ↦ e_{aⱼ}.
perm-matrix : (a₀ a₁ a₂ a₃ : ℕ) -> Matrix 4 4 DComplex
perm-matrix a₀ a₁ a₂ a₃ = gperm-matrix a₀ a₁ a₂ a₃ 0 0 0 0

-- The diagonal unitary diag(i^a, i^b, i^c, i^d).
diag-matrix : (a b c d : ℕ) -> Matrix 4 4 DComplex
diag-matrix a b c d = gperm-matrix 0 1 2 3 a b c d

-- Tupled versions.
gperm-matrix-of : Tuple4 -> Tuple4 -> Matrix 4 4 DComplex
gperm-matrix-of (a₀ , a₁ , a₂ , a₃) (p₀ , p₁ , p₂ , p₃) = gperm-matrix a₀ a₁ a₂ a₃ p₀ p₁ p₂ p₃

perm-matrix-of : Tuple4 -> Matrix 4 4 DComplex
perm-matrix-of (a₀ , a₁ , a₂ , a₃) = perm-matrix a₀ a₁ a₂ a₃

diag-matrix-of : Tuple4 -> Matrix 4 4 DComplex
diag-matrix-of (a , b , c , d) = diag-matrix a b c d

-- ----------------------------------------------------------------------
-- * Permutations (Table I)

-- All 24 permutations of {0,1,2,3}, in the order of Table I of the
-- paper (which is the order of Haskell's permutations [0,1,2,3]).
all-perms : List Tuple4
all-perms =
    (0 , 1 , 2 , 3) ∷ (1 , 0 , 2 , 3) ∷ (2 , 1 , 0 , 3) ∷ (1 , 2 , 0 , 3)
  ∷ (2 , 0 , 1 , 3) ∷ (0 , 2 , 1 , 3) ∷ (3 , 2 , 1 , 0) ∷ (2 , 3 , 1 , 0)
  ∷ (2 , 1 , 3 , 0) ∷ (3 , 1 , 2 , 0) ∷ (1 , 3 , 2 , 0) ∷ (1 , 2 , 3 , 0)
  ∷ (3 , 0 , 1 , 2) ∷ (0 , 3 , 1 , 2) ∷ (0 , 1 , 3 , 2) ∷ (3 , 1 , 0 , 2)
  ∷ (1 , 3 , 0 , 2) ∷ (1 , 0 , 3 , 2) ∷ (3 , 0 , 2 , 1) ∷ (0 , 3 , 2 , 1)
  ∷ (0 , 2 , 3 , 1) ∷ (3 , 2 , 0 , 1) ∷ (2 , 3 , 0 , 1) ∷ (2 , 0 , 3 , 1)
  ∷ []

-- A circuit for the permutation matrix P_{a₀a₁a₂a₃}: exactly Table I
-- of the paper. Every permutation needs at most three gates and no
-- K and no CS gate. A tuple that is not a permutation of {0,1,2,3} is
-- mapped to the empty circuit.
perm-circuit : (a₀ a₁ a₂ a₃ : ℕ) -> Circuit
perm-circuit 0 1 2 3 = []
perm-circuit 1 0 2 3 = X₁ ∷ CX ∷ []
perm-circuit 2 1 0 3 = X₀ ∷ XC ∷ []
perm-circuit 1 2 0 3 = Ex ∷ X₀ ∷ XC ∷ []
perm-circuit 2 0 1 3 = Ex ∷ X₁ ∷ CX ∷ []
perm-circuit 0 2 1 3 = Ex ∷ []
perm-circuit 3 2 1 0 = X₁ ∷ X₀ ∷ []
perm-circuit 2 3 1 0 = X₀ ∷ CX ∷ []
perm-circuit 2 1 3 0 = Ex ∷ X₁ ∷ XC ∷ []
perm-circuit 3 1 2 0 = Ex ∷ X₁ ∷ X₀ ∷ []
perm-circuit 1 3 2 0 = Ex ∷ X₀ ∷ CX ∷ []
perm-circuit 1 2 3 0 = X₁ ∷ XC ∷ []
perm-circuit 3 0 1 2 = XC ∷ X₁ ∷ []
perm-circuit 0 3 1 2 = Ex ∷ XC ∷ []
perm-circuit 0 1 3 2 = CX ∷ []
perm-circuit 3 1 0 2 = Ex ∷ CX ∷ X₀ ∷ []
perm-circuit 1 3 0 2 = Ex ∷ X₀ ∷ []
perm-circuit 1 0 3 2 = X₁ ∷ []
perm-circuit 3 0 2 1 = Ex ∷ XC ∷ X₁ ∷ []
perm-circuit 0 3 2 1 = XC ∷ []
perm-circuit 0 2 3 1 = Ex ∷ CX ∷ []
perm-circuit 3 2 0 1 = CX ∷ X₀ ∷ []
perm-circuit 2 3 0 1 = X₀ ∷ []
perm-circuit 2 0 3 1 = Ex ∷ X₁ ∷ []
perm-circuit _ _ _ _ = []

perm-circuit-of : Tuple4 -> Circuit
perm-circuit-of (a₀ , a₁ , a₂ , a₃) = perm-circuit a₀ a₁ a₂ a₃

-- The 24 permutation matrices (the authors' perm_mats), in the same
-- order as all-perms.
all-perm-matrices : List (Matrix 4 4 DComplex)
all-perm-matrices = List.map perm-matrix-of all-perms

-- ----------------------------------------------------------------------
-- * Diagonal unitaries

-- i^m on a single qubit, as a circuit over the given Z and S gates:
-- the empty circuit, S, Z, or ZS.
private
  zs-gates : ℕ -> Gate -> Gate -> Circuit
  zs-gates m zg sg with mod4 m
  ... | 0 = []
  ... | 1 = sg ∷ []
  ... | 2 = zg ∷ []
  ... | _ = zg ∷ sg ∷ []

  -- k copies of the scalar gate i (k < 4).
  ii-gates : ℕ -> Circuit
  ii-gates k with mod4 k
  ... | 0 = []
  ... | 1 = Ii ∷ []
  ... | 2 = Ii ∷ Ii ∷ []
  ... | _ = Ii ∷ Ii ∷ Ii ∷ []

-- A circuit for diag(i^a, i^b, i^c, i^d), of the form
-- Z₀^{b₀}Z₁^{b₁}S₀^{b₂}S₁^{b₃}CZ^{b₄}CS^{b₅}·i^k as in Section III B.
-- Writing the exponent vector in the basis
--
--   Ii = i^(1,1,1,1), S₀ = i^(0,0,1,1), S₁ = i^(0,1,0,1), CS = i^(0,0,0,1)
--
-- (with Z = S², CZ = CS²) gives k = a, the S₀-exponent c-a, the
-- S₁-exponent b-a and the CS-exponent d+a-b-c, all modulo 4. The
-- circuit has at most 6 gates besides the global phase i^k, at most
-- one CS gate and no K gate.
diag-circuit : (a b c d : ℕ) -> Circuit
diag-circuit a b c d =
  zs-gates (sub4 c a) Z₀ S₀ ++ zs-gates (sub4 b a) Z₁ S₁
    ++ zs-gates (sub4 (sub4 (d + mod4 a) b) c) CZ CS ++ ii-gates a

diag-circuit-of : Tuple4 -> Circuit
diag-circuit-of (a , b , c , d) = diag-circuit a b c d

-- The commutation fact of Section III C: for a permutation P and a
-- diagonal unitary D there is a diagonal unitary D′ with PD = D′P,
-- namely D′ = PDP⁻¹, whose exponent vector is e ∘ P⁻¹. It has the
-- same CS-count (indeed the same circuit up to a relabelling).
diag-commute : (p e : Tuple4) -> Tuple4
diag-commute p e = e ∘₄ perm-inverse p

-- ----------------------------------------------------------------------
-- * Generalized permutations

-- The exponent k with x = i^k, if there is one.
phase-of : DComplex -> Maybe ℕ
phase-of x =
  if x == 1 then just 0 else
  if x == i then just 1 else
  if x == - 1 then just 2 else
  if x == - i then just 3 else nothing

-- If a column of a matrix is i^k·e_r, return (r , k).
column-info : Vector 4 DComplex -> Maybe (ℕ × ℕ)
column-info (a ∷ b ∷ c ∷ d ∷ []) with phase-of a | phase-of b | phase-of c | phase-of d
... | just k | nothing | nothing | nothing =
      if (b == 0) ∧ (c == 0) ∧ (d == 0) then just (0 , k) else nothing
... | nothing | just k | nothing | nothing =
      if (a == 0) ∧ (c == 0) ∧ (d == 0) then just (1 , k) else nothing
... | nothing | nothing | just k | nothing =
      if (a == 0) ∧ (b == 0) ∧ (d == 0) then just (2 , k) else nothing
... | nothing | nothing | nothing | just k =
      if (a == 0) ∧ (b == 0) ∧ (c == 0) then just (3 , k) else nothing
... | _ | _ | _ | _ = nothing

-- If the matrix is a generalized permutation, return its permutation
-- a₀a₁a₂a₃ and its phase exponents p₀p₁p₂p₃, so that the matrix is
-- gperm-matrix a₀ a₁ a₂ a₃ p₀ p₁ p₂ p₃.
-- The case analysis is in the auxiliary function gperm-data-of rather
-- than in a "with", so that the four column-info results can be
-- rewritten when reasoning about gperm-data (and so that the type
-- checker never normalizes the matrix under a with-abstraction).
gperm-data-of : Maybe (ℕ × ℕ) -> Maybe (ℕ × ℕ) -> Maybe (ℕ × ℕ) -> Maybe (ℕ × ℕ) ->
                Maybe (Tuple4 × Tuple4)
gperm-data-of (just (a₀ , p₀)) (just (a₁ , p₁)) (just (a₂ , p₂)) (just (a₃ , p₃)) =
  if distinct4 (a₀ , a₁ , a₂ , a₃)
  then just ((a₀ , a₁ , a₂ , a₃) , (p₀ , p₁ , p₂ , p₃))
  else nothing
gperm-data-of _ _ _ _ = nothing

gperm-data : Matrix 4 4 DComplex -> Maybe (Tuple4 × Tuple4)
gperm-data (Matrix' (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ [])) =
  gperm-data-of (column-info v₀) (column-info v₁) (column-info v₂) (column-info v₃)

-- Is the matrix a generalized permutation? (Equivalently, by Section
-- III C, is it a Clifford+CS operator of lde 0?)
is-gperm : Matrix 4 4 DComplex -> Bool
is-gperm m = is-just (gperm-data m)

private
  -- The permutations of the X gates: X₀ = P₂₃₀₁, X₁ = P₁₀₃₂.
  x₀-perm x₁-perm : Tuple4
  x₀-perm = 2 , 3 , 0 , 1
  x₁-perm = 1 , 0 , 3 , 2

  -- Four circuits for the generalized permutation with permutation p
  -- and phases ph. The first writes it as D′·P, the second as P·D,
  -- and the last two as P·D·X (X = X₀ or X₁), which moves the global
  -- phase from the 0th to the 2nd resp. 1st diagonal entry. Since the
  -- number of scalar gates needed is the 0th exponent of the diagonal
  -- part, taking the shortest of the four keeps the total at 9 gates
  -- or fewer (the bound of Section III C); one candidate alone can
  -- need up to 13.
  gperm-candidates : (p ph : Tuple4) -> List Circuit
  gperm-candidates p ph =
      (diag-circuit-of (ph ∘₄ perm-inverse p) ++ perm-circuit-of p)
    ∷ (perm-circuit-of p ++ diag-circuit-of ph)
    ∷ (perm-circuit-of (p ∘₄ x₀-perm) ++ diag-circuit-of (ph ∘₄ x₀-perm) ++ (X₀ ∷ []))
    ∷ (perm-circuit-of (p ∘₄ x₁-perm) ++ diag-circuit-of (ph ∘₄ x₁-perm) ++ (X₁ ∷ []))
    ∷ []

  shortest-from : Circuit -> List Circuit -> Circuit
  shortest-from best [] = best
  shortest-from best (c ∷ cs) =
    if rlen c Nat.<ᵇ rlen best then shortest-from c cs else shortest-from best cs

  shortest : List Circuit -> Circuit
  shortest [] = []
  shortest (c ∷ cs) = shortest-from c cs

-- A circuit for a generalized permutation, exactly (including the
-- global phase): if m is a generalized permutation then
-- ⟦gperm-of m⟧ = m, and the circuit has at most 9 gates, at most one
-- CS gate and no K gate. Otherwise the result is nothing (the
-- authors' Haskell gperm_of raises an error in that case).
-- The circuit that gperm-of produces for the generalized permutation
-- with permutation part p and phase exponents ph: the shortest of the
-- four candidates. It is named (and public) so that it can be
-- reasoned about without unfolding gperm-of; see Kopt.SynthProperties.
gperm-circuit-for : Tuple4 -> Tuple4 -> Circuit
gperm-circuit-for p ph = shortest (gperm-candidates p ph)

-- Again the case analysis is in an auxiliary function rather than in
-- a "with", so that gperm-of can be computed from a known gperm-data.
gperm-of-data : Maybe (Tuple4 × Tuple4) -> Maybe Circuit
gperm-of-data nothing = nothing
gperm-of-data (just (p , ph)) = just (gperm-circuit-for p ph)

gperm-of : Matrix 4 4 DComplex -> Maybe Circuit
gperm-of m = gperm-of-data (gperm-data m)
