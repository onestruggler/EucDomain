-- Formalization of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026),
--
-- in the ring framework of this repository (Typeclasses, Instances,
-- Quantum.Synthesis.Ring, Quantum.Synthesis.Matrix).
--
-- This module is Section II ("Some algebra") of the paper: the ring
-- 𝔻[i] = ℤ[½, i], the prime γ = 1 + i, the least denominator exponent
-- lde with respect to γ, and the residues ρₙ : ℤ[i] → ℤ[i]/(γⁿ),
-- represented as binary strings b₀b₁...bₙ₋₁ (Section II B).
--
-- Naming: the rings are those of the framework, ℤ[i] = ZComplex and
-- 𝔻[i] = DComplex; the paper's γ is also called lam in the authors'
-- Haskell implementation.

{-# OPTIONS --without-K --safe #-}

module Kopt.Base where

open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_ ; _∧_ ; _∨_)
open import Data.List.Base using (List ; [] ; _∷_ ; map ; foldr)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤)
open import Data.String.Base using (String ; _++_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix

-- ----------------------------------------------------------------------
-- * The Gaussian prime γ = 1 + i

module _ {A : Set} {{_ : Ring A}} {{_ : ComplexRing A}} where
  open LiteralsFor A

  -- The paper's γ, in any ring that contains i (in particular in ℤ[i]
  -- and in 𝔻[i]). Note γ² = 2i, so γ² and 2 are associates.
  γ : A
  γ = 1 + i

  -- The conjugate γ† = 1 - i.
  γ† : A
  γ† = 1 - i

  -- 1/γ = (1 - i)/2 in any ring containing ½ and i.
  1/γ : {{_ : HalfRing A}} -> A
  1/γ = half * γ†

  -- Powers of γ. This is the structural power x ↑ n = x·(x·(…·1)),
  -- NOT the framework's _^_ (which is computed by repeated squaring
  -- like Haskell's (^)). The two agree on every ring whose
  -- multiplication is associative, but only the structural one can be
  -- reasoned about, since the SemiRing class carries no laws: see
  -- Kopt.Properties.Gamma, whose _↑_ this matches definitionally.
  infixr 8 γ↑_
  γ↑_ : ℕ -> A
  γ↑ zero = 1#
  γ↑ (suc n) = γ * γ↑ n

-- ----------------------------------------------------------------------
-- * Parity in ℤ[i] (Definition II.4)

-- x = a + bi is even if γ | x, i.e. if a + b is an even integer, and
-- odd otherwise. For x ∈ ℤ this is the usual parity.
parityℤ[i] : ZComplex -> Z2
parityℤ[i] (Cplx a b) = if evenℤ (a + b) then Even else Odd

evenℤ[i] oddℤ[i] : ZComplex -> Bool
evenℤ[i] (Cplx a b) = evenℤ (a + b)
oddℤ[i] x = not (evenℤ[i] x)

instance
  ParityZComplex : Parity ZComplex
  ParityZComplex .parity = parityℤ[i]

-- Division by γ in ℤ[i]: (a + bi)/(1 + i) = (a+b)/2 + ((b-a)/2) i.
-- For odd x (Haskell: when γ ∤ x) the halves are rounded down.
_/γ : ZComplex -> ZComplex
(Cplx a b) /γ = Cplx (shiftR (a + b) 1) (shiftR (b - a) 1)

-- Multiplication by γ.
_*γ : ZComplex -> ZComplex
x *γ = x * γ

-- ----------------------------------------------------------------------
-- * The least denominator exponent (Definition II.1)

-- A natural number k is a denominator exponent for t ∈ 𝔻[i] if
-- γᵏt ∈ ℤ[i]; lde t is the least one. Like the framework's DenomExp
-- (which is about powers of 1/√2), this is a type class, with
-- instances for 𝔻[i] and for vectors and matrices over it.
record LamDenomExp (A : Set) : Set where
  field
    -- The least k ≥ 0 such that a = b/γᵏ with b integral.
    lde : A -> ℕ
    -- Factor out a kth power of 1/γ, i.e. compute a·γᵏ.
    lde-factor : A -> ℕ -> A
open LamDenomExp {{...}} public

-- Calculate and factor out the least denominator exponent k of a.
-- Return (b, k) where a = b/γᵏ and k ≥ 0.
lde-decompose : {A B : Set} {{_ : WholePart A B}} {{_ : LamDenomExp A}} -> A -> B × ℕ
lde-decompose a = to-whole (lde-factor a k) , k
  where k = lde a

private
  -- The lde of a dyadic complex number. Let x = a/2ᵏ + (b/2ˡ)i and
  -- k' = max k l. Then 2^k' x = a2^(k'-k) + b2^(k'-l) i is integral,
  -- so 2k' is a denominator exponent; it is not least exactly when
  -- that integer is even (divisible by γ), by Lemma II.7.
  lde-DComplex : DComplex -> ℕ
  lde-DComplex (Cplx x y) with decompose-dyadic x | decompose-dyadic y
  ... | a , k | b , l = go (max k l)
    where
      go : ℕ -> ℕ
      go zero = 0
      go k'@(suc _) =
        if evenℤ (shiftL a (k' Nat.∸ k) + shiftL b (k' Nat.∸ l))
        then 2 * k' Nat.∸ 1
        else 2 * k'

instance
  LamDenomExpDComplex : LamDenomExp DComplex
  LamDenomExpDComplex .lde = lde-DComplex
  LamDenomExpDComplex .lde-factor a k = a * γ↑ k

  LamDenomExpVector : {n : ℕ} {A : Set} {{_ : LamDenomExp A}} -> LamDenomExp (Vector n A)
  LamDenomExpVector .lde as = foldr (λ a k -> max (lde a) k) 0 (list-of-vector as)
  LamDenomExpVector .lde-factor as k = vector-map (λ a -> lde-factor a k) as

  LamDenomExpMatrix : {m n : ℕ} {A : Set} {{_ : LamDenomExp A}} -> LamDenomExp (Matrix m n A)
  LamDenomExpMatrix .lde (Matrix' m) = lde m
  LamDenomExpMatrix .lde-factor (Matrix' m) k = Matrix' (lde-factor m k)

  LamDenomExpPair : {A B : Set} {{_ : LamDenomExp A}} {{_ : LamDenomExp B}} -> LamDenomExp (A × B)
  LamDenomExpPair .lde (a , b) = max (lde a) (lde b)
  LamDenomExpPair .lde-factor (a , b) k = lde-factor a k , lde-factor b k

  LamDenomExpList : {A : Set} {{_ : LamDenomExp A}} -> LamDenomExp (List A)
  LamDenomExpList .lde as = foldr (λ a k -> max (lde a) k) 0 as
  LamDenomExpList .lde-factor as k = map (λ a -> lde-factor a k) as

-- ----------------------------------------------------------------------
-- * Residues (Section II B)

-- ℤ[i]/(γⁿ) = { Σ_{j<n} bⱼγʲ | bⱼ ∈ {0,1} }, and distinct binary
-- strings are distinct residue classes. We represent the residue
-- class of x by the string b₀b₁...bₙ₋₁ (least significant digit
-- first, as in the paper).
Residue : ℕ -> Set
Residue n = Vec Z2 n

-- The canonical projection ρₙ : ℤ[i] → ℤ[i]/(γⁿ): the first digit is
-- the parity, and the remaining digits are those of (x - b₀)/γ.
ρ : (n : ℕ) -> ZComplex -> Residue n
ρ zero x = []
ρ (suc n) x with parityℤ[i] x
... | Even = Even ∷ ρ n (x /γ)
... | Odd = Odd ∷ ρ n ((x - 1) /γ)

-- The value in ℤ[i] of a residue: Σ bⱼγʲ.
value-of-residue : {n : ℕ} -> Residue n -> ZComplex
value-of-residue [] = 0
value-of-residue (Even ∷ bs) = (value-of-residue bs) *γ
value-of-residue (Odd ∷ bs) = 1 + (value-of-residue bs) *γ

-- The (n,l)-residue of a dyadic complex number (Definition II.3):
-- ρˡₙ(x) = ρₙ(γˡx). Here l must be a denominator exponent of x (not
-- necessarily the least); otherwise γˡx is not integral and the
-- residue is that of its truncation.
residue : (l n : ℕ) -> DComplex -> Residue n
residue l n x = ρ n (to-whole (lde-factor x l))

-- The (n,l)-residue of a matrix, entrywise (Definition II.3). The
-- paper writes ρˡₙ(A); the arguments are (l, n, A) as in the authors'
-- Haskell code (rho k n m).
residue-matrix : {r c : ℕ} -> (l n : ℕ) -> Matrix r c DComplex -> Matrix r c (Residue n)
residue-matrix l n m = matrix-map (ρ n) (to-whole (lde-factor m l))

-- The (1,l)-residue of a matrix, as a matrix over ℤ₂ (this is the
-- "pattern" data of Section IV A).
residue1-matrix : {r c : ℕ} -> (l : ℕ) -> Matrix r c DComplex -> Matrix r c Z2
residue1-matrix l m = matrix-map parityℤ[i] (to-whole (lde-factor m l))

-- The (n,lde A)-residue of a matrix.
residue-lde : {r c : ℕ} -> (n : ℕ) -> Matrix r c DComplex -> Matrix r c (Residue n)
residue-lde n m = residue-matrix (lde m) n m

residue1-lde : {r c : ℕ} -> Matrix r c DComplex -> Matrix r c Z2
residue1-lde m = residue1-matrix (lde m) m

-- ----------------------------------------------------------------------
-- * Shifts (Section II C)

-- A right shift prepends a zero digit: it is the residue of γx.
RS : {n : ℕ} -> Residue n -> Residue (suc n)
RS bs = Even ∷ bs

-- A left shift drops the leading zero digit: the residue of x/γ, for
-- even x.
LS : {n : ℕ} -> Residue (suc n) -> Residue n
LS (_ ∷ bs) = bs

-- ----------------------------------------------------------------------
-- * Norms

-- The norm ∥x∥² = x†x of a Gaussian integer (Lemma II.5).
normℤ[i] : ZComplex -> ℤ
normℤ[i] (Cplx a b) = a ^2 + b ^2

-- ----------------------------------------------------------------------
-- * Printing

-- Residues are printed as binary strings, e.g. "100".
show-residue : {n : ℕ} -> Residue n -> String
show-residue [] = ""
show-residue (b ∷ bs) = show b ++ show-residue bs

instance
  ShowResidue : {n : ℕ} -> Show (Residue n)
  ShowResidue .showsPrec d bs = show-residue bs
