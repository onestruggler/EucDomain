-- Lemma IV.1 of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- every A ∈ 𝒞𝒞𝒮 has one of the six patterns, and it has pattern (i) if
-- and only if lde(A) = 0.
--
-- Unitarity is an explicit hypothesis (Kopt.Unitary.IsUnitary), since
-- the type Matrix 4 4 DComplex of the algorithm contains all matrices
-- and the statement is false without it: for example the matrix
-- γ⁻¹·1 has lde 1 and pattern (i).
--
-- The proof is the paper's, in three steps.
--
--  * ρˡ₁(A) is determined by the four counting facts of
--    Kopt.Unitary (Lemmas IV.2 and IV.3) up to the choice of
--    a ℤ₂-matrix: at lde l = k+1 > 0 every row and every column of
--    ρˡ₁(A) has an even number of odd entries, two distinct rows (or
--    columns) are both odd at an even number of positions, and ρˡ₁(A)
--    is not the zero matrix (Lemma II.7). At lde 0 the norms are
--    integral and sum to 1, so every row and every column of ρ⁰₁(A) is
--    a unit vector.
--
--  * Those are finitely many ℤ₂-matrices: 4096 = 8⁴ have even columns,
--    and the further conditions cut them down to the list pos-cand;
--    256 = 4⁴ have unit columns, cut down to the 24 permutation
--    matrices in zero-cand. Both lists are enumerated and the search
--    of lemma-six is *run* on every element of them by the type
--    checker (pos-check, zero-check). This is the combinatorial part of
--    the paper's Lemma IV.1, and these two checks are its proof.
--
--  * The defining equations of Kopt.Patterns.patof (which is why the
--    search there is written with auxiliary functions rather than with
--    `with`) then turn the outcome of the search into a statement about
--    patof.
--
-- The bridge between the two ways of computing ρˡ₁ -- the residues of
-- Kopt.Base, which use the structural power γ↑l, and
-- Kopt.Patterns.integral-matrix, which uses the fast γ-pow of
-- Kopt.GammaPow -- is γ-pow-↑ and rho1-integral below.

{-# OPTIONS --without-K --safe #-}

module Kopt.PatternFacts where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as IntP
import Data.Integer.Solver as IntSolver
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.GammaPow
open import Kopt.Properties.Algebra
open import Kopt.Gates using (Circuit)
open import Kopt.Permutations
open import Kopt.Patterns
open import Kopt.Unitary2
open import Kopt.Descent using (_∈ˡ_ ; here ; there ; all-of ; all-of-∈ ; filt ; ∈-filt ;
                               ∈-map ; ∈-++ˡ ; ∈-++ʳ)

private
  module ℤS = IntSolver.+-*-Solver
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex

  Op : Set
  Op = Matrix 4 4 DComplex

  true≢false : true ≡ false -> ⊥
  true≢false ()

  false≢true : false ≡ true -> ⊥
  false≢true ()

  just-inj : {A : Set} {x y : A} -> _≡_ {A = Maybe A} (just x) (just y) -> x ≡ y
  just-inj refl = refl

  ∨-true : {a b : Bool} -> a ∨ b ≡ true -> (a ≡ true) ⊎ (b ≡ true)
  ∨-true {true} {b} _ = inj₁ refl
  ∨-true {false} {true} _ = inj₂ refl

  ∧-intro : {a b : Bool} -> a ≡ true -> b ≡ true -> a ∧ b ≡ true
  ∧-intro refl refl = refl

  re-eq : {A : Set} {x y u v : A} -> Cplx x y ≡ Cplx u v -> x ≡ u
  re-eq refl = refl

-- A boolean equality test that succeeds is an equality (as in
-- Kopt.GPData, repeated here to avoid depending on that module).
==⇒≡ : {A : Set} {{_ : DecEq A}} {x y : A} -> (x == y) ≡ true -> x ≡ y
==⇒≡ {x = x} {y} e with x ≟ y
... | yes p = p
... | no _ = ⊥-elim (false≢true e)

-- ----------------------------------------------------------------------
-- * The two powers of γ agree
--
-- Kopt.GammaPow.gz computes γˡ in ℤ[i] by ⌊l/2⌋ multiplications by
-- γ² = 2i; this is the structural power.

private
  twoi-mul : (x : ZComplex) -> twoi* x ≡ γ * (γ * x)
  twoi-mul (Cplx a b) = trans (cong₂ Cplx (sym e1) (sym e2)) (sym rhs)
    where
      open ℤS
      rhs : γ * (γ * Cplx a b) ≡ Cplx ((a - b) - (b + a)) ((b + a) + (a - b))
      rhs = trans (cong (λ z -> γ * z) (γ*-Cplx a b)) (γ*-Cplx (a - b) (b + a))
      e1 : (a - b) - (b + a) ≡ - (b + b)
      e1 = solve 2 (λ x y -> (x :- y) :- (y :+ x) := :- (y :+ y)) refl a b
      e2 : (b + a) + (a - b) ≡ a + a
      e2 = solve 2 (λ x y -> (y :+ x) :+ (x :- y) := x :+ x) refl a b

gz-↑ : (l : ℕ) -> gz l ≡ (γ {ZComplex}) ↑ l
gz-↑ zero = refl
gz-↑ (suc zero) = sym (ZR.*-identityʳ γ)
gz-↑ (suc (suc l)) = trans (cong twoi* (gz-↑ l)) (twoi-mul ((γ {ZComplex}) ↑ l))

γ-pow-↑ : (l : ℕ) -> γ-pow l ≡ (γ {DComplex}) ↑ l
γ-pow-↑ l = trans (cong (λ z -> DComplex ∋ from-whole z) (gz-↑ l)) (from-whole-γ↑ l)

-- ----------------------------------------------------------------------
-- * Extensionality for 4-vectors and 4×4 matrices

private
  vec4-ext : {A : Set} (v w : Vector 4 A) -> ((k : Ix) -> vsel k v ≡ vsel k w) -> v ≡ w
  vec4-ext (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) h = go (h ι0) (h ι1) (h ι2) (h ι3)
    where
      go : a₀ ≡ b₀ -> a₁ ≡ b₁ -> a₂ ≡ b₂ -> a₃ ≡ b₃ ->
           (Vector 4 _ ∋ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) ≡ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])
      go refl refl refl refl = refl

  mat4-ext : {A : Set} (M N : Matrix 4 4 A) -> ((r c : Ix) -> ment r c M ≡ ment r c N) -> M ≡ N
  mat4-ext (Matrix' cs) (Matrix' ds) h =
    cong Matrix' (vec4-ext cs ds (λ c -> vec4-ext (vsel c cs) (vsel c ds) (λ r -> h r c)))

  vsel-map : {A B : Set} (f : A -> B) (k : Ix) (v : Vector 4 A) ->
             vsel k (vector-map f v) ≡ f (vsel k v)
  vsel-map f ι0 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) = refl
  vsel-map f ι1 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) = refl
  vsel-map f ι2 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) = refl
  vsel-map f ι3 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) = refl

  ment-map : {A B : Set} (f : A -> B) (M : Matrix 4 4 A) (r c : Ix) ->
             ment r c (matrix-map f M) ≡ f (ment r c M)
  ment-map f (Matrix' cs) r c =
    trans (cong (vsel r) (vsel-map (vector-map f) c cs)) (vsel-map f r (vsel c cs))

  mcol-η : {A : Set} (M : Matrix 4 4 A) ->
           M ≡ Matrix' (mcol ι0 M ∷ mcol ι1 M ∷ mcol ι2 M ∷ mcol ι3 M ∷ [])
  mcol-η (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl

  mrow-η : {A : Set} (M : Matrix 4 4 A) (r : Ix) ->
           mrow r M ≡ (ment r ι0 M ∷ ment r ι1 M ∷ ment r ι2 M ∷ ment r ι3 M ∷ [])
  mrow-η (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) r = refl

-- The residue matrix that lemma-six computes is the (1,l)-residue
-- matrix of Kopt.Base.
rho1-integral : (l : ℕ) (m : Op) -> rho1-of (integral-matrix l m) ≡ residue1-matrix l m
rho1-integral l m = mat4-ext _ _ ent
  where
    ent : (r c : Ix) -> ment r c (rho1-of (integral-matrix l m)) ≡ ment r c (residue1-matrix l m)
    ent r c =
      trans (ment-map parityℤ[i] (integral-matrix l m) r c)
      (trans (cong parityℤ[i] (ment-map (λ x -> to-whole (x * γ-pow l)) m r c))
      (trans (cong (λ z -> parityℤ[i] (to-whole (ment r c m * z))) (γ-pow-↑ l))
             (sym (entry-res1 m l r c))))

-- ----------------------------------------------------------------------
-- * Enumerations of ℤ₂ 4-vectors

all-v4 : List (Vector 4 Z2)
all-v4 =
    (Even ∷ Even ∷ Even ∷ Even ∷ [])
  ∷ (Odd  ∷ Even ∷ Even ∷ Even ∷ [])
  ∷ (Even ∷ Odd  ∷ Even ∷ Even ∷ [])
  ∷ (Odd  ∷ Odd  ∷ Even ∷ Even ∷ [])
  ∷ (Even ∷ Even ∷ Odd  ∷ Even ∷ [])
  ∷ (Odd  ∷ Even ∷ Odd  ∷ Even ∷ [])
  ∷ (Even ∷ Odd  ∷ Odd  ∷ Even ∷ [])
  ∷ (Odd  ∷ Odd  ∷ Odd  ∷ Even ∷ [])
  ∷ (Even ∷ Even ∷ Even ∷ Odd  ∷ [])
  ∷ (Odd  ∷ Even ∷ Even ∷ Odd  ∷ [])
  ∷ (Even ∷ Odd  ∷ Even ∷ Odd  ∷ [])
  ∷ (Odd  ∷ Odd  ∷ Even ∷ Odd  ∷ [])
  ∷ (Even ∷ Even ∷ Odd  ∷ Odd  ∷ [])
  ∷ (Odd  ∷ Even ∷ Odd  ∷ Odd  ∷ [])
  ∷ (Even ∷ Odd  ∷ Odd  ∷ Odd  ∷ [])
  ∷ (Odd  ∷ Odd  ∷ Odd  ∷ Odd  ∷ [])
  ∷ []

∈-all-v4 : (v : Vector 4 Z2) -> v ∈ˡ all-v4
∈-all-v4 (Even ∷ Even ∷ Even ∷ Even ∷ []) = here
∈-all-v4 (Odd ∷ Even ∷ Even ∷ Even ∷ []) = there here
∈-all-v4 (Even ∷ Odd ∷ Even ∷ Even ∷ []) = there (there here)
∈-all-v4 (Odd ∷ Odd ∷ Even ∷ Even ∷ []) = there (there (there here))
∈-all-v4 (Even ∷ Even ∷ Odd ∷ Even ∷ []) = there (there (there (there here)))
∈-all-v4 (Odd ∷ Even ∷ Odd ∷ Even ∷ []) = there (there (there (there (there here))))
∈-all-v4 (Even ∷ Odd ∷ Odd ∷ Even ∷ []) = there (there (there (there (there (there here)))))
∈-all-v4 (Odd ∷ Odd ∷ Odd ∷ Even ∷ []) =
  there (there (there (there (there (there (there here))))))
∈-all-v4 (Even ∷ Even ∷ Even ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there here)))))))
∈-all-v4 (Odd ∷ Even ∷ Even ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there here))))))))
∈-all-v4 (Even ∷ Odd ∷ Even ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there here)))))))))
∈-all-v4 (Odd ∷ Odd ∷ Even ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there (there here))))))))))
∈-all-v4 (Even ∷ Even ∷ Odd ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there (there
    (there here)))))))))))
∈-all-v4 (Odd ∷ Even ∷ Odd ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there (there
    (there (there here))))))))))))
∈-all-v4 (Even ∷ Odd ∷ Odd ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there (there
    (there (there (there here)))))))))))))
∈-all-v4 (Odd ∷ Odd ∷ Odd ∷ Odd ∷ []) =
  there (there (there (there (there (there (there (there (there (there (there
    (there (there (there (there here))))))))))))))

-- The eight 4-vectors with an even number of odd entries.
even-v4 : List (Vector 4 Z2)
even-v4 = filt (λ v -> odd-count v == Even) all-v4

-- The predicate is given explicitly rather than left to unification: for
-- a literal list `filt` evaluates, so `filt ?f all-v4` is stuck on the
-- metavariable and Agda cannot invert it.
∈-even-v4 : (v : Vector 4 Z2) -> odd-count v ≡ Even -> v ∈ˡ even-v4
∈-even-v4 v h = ∈-filt (λ w -> odd-count w == Even) (∈-all-v4 v) (cong (λ z -> z == Even) h)

-- The four unit vectors.
uv : Ix -> Vector 4 Z2
uv ι0 = Odd ∷ Even ∷ Even ∷ Even ∷ []
uv ι1 = Even ∷ Odd ∷ Even ∷ Even ∷ []
uv ι2 = Even ∷ Even ∷ Odd ∷ Even ∷ []
uv ι3 = Even ∷ Even ∷ Even ∷ Odd ∷ []

unit-v4 : List (Vector 4 Z2)
unit-v4 = uv ι0 ∷ uv ι1 ∷ uv ι2 ∷ uv ι3 ∷ []

-- Is a 4-vector a unit vector?
w1? : Vector 4 Z2 -> Bool
w1? v = (v == uv ι0) ∨ ((v == uv ι1) ∨ ((v == uv ι2) ∨ (v == uv ι3)))

∈-unit-v4 : (v : Vector 4 Z2) -> w1? v ≡ true -> v ∈ˡ unit-v4
∈-unit-v4 v h with ∨-true h
... | inj₁ e = subst (λ w -> w ∈ˡ unit-v4) (sym (==⇒≡ e)) here
... | inj₂ h1 with ∨-true h1
...   | inj₁ e = subst (λ w -> w ∈ˡ unit-v4) (sym (==⇒≡ e)) (there here)
...   | inj₂ h2 with ∨-true h2
...     | inj₁ e = subst (λ w -> w ∈ˡ unit-v4) (sym (==⇒≡ e)) (there (there here))
...     | inj₂ e = subst (λ w -> w ∈ˡ unit-v4) (sym (==⇒≡ e)) (there (there (there here)))

-- ----------------------------------------------------------------------
-- * Enumerations of ℤ₂ 4×4 matrices

private
  ∈-concatMap : {A B : Set} (f : A -> List B) {x : A} {xs : List A} {y : B} ->
                x ∈ˡ xs -> y ∈ˡ f x -> y ∈ˡ List.concatMap f xs
  ∈-concatMap f (here {xs = xs}) hy = ∈-++ˡ (List.concatMap f xs) hy
  ∈-concatMap f (there {y = z} hx) hy = ∈-++ʳ (f z) (∈-concatMap f hx hy)

-- All matrices whose columns come from the given list.
mats-from : List (Vector 4 Z2) -> List (Matrix 4 4 Z2)
mats-from vs =
  List.concatMap (λ c₀ ->
    List.concatMap (λ c₁ ->
      List.concatMap (λ c₂ ->
        List.map (λ c₃ -> Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) vs) vs) vs) vs

∈-mats-from : (vs : List (Vector 4 Z2)) (c₀ c₁ c₂ c₃ : Vector 4 Z2) ->
              c₀ ∈ˡ vs -> c₁ ∈ˡ vs -> c₂ ∈ˡ vs -> c₃ ∈ˡ vs ->
              (Matrix 4 4 Z2 ∋ Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) ∈ˡ mats-from vs
∈-mats-from vs c₀ c₁ c₂ c₃ m₀ m₁ m₂ m₃ =
  ∈-concatMap (λ x₀ -> List.concatMap (λ x₁ -> List.concatMap (λ x₂ ->
                 List.map (λ x₃ -> Matrix' (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) vs) vs) vs) m₀
   (∈-concatMap (λ x₁ -> List.concatMap (λ x₂ ->
                 List.map (λ x₃ -> Matrix' (c₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) vs) vs) m₁
    (∈-concatMap (λ x₂ -> List.map (λ x₃ -> Matrix' (c₀ ∷ c₁ ∷ x₂ ∷ x₃ ∷ [])) vs) m₂
      (∈-map (λ x₃ -> Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ x₃ ∷ [])) m₃)))

-- ----------------------------------------------------------------------
-- * The conditions that unitarity imposes on ρˡ₁

even-rows? : Matrix 4 4 Z2 -> Bool
even-rows? M = (odd-count (mrow ι0 M) == Even) ∧ ((odd-count (mrow ι1 M) == Even)
             ∧ ((odd-count (mrow ι2 M) == Even) ∧ (odd-count (mrow ι3 M) == Even)))

col-meets? : Matrix 4 4 Z2 -> Bool
col-meets? M = (meet-count (mcol ι0 M) (mcol ι1 M) == Even)
             ∧ ((meet-count (mcol ι0 M) (mcol ι2 M) == Even)
             ∧ ((meet-count (mcol ι0 M) (mcol ι3 M) == Even)
             ∧ ((meet-count (mcol ι1 M) (mcol ι2 M) == Even)
             ∧ ((meet-count (mcol ι1 M) (mcol ι3 M) == Even)
             ∧ (meet-count (mcol ι2 M) (mcol ι3 M) == Even)))))

row-meets? : Matrix 4 4 Z2 -> Bool
row-meets? M = (meet-count (mrow ι0 M) (mrow ι1 M) == Even)
             ∧ ((meet-count (mrow ι0 M) (mrow ι2 M) == Even)
             ∧ ((meet-count (mrow ι0 M) (mrow ι3 M) == Even)
             ∧ ((meet-count (mrow ι1 M) (mrow ι2 M) == Even)
             ∧ ((meet-count (mrow ι1 M) (mrow ι3 M) == Even)
             ∧ (meet-count (mrow ι2 M) (mrow ι3 M) == Even)))))

zero-mat : Matrix 4 4 Z2
zero-mat = Matrix' (zv ∷ zv ∷ zv ∷ zv ∷ [])
  where
    zv : Vector 4 Z2
    zv = Even ∷ Even ∷ Even ∷ Even ∷ []

nonzero? : Matrix 4 4 Z2 -> Bool
nonzero? M = not (M == zero-mat)

unit-rows? : Matrix 4 4 Z2 -> Bool
unit-rows? M = w1? (mrow ι0 M) ∧ (w1? (mrow ι1 M) ∧ (w1? (mrow ι2 M) ∧ w1? (mrow ι3 M)))

-- The residue matrices that a unitary of lde l = k+1 can have.
pos-ok? : Matrix 4 4 Z2 -> Bool
pos-ok? M = even-rows? M ∧ (col-meets? M ∧ (row-meets? M ∧ nonzero? M))

pos-cand : List (Matrix 4 4 Z2)
pos-cand = filt pos-ok? (mats-from even-v4)

-- The residue matrices that a unitary of lde 0 can have: the 24
-- permutation matrices over ℤ₂.
zero-cand : List (Matrix 4 4 Z2)
zero-cand = filt unit-rows? (mats-from unit-v4)

-- ----------------------------------------------------------------------
-- * The two exhaustive checks
--
-- The search of lemma-six is run by the type checker on every element
-- of the two lists. Together with the derivations above this is the
-- proof of Lemma IV.1.

search-of : Matrix 4 4 Z2 -> Maybe Search.Found
search-of M = Search.search-x all-perms (Search.cols-table (rows-4 M))

search-i-of : Matrix 4 4 Z2 -> Maybe Tuple4
search-i-of M = Search.search-i all-perms (Search.encode-rows (rows-4 M))

found? : Maybe Search.Found -> Bool
found? nothing = false
found? (just (p , x , y)) = not (p == I)

found-i? : Maybe Tuple4 -> Bool
found-i? nothing = false
found-i? (just x) = true

-- At lde > 0: the search finds a pattern, and it is not (i).
pos-check : all-of (λ M -> found? (search-of M)) pos-cand ≡ true
pos-check = refl

-- At lde 0: the search of the lde-0 branch succeeds.
zero-check : all-of (λ M -> found-i? (search-i-of M)) zero-cand ≡ true
zero-check = refl

-- ----------------------------------------------------------------------
-- * From unitarity to the conditions
-- ** lde l = k+1

module _ (U : Op) (hu : IsUnitary U) (k : ℕ) (hl : lde U ≡ suc k) where
  private
    le : lde U Nat.≤ suc k
    le = NatP.≤-reflexive hl

    R : Matrix 4 4 Z2
    R = residue1-matrix (suc k) U

    ev-col : (c : Ix) -> odd-count (mcol c R) ≡ Even
    ev-col c = lemma-IV-2-col U k (u-left hu) le c

    ev-row : (r : Ix) -> odd-count (mrow r R) ≡ Even
    ev-row r = lemma-IV-2-row U k (u-right hu) le r

    mt-col : (r c : Ix) -> ix/= r c ≡ true -> meet-count (mcol c R) (mcol r R) ≡ Even
    mt-col r c d = lemma-IV-3-col U (suc k) (u-left hu) le r c d

    mt-row : (r c : Ix) -> ix/= r c ≡ true -> meet-count (mrow c R) (mrow r R) ≡ Even
    mt-row r c d = lemma-IV-3-row U (suc k) (u-right hu) le r c d

    eqT : {b : Z2} -> b ≡ Even -> (b == Even) ≡ true
    eqT h = cong (λ z -> z == Even) h

    nz-R : nonzero? R ≡ true
    nz-R = go (res1-has-odd U k hl)
      where
        zero-ment : (r c : Ix) -> ment r c zero-mat ≡ Even
        zero-ment ι0 ι0 = refl
        zero-ment ι0 ι1 = refl
        zero-ment ι0 ι2 = refl
        zero-ment ι0 ι3 = refl
        zero-ment ι1 ι0 = refl
        zero-ment ι1 ι1 = refl
        zero-ment ι1 ι2 = refl
        zero-ment ι1 ι3 = refl
        zero-ment ι2 ι0 = refl
        zero-ment ι2 ι1 = refl
        zero-ment ι2 ι2 = refl
        zero-ment ι2 ι3 = refl
        zero-ment ι3 ι0 = refl
        zero-ment ι3 ι1 = refl
        zero-ment ι3 ι2 = refl
        zero-ment ι3 ι3 = refl
        odd≢even : Odd ≡ Even -> ⊥
        odd≢even ()
        go : Σ[ r ∈ Ix ] Σ[ c ∈ Ix ] ment r c R ≡ Odd -> nonzero? R ≡ true
        go (r , c , ho) with R == zero-mat in eqz
        ... | false = refl
        ... | true = ⊥-elim (odd≢even (trans (sym ho)
                              (trans (cong (ment r c) (==⇒≡ eqz)) (zero-ment r c))))

    ok : pos-ok? R ≡ true
    ok = ∧-intro (∧-intro (eqT (ev-row ι0)) (∧-intro (eqT (ev-row ι1))
                    (∧-intro (eqT (ev-row ι2)) (eqT (ev-row ι3)))))
         (∧-intro (∧-intro (eqT (mt-col ι1 ι0 refl)) (∧-intro (eqT (mt-col ι2 ι0 refl))
                    (∧-intro (eqT (mt-col ι3 ι0 refl)) (∧-intro (eqT (mt-col ι2 ι1 refl))
                      (∧-intro (eqT (mt-col ι3 ι1 refl)) (eqT (mt-col ι3 ι2 refl)))))))
         (∧-intro (∧-intro (eqT (mt-row ι1 ι0 refl)) (∧-intro (eqT (mt-row ι2 ι0 refl))
                    (∧-intro (eqT (mt-row ι3 ι0 refl)) (∧-intro (eqT (mt-row ι2 ι1 refl))
                      (∧-intro (eqT (mt-row ι3 ι1 refl)) (eqT (mt-row ι3 ι2 refl)))))))
                  nz-R))

    mem-all : R ∈ˡ mats-from even-v4
    mem-all = subst (λ N -> N ∈ˡ mats-from even-v4) (sym (mcol-η R))
                    (∈-mats-from even-v4 (mcol ι0 R) (mcol ι1 R) (mcol ι2 R) (mcol ι3 R)
                                 (∈-even-v4 _ (ev-col ι0)) (∈-even-v4 _ (ev-col ι1))
                                 (∈-even-v4 _ (ev-col ι2)) (∈-even-v4 _ (ev-col ι3)))

  -- The search of lemma-six, run on ρˡ₁(U), finds a pattern ≠ (i).
  pos-found : found? (search-of (residue1-matrix (suc k) U)) ≡ true
  pos-found = all-of-∈ (λ M -> found? (search-of M)) pos-cand pos-check (∈-filt pos-ok? mem-all ok)

-- ----------------------------------------------------------------------
-- ** lde 0
--
-- Here the norms are needed: Σₖ ∥Xₖ∥² = 1 with ∥Xₖ∥² a natural number
-- forces exactly one Xₖ to be odd.

private
  -- X·X† = ∥X∥².
  norm-adj : (X : ZComplex) -> X * (X †) ≡ Cplx (normℤ[i] X) 0#
  norm-adj (Cplx a b) = cong₂ Cplx e1 e2
    where
      open ℤS
      e1 : a * a - b * (- b) ≡ a * a + b * b
      e1 = solve 2 (λ x y -> x :* x :- y :* (:- y) := x :* x :+ y :* y) refl a b
      e2 : a * (- b) + b * a ≡ 0#
      e2 = solve 2 (λ x y -> x :* (:- y) :+ y :* x := con (+ 0)) refl a b

  sq-nat : (a : ℤ) -> Σ[ n ∈ ℕ ] a * a ≡ + n
  sq-nat (+ m) = m Nat.* m , sym (IntP.pos-* m m)
  sq-nat -[1+ m ] = suc m Nat.* suc m ,
    trans (ℤS.solve 1 (λ x -> (:- x) :* (:- x) := x :* x) refl (+ suc m))
          (sym (IntP.pos-* (suc m) (suc m)))
    where open ℤS

  norm-nat : (X : ZComplex) -> Σ[ n ∈ ℕ ] normℤ[i] X ≡ + n
  norm-nat (Cplx a b) with sq-nat a | sq-nat b
  ... | (p , ea) | (q , eb) =
        (p Nat.+ q) , trans (cong₂ (λ u v -> u + v) ea eb) (sym (IntP.pos-+ p q))

  -- Four naturals summing to zero are all zero.
  sum0 : (n₀ n₁ n₂ n₃ : ℕ) -> n₀ Nat.+ (n₁ Nat.+ (n₂ Nat.+ n₃)) ≡ 0 ->
         (n₀ ≡ 0) × ((n₁ ≡ 0) × ((n₂ ≡ 0) × (n₃ ≡ 0)))
  sum0 zero zero zero zero e = refl , refl , refl , refl
  sum0 zero zero zero (suc n) ()
  sum0 zero zero (suc n) n₃ ()
  sum0 zero (suc n) n₂ n₃ ()
  sum0 (suc n) n₁ n₂ n₃ ()

  sum0₃ : (n₁ n₂ n₃ : ℕ) -> n₁ Nat.+ (n₂ Nat.+ n₃) ≡ 0 -> (n₁ ≡ 0) × ((n₂ ≡ 0) × (n₃ ≡ 0))
  sum0₃ zero zero zero e = refl , refl , refl
  sum0₃ zero zero (suc n) ()
  sum0₃ zero (suc n) n₃ ()
  sum0₃ (suc n) n₂ n₃ ()

  sum0₂ : (n₂ n₃ : ℕ) -> n₂ Nat.+ n₃ ≡ 0 -> (n₂ ≡ 0) × (n₃ ≡ 0)
  sum0₂ zero zero e = refl , refl
  sum0₂ zero (suc n) ()
  sum0₂ (suc n) n₃ ()

  -- The parity of a natural number, as the parity of the integer.
  pZ : ℕ -> Z2
  pZ m = parity (+ m)

  -- Four naturals summing to one give a unit vector of parities.
  sum1-w1 : (n₀ n₁ n₂ n₃ : ℕ) -> n₀ Nat.+ (n₁ Nat.+ (n₂ Nat.+ n₃)) ≡ 1 ->
            w1? (pZ n₀ ∷ pZ n₁ ∷ pZ n₂ ∷ pZ n₃ ∷ []) ≡ true
  sum1-w1 (suc n₀) n₁ n₂ n₃ e with sum0 n₀ n₁ n₂ n₃ (NatP.suc-injective e)
  ... | refl , refl , refl , refl = refl
  sum1-w1 zero (suc n₁) n₂ n₃ e with sum0₃ n₁ n₂ n₃ (NatP.suc-injective e)
  ... | refl , refl , refl = refl
  sum1-w1 zero zero (suc n₂) n₃ e with sum0₂ n₂ n₃ (NatP.suc-injective e)
  ... | refl , refl = refl
  sum1-w1 zero zero zero (suc n₃) e with NatP.suc-injective e
  ... | refl = refl
  sum1-w1 zero zero zero zero ()

  congS4 : {A : Set} {{_ : SemiRing A}} {p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : A} ->
           p₀ ≡ q₀ -> p₁ ≡ q₁ -> p₂ ≡ q₂ -> p₃ ≡ q₃ ->
           sum4 p₀ p₁ p₂ p₃ ≡ sum4 q₀ q₁ q₂ q₃
  congS4 refl refl refl refl = refl

  congV4 : {A : Set} {p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : A} ->
           p₀ ≡ q₀ -> p₁ ≡ q₁ -> p₂ ≡ q₂ -> p₃ ≡ q₃ ->
           (Vector 4 A ∋ (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ [])) ≡ (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ [])
  congV4 refl refl refl refl = refl

-- Four Gaussian integers whose norms sum to 1 have exactly one odd
-- one: the vector of their parities is a unit vector.
unit-of-norm-1 : (X₀ X₁ X₂ X₃ : ZComplex) ->
                 sum4 (X₀ * (X₀ †)) (X₁ * (X₁ †)) (X₂ * (X₂ †)) (X₃ * (X₃ †)) ≡ 1# ->
                 w1? (parityℤ[i] X₀ ∷ parityℤ[i] X₁ ∷ parityℤ[i] X₂ ∷ parityℤ[i] X₃ ∷ []) ≡ true
unit-of-norm-1 X₀ X₁ X₂ X₃ h = trans (cong w1? parities) (sum1-w1 m₀ m₁ m₂ m₃ sum-one)
  where
    n : ZComplex -> ℤ
    n = normℤ[i]
    m₀ = proj₁ (norm-nat X₀)
    m₁ = proj₁ (norm-nat X₁)
    m₂ = proj₁ (norm-nat X₂)
    m₃ = proj₁ (norm-nat X₃)
    e₀ = proj₂ (norm-nat X₀)
    e₁ = proj₂ (norm-nat X₁)
    e₂ = proj₂ (norm-nat X₂)
    e₃ = proj₂ (norm-nat X₃)
    -- the real parts add up to 1
    reals : n X₀ + (n X₁ + (n X₂ + n X₃)) ≡ 1#
    reals = re-eq (trans (sym (congS4 (norm-adj X₀) (norm-adj X₁) (norm-adj X₂) (norm-adj X₃))) h)
    sum-pos : (+ (m₀ Nat.+ (m₁ Nat.+ (m₂ Nat.+ m₃)))) ≡ (+ 1)
    sum-pos = trans (trans (IntP.pos-+ m₀ (m₁ Nat.+ (m₂ Nat.+ m₃)))
                     (trans (cong (λ z -> (+ m₀) + z) (IntP.pos-+ m₁ (m₂ Nat.+ m₃)))
                            (cong (λ z -> (+ m₀) + ((+ m₁) + z)) (IntP.pos-+ m₂ m₃))))
                    (trans (sym (cong₂ (λ u v -> u + v) e₀
                                  (cong₂ (λ u v -> u + v) e₁ (cong₂ (λ u v -> u + v) e₂ e₃))))
                           reals)
    sum-one : m₀ Nat.+ (m₁ Nat.+ (m₂ Nat.+ m₃)) ≡ 1
    sum-one = IntP.+-injective sum-pos
    parities : (Vector 4 Z2 ∋ (parityℤ[i] X₀ ∷ parityℤ[i] X₁ ∷ parityℤ[i] X₂ ∷ parityℤ[i] X₃ ∷ []))
                 ≡ (pZ m₀ ∷ pZ m₁ ∷ pZ m₂ ∷ pZ m₃ ∷ [])
    parities = congV4 (par X₀ e₀) (par X₁ e₁) (par X₂ e₂) (par X₃ e₃)
      where
        par : (X : ZComplex) {m : ℕ} -> normℤ[i] X ≡ + m -> parityℤ[i] X ≡ pZ m
        par X e = trans (lemma-II-5 X) (cong parity e)

-- ----------------------------------------------------------------------
-- ** The lde-0 conditions

module _ (U : Op) (hu : IsUnitary U) (hl : lde U ≡ 0) where
  private
    le : lde U Nat.≤ 0
    le = NatP.≤-reflexive hl

    R₀ : Matrix 4 4 Z2
    R₀ = residue1-matrix 0 U

    E : Ix -> Ix -> ZComplex
    E = int-entry U 0 le

    -- Every column of ρ⁰₁(U) is a unit vector.
    w1-col : (c : Ix) -> w1? (mcol c R₀) ≡ true
    w1-col c = trans (cong w1? colv) (unit-of-norm-1 (E ι0 c) (E ι1 c) (E ι2 c) (E ι3 c)
                                                    (col-norm-ints U 0 le (u-left hu) c))
      where
        colv : mcol c R₀ ≡ (parityℤ[i] (E ι0 c) ∷ parityℤ[i] (E ι1 c)
                           ∷ parityℤ[i] (E ι2 c) ∷ parityℤ[i] (E ι3 c) ∷ [])
        colv = trans (vec4-η (mcol c R₀))
                     (congV4 (res1-entry U 0 le ι0 c) (res1-entry U 0 le ι1 c)
                             (res1-entry U 0 le ι2 c) (res1-entry U 0 le ι3 c))

    -- and so is every row.
    w1-row : (r : Ix) -> w1? (mrow r R₀) ≡ true
    w1-row r = trans (cong w1? rowv) (unit-of-norm-1 (E r ι0) (E r ι1) (E r ι2) (E r ι3)
                                                    (row-norm-ints U 0 le (u-right hu) r))
      where
        rowv : mrow r R₀ ≡ (parityℤ[i] (E r ι0) ∷ parityℤ[i] (E r ι1)
                           ∷ parityℤ[i] (E r ι2) ∷ parityℤ[i] (E r ι3) ∷ [])
        rowv = trans (mrow-η R₀ r)
                     (congV4 (res1-entry U 0 le r ι0) (res1-entry U 0 le r ι1)
                             (res1-entry U 0 le r ι2) (res1-entry U 0 le r ι3))

    mem-all : R₀ ∈ˡ mats-from unit-v4
    mem-all = subst (λ N -> N ∈ˡ mats-from unit-v4) (sym (mcol-η R₀))
                    (∈-mats-from unit-v4 (mcol ι0 R₀) (mcol ι1 R₀) (mcol ι2 R₀) (mcol ι3 R₀)
                                 (∈-unit-v4 _ (w1-col ι0)) (∈-unit-v4 _ (w1-col ι1))
                                 (∈-unit-v4 _ (w1-col ι2)) (∈-unit-v4 _ (w1-col ι3)))

    ok : unit-rows? R₀ ≡ true
    ok = ∧-intro (w1-row ι0) (∧-intro (w1-row ι1) (∧-intro (w1-row ι2) (w1-row ι3)))

  -- The lde-0 branch of lemma-six succeeds on ρ⁰₁(U).
  zero-found : found-i? (search-i-of (residue1-matrix 0 U)) ≡ true
  zero-found = all-of-∈ (λ M -> found-i? (search-i-of M)) zero-cand zero-check (∈-filt unit-rows? mem-all ok)

-- ----------------------------------------------------------------------
-- * Lemma IV.1
--
-- The defining equations of patof: level-at unfolds to the auxiliary
-- functions of Kopt.Patterns.Level applied to the outcome of the
-- search, and rho1-integral identifies the matrix the search is run on.

level-at-suc : (A : Op) (k : ℕ) ->
               level-at (suc k) A
                 ≡ Level.level-from-s (suc k) (search-of (residue1-matrix (suc k) A))
                                      (integral-matrix (suc k) A)
level-at-suc A k =
  cong (λ M -> Level.level-from-s (suc k)
                 (Search.search-x all-perms (Search.cols-table (rows-4 M)))
                 (integral-matrix (suc k) A))
       (rho1-integral (suc k) A)

level-at-zero : (A : Op) ->
                level-at 0 A
                  ≡ Level.level-from-0 (search-i-of (residue1-matrix 0 A)) (integral-matrix 0 A)
level-at-zero A =
  cong (λ M -> Level.level-from-0 (Search.search-i all-perms (Search.encode-rows (rows-4 M)))
                                  (integral-matrix 0 A))
       (rho1-integral 0 A)

private
  not-I-aux : (l : ℕ) (W : Matrix 4 4 ZComplex) (s : Maybe Search.Found) -> found? s ≡ true ->
              ¬ (patof-of (Level.level-from-s (suc l) s W) ≡ just I)
  not-I-aux l W nothing h e = ⊥-elim (false≢true h)
  not-I-aux l W (just (p , x , y)) h e =
    true≢false (trans (sym h) (cong (λ q -> not (q == I)) (just-inj e)))

  at-0-aux : (W : Matrix 4 4 ZComplex) (s : Maybe Tuple4) -> found-i? s ≡ true ->
             patof-of (Level.level-from-0 s W) ≡ just I
  at-0-aux W nothing h = ⊥-elim (false≢true h)
  at-0-aux W (just x) h = refl

  just-aux-s : (l : ℕ) (W : Matrix 4 4 ZComplex) (s : Maybe Search.Found) -> found? s ≡ true ->
               Σ[ ld ∈ LevelData ] Level.level-from-s (suc l) s W ≡ just ld
  just-aux-s l W nothing h = ⊥-elim (false≢true h)
  just-aux-s l W (just (p , x , y)) h =
    level-data (suc l) p x y (permute-matrix x y (rho2-of W)) , refl

  just-aux-0 : (W : Matrix 4 4 ZComplex) (s : Maybe Tuple4) -> found-i? s ≡ true ->
               Σ[ ld ∈ LevelData ] Level.level-from-0 s W ≡ just ld
  just-aux-0 W nothing h = ⊥-elim (false≢true h)
  just-aux-0 W (just x) h =
    level-data 0 I x Search.identity-perm
               (permute-matrix x Search.identity-perm (rho2-of W)) , refl

-- At lde 0 the pattern is (i).
patof-at-0 : (A : Op) -> IsUnitary A -> lde A ≡ 0 -> patof A ≡ just I
patof-at-0 A hu hl =
  trans (trans (cong (λ n -> patof-of (level-at n A)) hl) (cong patof-of (level-at-zero A)))
        (at-0-aux (integral-matrix 0 A) (search-i-of (residue1-matrix 0 A)) (zero-found A hu hl))

-- At lde > 0 the pattern is not (i).
patof-not-I : (A : Op) -> IsUnitary A -> (k : ℕ) -> lde A ≡ suc k -> ¬ (patof A ≡ just I)
patof-not-I A hu k hl e =
  not-I-aux k (integral-matrix (suc k) A) (search-of (residue1-matrix (suc k) A))
            (pos-found A hu k hl)
            (trans (sym (trans (cong (λ n -> patof-of (level-at n A)) hl)
                               (cong patof-of (level-at-suc A k)))) e)

-- Lemma IV.1, the pattern-(i) half: A has pattern (i) if and only if
-- lde A = 0. This is Kopt.OptSteps.Lemma-IV-1-I for a unitary A.
lemma-IV-1-I : (A : Op) -> IsUnitary A ->
               (lde A ≡ 0 -> patof A ≡ just I) × (patof A ≡ just I -> lde A ≡ 0)
lemma-IV-1-I A hu = patof-at-0 A hu , back
  where
    back : patof A ≡ just I -> lde A ≡ 0
    back e = go (lde A) refl
      where
        go : (n : ℕ) -> lde A ≡ n -> lde A ≡ 0
        go zero h = h
        go (suc k) h = ⊥-elim (patof-not-I A hu k h e)

-- Lemma IV.1: every unitary over 𝔻[i] has a pattern, i.e. lemma-six
-- returns a pattern and two permutation circuits.
level-of-just : (A : Op) -> IsUnitary A -> Σ[ ld ∈ LevelData ] level-of A ≡ just ld
level-of-just A hu = go (lde A) refl
  where
    go : (n : ℕ) -> lde A ≡ n -> Σ[ ld ∈ LevelData ] level-of A ≡ just ld
    go zero h = fix h (just-aux-0 (integral-matrix 0 A) (search-i-of (residue1-matrix 0 A))
                                  (zero-found A hu h))
      where
        fix : lde A ≡ 0 -> Σ[ ld ∈ LevelData ] Level.level-from-0 (search-i-of (residue1-matrix 0 A))
                                                (integral-matrix 0 A) ≡ just ld ->
              Σ[ ld ∈ LevelData ] level-of A ≡ just ld
        fix h0 (ld , eld) = ld , trans (trans (cong (λ n -> level-at n A) h0) (level-at-zero A)) eld
    go (suc k) h = fix h (just-aux-s k (integral-matrix (suc k) A)
                                     (search-of (residue1-matrix (suc k) A))
                                     (pos-found A hu k h))
      where
        fix : lde A ≡ suc k ->
              Σ[ ld ∈ LevelData ] Level.level-from-s (suc k) (search-of (residue1-matrix (suc k) A))
                                    (integral-matrix (suc k) A) ≡ just ld ->
              Σ[ ld ∈ LevelData ] level-of A ≡ just ld
        fix hs (ld , eld) = ld , trans (trans (cong (λ n -> level-at n A) hs) (level-at-suc A k)) eld

lemma-IV-1 : (A : Op) -> IsUnitary A ->
             Σ[ p ∈ SixCases ] Σ[ L ∈ Circuit ] Σ[ R ∈ Circuit ] lemma-six A ≡ just (p , L , R)
lemma-IV-1 A hu = go (level-of-just A hu)
  where
    go : Σ[ ld ∈ LevelData ] level-of A ≡ just ld ->
         Σ[ p ∈ SixCases ] Σ[ L ∈ Circuit ] Σ[ R ∈ Circuit ] lemma-six A ≡ just (p , L , R)
    go (ld , e) = lev-pat ld , lev-lcir ld , lev-rcir ld , cong lemma-six-of e

-- Every unitary has a pattern.
patof-just : (A : Op) -> IsUnitary A -> Σ[ p ∈ SixCases ] patof A ≡ just p
patof-just A hu = go (level-of-just A hu)
  where
    go : Σ[ ld ∈ LevelData ] level-of A ≡ just ld -> Σ[ p ∈ SixCases ] patof A ≡ just p
    go (ld , e) = lev-pat ld , cong patof-of e
