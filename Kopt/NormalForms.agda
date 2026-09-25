-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the residue-level content of Lemmas V.3, V.4 and V.6, as exhaustive
-- checks that the *type checker* runs, in the style of gp-check-all of
-- Kopt.Optimality: a boolean test over an explicit finite list, proved
-- by refl, together with the membership lemmas that turn it into a
-- universally quantified statement.
--
-- What is and is not covered
-- --------------------------
--
-- All three lemmas are proved in the paper by enumerating residue
-- data, and that enumeration is what is verified here. The step from
-- an arbitrary operator to its residue data -- that ρˡ₁ of an operator
-- is, up to row and column permutations, the pattern matrix of its
-- pattern (Lemma IV.1), and that ρˡ₂ of an operator brought into
-- normal form by the refinements of Section IV B is one of the
-- matrices listed by Kopt.Patterns.normal-forms -- is the correctness
-- of lemma-six and of refine, which is checked by execution on the
-- authors' data set (Test.KoptNormRun, Test.KoptSynthRun) and is not
-- proved. So what follows is exactly the finite half of each lemma.

{-# OPTIONS --without-K --safe #-}

module Kopt.NormalForms where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)
open import Relation.Nullary using (¬_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Patterns
open import Kopt.Descent
  using (_∈ˡ_ ; here ; there ; all-of ; all-of-∈ ; pairs ; ∈-pairs ; ∈-++ˡ ; ∧-true
        ; fig1-drop ; fig1-keep)

private
  false≢true : false ≡ true -> ⊥
  false≢true ()

  not-true : {b : Bool} -> not b ≡ true -> b ≡ false
  not-true {false} _ = refl
  not-true {true} ()

-- Every one of the seven cases occurs in the list six-cases, so an
-- exhaustive check over that list applies to all of them.
∈-six-cases : (p : SixCases) -> p ∈ˡ six-cases
∈-six-cases I = here
∈-six-cases II = there here
∈-six-cases III = there (there here)
∈-six-cases IV = there (there (there here))
∈-six-cases V = there (there (there (there here)))
∈-six-cases VI = there (there (there (there (there here))))
∈-six-cases IVt = there (there (there (there (there (there here)))))

-- ----------------------------------------------------------------------
-- * A permutation invariant of the ℤ₂ patterns
--
-- The pattern of an operator is only defined up to permutations of the
-- rows and of the columns, so to *exclude* a pattern one needs a
-- quantity that is constant on each orbit. The sum of the squares of
-- the row weights, together with the same for the columns, is such a
-- quantity, and it tells the seven pattern matrices apart:
--
--     (i) (4,4)   (ii) (8,8)   (iii) (16,16)   (iv) (32,16)
--     (iv)ᵀ (16,32)   (v) (40,40)   (vi) (64,64).
--
-- Both facts are checked rather than proved: the invariance over the
-- 7·24·24 permuted pattern matrices, and the distinctness over the
-- 7·7 pairs. That is all the arguments below need.

private
  bit : Z2 -> ℕ
  bit Even = 0
  bit Odd = 1

  weight : Vector 4 Z2 -> ℕ
  weight (a ∷ b ∷ c ∷ d ∷ []) = bit a Nat.+ (bit b Nat.+ (bit c Nat.+ bit d))

  sq : ℕ -> ℕ
  sq n = n Nat.* n

  wsq : Vector 4 (Vector 4 Z2) -> ℕ
  wsq (a ∷ b ∷ c ∷ d ∷ []) =
    sq (weight a) Nat.+ (sq (weight b) Nat.+ (sq (weight c) Nat.+ sq (weight d)))

inv : Matrix 4 4 Z2 -> ℕ × ℕ
inv m = wsq (rows-4 m) , wsq (unMatrix m)

inv-eq : ℕ × ℕ -> ℕ × ℕ -> Bool
inv-eq (a , b) (c , d) = (a Nat.≡ᵇ c) ∧ (b Nat.≡ᵇ d)

-- The invariant of each of the seven pattern matrices, tabulated (so
-- that the enumerations below do not recompute it).
pat-inv : SixCases -> ℕ × ℕ
pat-inv I = 4 , 4
pat-inv II = 8 , 8
pat-inv III = 16 , 16
pat-inv IV = 32 , 16
pat-inv IVt = 16 , 32
pat-inv V = 40 , 40
pat-inv VI = 64 , 64

pat-inv-ok : (p : SixCases) -> inv (pattern-matrix p) ≡ pat-inv p
pat-inv-ok I = refl
pat-inv-ok II = refl
pat-inv-ok III = refl
pat-inv-ok IV = refl
pat-inv-ok IVt = refl
pat-inv-ok V = refl
pat-inv-ok VI = refl

private
  inv-perm-one : SixCases -> Bool
  inv-perm-one p =
    all-of (λ xy -> inv-eq (inv (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix p)))
                           (pat-inv p))
           (pairs all-perms all-perms)

  -- 7 · 576 permuted pattern matrices.
  inv-perm-ok : all-of inv-perm-one six-cases ≡ true
  inv-perm-ok = refl

  -- The seven invariants are pairwise distinct.
  inv-distinct : all-of (λ pq -> if proj₁ pq == proj₂ pq then true
                                 else not (inv-eq (pat-inv (proj₁ pq)) (pat-inv (proj₂ pq))))
                        (pairs six-cases six-cases) ≡ true
  inv-distinct = refl

inv-permuted : (p : SixCases) (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
               inv-eq (inv (permute-matrix x y (pattern-matrix p))) (pat-inv p) ≡ true
inv-permuted p x y hx hy =
  all-of-∈ (λ xy -> inv-eq (inv (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix p)))
                           (pat-inv p))
           (pairs all-perms all-perms)
           (all-of-∈ inv-perm-one six-cases inv-perm-ok (∈-six-cases p))
           (∈-pairs hx hy)

-- A matrix whose invariant differs from that of the pattern matrix of
-- p is not a row-and-column permutation of it, i.e. does not have
-- pattern p.
not-orbit : (Z : Matrix 4 4 Z2) (p : SixCases) ->
            inv-eq (inv Z) (pat-inv p) ≡ false ->
            (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
            ¬ (Z ≡ permute-matrix x y (pattern-matrix p))
not-orbit Z p hne x y hx hy e =
  false≢true (trans (sym hne)
    (subst (λ W -> inv-eq (inv W) (pat-inv p) ≡ true) (sym e) (inv-permuted p x y hx hy)))

-- ----------------------------------------------------------------------
-- * Lemma V.4 (pattern locking), at the level of the residues
--
-- The proof of the paper goes through 1-ascents. Let B have lde m and
-- let K₁ act on its rows after a generalized permutation. By the four
-- K cases of Section II C, an entry of K₁B in a row of a pair has
--
--     ρ^{m+1}₁ = ρᵐ₁(first row of the pair) ⊕ ρᵐ₁(second row),
--
-- since ρ^{m+1}₁((x ± y)/γ) is the parity of γᵐx ± γᵐy. So ρ^{m+1}₁(K₁B)
-- has the two rows of each pair equal to the sum of the two rows of
-- the corresponding pair of ρᵐ₁(B), and the lde goes up exactly when
-- that matrix is nonzero: an lde-raising K gate "doubles the odd
-- entries".
--
-- Enumerating the 24·24 row-and-column permutations of each of the
-- seven pattern matrices therefore enumerates all K-count-1 1-ascents
-- out of each pattern -- the row permutation is the choice of the two
-- pairs of rows that K acts on, and the phases of the generalized
-- permutation do not affect ρ₁ -- and the check below verifies that
-- the pattern reached is always the source of an undashed edge of
-- Figure 1 into the pattern one started from.

-- ρˡ₁ of K₁·B from ρ^{l-1}₁(B) (a K gate acting on the left), and the
-- mirror image (a K gate acting on the right).
double-rows : Matrix 4 4 Z2 -> Matrix 4 4 Z2
double-rows m = Matrix' (vector-transpose (u ∷ u ∷ v ∷ v ∷ []))
  where
    rs : Vector 4 (Vector 4 Z2)
    rs = rows-4 m
    u v : Vector 4 Z2
    u = vector-zipwith _+_ (vsel4 rs 0) (vsel4 rs 1)
    v = vector-zipwith _+_ (vsel4 rs 2) (vsel4 rs 3)

double-cols : Matrix 4 4 Z2 -> Matrix 4 4 Z2
double-cols m = matrix-transpose (double-rows (matrix-transpose m))

z2-zero : Matrix 4 4 Z2
z2-zero = matrix4x4 (Even , Even , Even , Even) (Even , Even , Even , Even)
                    (Even , Even , Even , Even) (Even , Even , Even , Even)

private
  -- Z is the ρˡ₁ of the source of a 1-descent whose target has pattern
  -- T: every pattern S that Figure 1 does not allow is excluded.
  v4-ok-one : SixCases -> Matrix 4 4 Z2 -> Bool
  v4-ok-one T Z =
    if Z == z2-zero then true
    else all-of (λ S -> if fig1-drop S T then true else not (inv-eq (inv Z) (pat-inv S)))
                six-cases

  v4-case : SixCases -> Tuple4 × Tuple4 -> Bool
  v4-case T xy =
    v4-ok-one T (double-rows (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix T)))
      ∧ v4-ok-one T (double-cols (permute-matrix (proj₁ xy) (proj₂ xy) (pattern-matrix T)))

  v4-one : SixCases -> Bool
  v4-one T = all-of (v4-case T) (pairs all-perms all-perms)

  -- 7 · 576 · 2 one-K-gate 1-ascents.
  v4-ok : all-of v4-one six-cases ≡ true
  v4-ok = refl

  v4-parts : (T : SixCases) (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
             (v4-ok-one T (double-rows (permute-matrix x y (pattern-matrix T))) ≡ true) ×
             (v4-ok-one T (double-cols (permute-matrix x y (pattern-matrix T))) ≡ true)
  v4-parts T x y hx hy =
    ∧-true (all-of-∈ (v4-case T) (pairs all-perms all-perms)
                     (all-of-∈ v4-one six-cases v4-ok (∈-six-cases T)) (∈-pairs hx hy))

  v4-exclude : (T : SixCases) (Z : Matrix 4 4 Z2) -> v4-ok-one T Z ≡ true ->
               (Z == z2-zero) ≡ false ->
               (S : SixCases) -> fig1-drop S T ≡ false ->
               inv-eq (inv Z) (pat-inv S) ≡ false
  v4-exclude T Z hok hnz S hS =
    not-true (subst (λ b -> (if b then true else not (inv-eq (inv Z) (pat-inv S))) ≡ true)
                    hS step1')
    where
      body : SixCases -> Bool
      body S' = if fig1-drop S' T then true else not (inv-eq (inv Z) (pat-inv S'))
      step1 : all-of body six-cases ≡ true
      step1 = subst (λ b -> (if b then true else all-of body six-cases) ≡ true) hnz hok
      step1' : body S ≡ true
      step1' = all-of-∈ body six-cases step1 (∈-six-cases S)

-- Lemma V.4, at the level of the residues, for a K gate acting on the
-- left: if the target of a K-count-1 1-descent has pattern T, then the
-- source cannot have a pattern S for which Figure 1 has no undashed
-- edge S → T.
lemma-V-4-rows :
  (T S : SixCases) (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
  (double-rows (permute-matrix x y (pattern-matrix T)) == z2-zero) ≡ false ->
  fig1-drop S T ≡ false ->
  (u v : Tuple4) -> u ∈ˡ all-perms -> v ∈ˡ all-perms ->
  ¬ (double-rows (permute-matrix x y (pattern-matrix T)) ≡ permute-matrix u v (pattern-matrix S))
lemma-V-4-rows T S x y hx hy hnz hS u v hu hv =
  not-orbit (double-rows (permute-matrix x y (pattern-matrix T))) S
            (v4-exclude T (double-rows (permute-matrix x y (pattern-matrix T)))
                        (proj₁ (v4-parts T x y hx hy)) hnz S hS)
            u v hu hv

-- The same for a K gate acting on the right.
lemma-V-4-cols :
  (T S : SixCases) (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
  (double-cols (permute-matrix x y (pattern-matrix T)) == z2-zero) ≡ false ->
  fig1-drop S T ≡ false ->
  (u v : Tuple4) -> u ∈ˡ all-perms -> v ∈ˡ all-perms ->
  ¬ (double-cols (permute-matrix x y (pattern-matrix T)) ≡ permute-matrix u v (pattern-matrix S))
lemma-V-4-cols T S x y hx hy hnz hS u v hu hv =
  not-orbit (double-cols (permute-matrix x y (pattern-matrix T))) S
            (v4-exclude T (double-cols (permute-matrix x y (pattern-matrix T)))
                        (proj₂ (v4-parts T x y hx hy)) hnz S hS)
            u v hu hv

-- ----------------------------------------------------------------------
-- * Lemma V.6, at the level of the residues
--
-- A K gate on the left combines the rows 0,1 and the rows 2,3. The
-- step is a 0-descent exactly when no pair is mixed (which would raise
-- the lde) and the two pairs are not both equal modulo γ² (which would
-- lower it). In that case the K action of Section II C,
--
--    1b₀b₁ / 1b′₀b′₁ ↦ [(b₀⊕b′₀)(b₁⊕b′₁⊕1), (b₀⊕b′₀)(b₁⊕b′₁)],
--    0b₀b₁ / 0b′₀b′₁ ↦ both (b₀⊕b′₀)(b₁⊕b′₁),
--
-- gives both entries of a pair the same parity b₀⊕b′₀, the sum of the
-- *second* digits of the two ρˡ₂ entries: so ρˡ₁ of the target of a
-- 0-descent is determined by ρˡ₂ of the source.
--
-- A general K-count-1 0-descent is L₂·K₁·L₁·A·R₁ (or its mirror
-- image). The outer L₂ and R₁ do not change the pattern, and
-- ρˡ₂(L₁·A·R) is ρ₂(L₁) times the normal form of Section IV B times a
-- column permutation and rescaling, which again does not change the
-- pattern. So it is enough to enumerate the 24·16 = 384 residue
-- classes of ρ₂(L₁) over the normal forms of pattern (vi) and their
-- transposes.

R2Phase4 : Set
R2Phase4 = R2 × R2 × R2 × R2

private
  fst-digit snd-digit : R2 -> Z2
  fst-digit (a ∷ b ∷ []) = a
  snd-digit (a ∷ b ∷ []) = b

  row-of : Matrix 4 4 R2 -> ℕ -> Vector 4 R2
  row-of m j = vsel4 (rows-4 m) j

  scale-row : R2 -> Vector 4 R2 -> Vector 4 R2
  scale-row c v = vector-map (c r2*_) v

-- P·M for the left generalized permutation given by a row permutation
-- and four unit phases (ρ₂ of a power of i is 10 or 11).
left-act : Tuple4 -> R2Phase4 -> Matrix 4 4 R2 -> Matrix 4 4 R2
left-act σ (c₀ , c₁ , c₂ , c₃) m =
  Matrix' (vector-transpose (scale-row c₀ (row-of m (sel σ 0)) ∷
                             scale-row c₁ (row-of m (sel σ 1)) ∷
                             scale-row c₂ (row-of m (sel σ 2)) ∷
                             scale-row c₃ (row-of m (sel σ 3)) ∷ []))

private
  and4 : Vector 4 Bool -> Bool
  and4 (a ∷ b ∷ c ∷ d ∷ []) = a ∧ b ∧ c ∧ d

  same-parity? : Vector 4 R2 -> Vector 4 R2 -> Bool
  same-parity? u v = and4 (vector-zipwith (λ x y -> fst-digit x == fst-digit y) u v)

  k-parity-row : Vector 4 R2 -> Vector 4 R2 -> Vector 4 Z2
  k-parity-row u v = vector-zipwith (λ x y -> snd-digit x + snd-digit y) u v

-- The ρˡ₁ of the target of a K-count-1 step on the left, when that
-- step is a 0-descent; nothing when it is not one.
zero-descent-target : Matrix 4 4 R2 -> Maybe (Matrix 4 4 Z2)
zero-descent-target m = zdt (row-of m 0) (row-of m 1) (row-of m 2) (row-of m 3)
  where
    zdt : Vector 4 R2 -> Vector 4 R2 -> Vector 4 R2 -> Vector 4 R2 -> Maybe (Matrix 4 4 Z2)
    zdt r0 r1 r2 r3 =
      if (same-parity? r0 r1 ∧ same-parity? r2 r3) ∧ not ((r0 == r1) ∧ (r2 == r3))
      then just (build (k-parity-row r0 r1) (k-parity-row r2 r3))
      else nothing
      where
        build : Vector 4 Z2 -> Vector 4 Z2 -> Matrix 4 4 Z2
        build p q = Matrix' (vector-transpose (p ∷ p ∷ q ∷ q ∷ []))

-- The two unit residues and the 16 phase vectors.
r2-units : List R2
r2-units = r2-one ∷ r2-i ∷ []

∈-r2-units-one : r2-one ∈ˡ r2-units
∈-r2-units-one = here

∈-r2-units-i : r2-i ∈ˡ r2-units
∈-r2-units-i = there here

unit4s : List R2Phase4
unit4s = pairs r2-units (pairs r2-units (pairs r2-units r2-units))

∈-unit4s : {a b c d : R2} -> a ∈ˡ r2-units -> b ∈ˡ r2-units -> c ∈ˡ r2-units -> d ∈ˡ r2-units ->
           (a , b , c , d) ∈ˡ unit4s
∈-unit4s ha hb hc hd = ∈-pairs ha (∈-pairs hb (∈-pairs hc hd))

-- The 24·16 = 384 residue classes of a left generalized permutation.
left-classes : List (Tuple4 × R2Phase4)
left-classes = pairs all-perms unit4s

∈-left-classes : {σ : Tuple4} {c : R2Phase4} -> σ ∈ˡ all-perms -> c ∈ˡ unit4s ->
                 (σ , c) ∈ˡ left-classes
∈-left-classes hσ hc = ∈-pairs hσ hc

-- The normal forms of pattern (vi), and their transposes (for the
-- mirror-image descents A·P·K₁).
vi-forms : List (Matrix 4 4 R2)
vi-forms = normal-forms VI 2 ++ List.map matrix-transpose (normal-forms VI 2)

private
  v6-target-ok : Maybe (Matrix 4 4 Z2) -> Bool
  v6-target-ok nothing = true
  v6-target-ok (just Z) = not (inv-eq (inv Z) (pat-inv II)) ∧ not (inv-eq (inv Z) (pat-inv V))

  v6-one : Matrix 4 4 R2 -> Tuple4 × R2Phase4 -> Bool
  v6-one N lc = v6-target-ok (zero-descent-target (left-act (proj₁ lc) (proj₂ lc) N))

  v6-form : Matrix 4 4 R2 -> Bool
  v6-form N = all-of (v6-one N) left-classes

  -- 4 · 384 = 1536 residue steps.
  v6-ok : all-of v6-form vi-forms ≡ true
  v6-ok = refl

-- Lemma V.6, at the level of the residues: no K-count-1 0-descent out
-- of a pattern-(vi) normal form reaches pattern (ii) or pattern (v).
lemma-V-6-residue :
  (N : Matrix 4 4 R2) -> N ∈ˡ vi-forms ->
  (σ : Tuple4) -> σ ∈ˡ all-perms -> (c : R2Phase4) -> c ∈ˡ unit4s ->
  (Z : Matrix 4 4 Z2) -> zero-descent-target (left-act σ c N) ≡ just Z ->
  (x y : Tuple4) -> x ∈ˡ all-perms -> y ∈ˡ all-perms ->
  ¬ (Z ≡ permute-matrix x y (pattern-matrix II)) × ¬ (Z ≡ permute-matrix x y (pattern-matrix V))
lemma-V-6-residue N hN σ hσ c hc Z hZ x y hx hy =
  not-orbit Z II (not-true (proj₁ parts)) x y hx hy ,
  not-orbit Z V (not-true (proj₂ parts)) x y hx hy
  where
    chk : v6-target-ok (just Z) ≡ true
    chk = subst (λ w -> v6-target-ok w ≡ true) hZ
                (all-of-∈ (v6-one N) left-classes
                          (all-of-∈ v6-form vi-forms v6-ok hN) (∈-left-classes hσ hc))
    parts : (not (inv-eq (inv Z) (pat-inv II)) ≡ true) × (not (inv-eq (inv Z) (pat-inv V)) ≡ true)
    parts = ∧-true chk

-- ----------------------------------------------------------------------
-- * Lemma V.3, at the level of the residues
--
-- A K₁ gate on the left combines the rows 0,1 and the rows 2,3 of the
-- operator: the entries of K₁A are (A₀ⱼ ± A₁ⱼ)/γ and (A₂ⱼ ± A₃ⱼ)/γ.
-- For A of lde l > 0, lde(K₁A) < l exactly when
--
--    ρˡ₂(A₀ⱼ) = ρˡ₂(A₁ⱼ)  and  ρˡ₂(A₂ⱼ) = ρˡ₂(A₃ⱼ)   for all j,
--
-- because -1 ≡ 1 (mod γ²), so the two conditions γ² | A₀ⱼ + A₁ⱼ and
-- γ² | A₀ⱼ - A₁ⱼ coincide. Multiplying on the left by a generalized
-- permutation permutes the rows and multiplies them by powers of i,
-- and ρ₂(i^k) is 10 or 11, so the condition for lde(K₁·P·A) < l is
-- that the four rows of ρˡ₂(A) can be split into two pairs, each of
-- which is equal up to a factor 11. Multiplying on the right by a
-- generalized permutation permutes and rescales the columns, which
-- does not change whether two rows are equal, so the condition is
-- invariant under it; and the same applies to the columns for A·P·K₁.

-- Is u equal to v, possibly after multiplication by ρ₂(i) = 11?
r2-pair? : Vector 4 R2 -> Vector 4 R2 -> Bool
r2-pair? u v = (u == v) ∨ (u == vector-map (r2-i r2*_) v)

-- Can the four vectors be split into two pairs, each equal up to a
-- factor 11?
k-pairs? : Vector 4 (Vector 4 R2) -> Bool
k-pairs? vs = go (vsel4 vs 0) (vsel4 vs 1) (vsel4 vs 2) (vsel4 vs 3)
  where
    go : Vector 4 R2 -> Vector 4 R2 -> Vector 4 R2 -> Vector 4 R2 -> Bool
    go a b c d = (r2-pair? a b ∧ r2-pair? c d)
               ∨ (r2-pair? a c ∧ r2-pair? b d)
               ∨ (r2-pair? a d ∧ r2-pair? b c)

-- Is there a generalized permutation P with lde(K₁·P·A) < lde A?  And
-- the mirror question for A·P·K₁.
k-drop-left? k-drop-right? : Matrix 4 4 R2 -> Bool
k-drop-left? m = k-pairs? (rows-4 m)
k-drop-right? m = k-pairs? (unMatrix m)

no-one-K-descent? : Matrix 4 4 R2 -> Bool
no-one-K-descent? m = not (k-drop-left? m) ∧ not (k-drop-right? m)

-- ----------------------------------------------------------------------
-- ** The unitarity reduction of the pattern-(ii) normal form at lde 1
--
-- Kopt.Patterns.normal-forms II 1 over-approximates: it lists all 16
-- choices of the four free bits d,e,f,g of the lower right block of
-- pii2k1. Unitarity cuts these down to two, as follows. In the normal
-- form ρ¹₂(B) = pii2k1 d e f g the last two columns have all their ρ₂
-- entries even, so the last two columns of B itself are integral:
-- dividing by γ shifts the residues left (Lemma II.9), and their ρ⁰₁
-- are (0,0,d,f)ᵀ and (0,0,e,g)ᵀ. An integral column of a unitary is a
-- unit vector over ℤ[i]: by Lemma II.5 an entry has odd norm exactly
-- when it is odd, and the four norms are non-negative integers summing
-- to 1, so exactly one entry is odd (a power of i) and the others
-- vanish. Two such columns are orthogonal, so their odd entries are in
-- different rows. (This is the lde-0 case of Lemmas IV.2 and IV.3.)
--
-- So exactly one of d,f is odd, exactly one of e,g is odd, and the two
-- are not in the same row.

-- The condition just described, as a boolean test on the four bits:
-- exactly one of d,f is odd (column 2 has exactly one odd entry),
-- exactly one of e,g is odd (column 3 has exactly one odd entry), and
-- the two odd entries are not both in row 2 nor both in row 3 (the two
-- columns are orthogonal).
pii2k1-unitary? : Z2 -> Z2 -> Z2 -> Z2 -> Bool
pii2k1-unitary? d e f g =
  ((d + f) == Odd) ∧ ((e + g) == Odd) ∧ not (both-odd d e) ∧ not (both-odd f g)
  where
    both-odd : Z2 -> Z2 -> Bool
    both-odd Odd Odd = true
    both-odd _ _ = false

-- The two forms that survive: the lower right block is one of the two
-- 2×2 generalized permutations with entries γ. (This list is
-- Kopt.Patterns.pii2k1-unitary.)
pii2k1-forms : List (Matrix 4 4 R2)
pii2k1-forms = pii2k1 Odd Even Even Odd ∷ pii2k1 Even Odd Odd Even ∷ []

-- The reduction, by enumerating the 16 possibilities.
pii2k1-restricted : (d e f g : Z2) -> pii2k1-unitary? d e f g ≡ true ->
                    pii2k1 d e f g ∈ˡ pii2k1-forms
pii2k1-restricted Odd Even Even Odd _ = here
pii2k1-restricted Even Odd Odd Even _ = there here
pii2k1-restricted Even Even Even Even ()
pii2k1-restricted Even Even Even Odd ()
pii2k1-restricted Even Even Odd Even ()
pii2k1-restricted Even Even Odd Odd ()
pii2k1-restricted Even Odd Even Even ()
pii2k1-restricted Even Odd Even Odd ()
pii2k1-restricted Even Odd Odd Odd ()
pii2k1-restricted Odd Even Even Even ()
pii2k1-restricted Odd Even Odd Even ()
pii2k1-restricted Odd Even Odd Odd ()
pii2k1-restricted Odd Odd Even Even ()
pii2k1-restricted Odd Odd Even Odd ()
pii2k1-restricted Odd Odd Odd Even ()
pii2k1-restricted Odd Odd Odd Odd ()

-- ----------------------------------------------------------------------
-- ** The check
--
-- The normal forms for which the path descent spends two K gates on
-- one step of the lde: pattern (ii) at any lde, pattern (v), and
-- pattern (iii) at lde > 1. None of them admits a one-K-gate
-- 1-descent.

lemma-V-3-forms : List (Matrix 4 4 R2)
lemma-V-3-forms = pii2k1-forms ++ normal-forms II 2 ++ normal-forms V 2 ++ normal-forms III 2

private
  v3-ok : all-of no-one-K-descent? lemma-V-3-forms ≡ true
  v3-ok = refl

-- Lemma V.3, at the level of the residues: no generalized permutation
-- together with a single K gate lowers the lde of any of these normal
-- forms, so the two-K-gate step of the path descent cannot be replaced
-- by a one-K-gate step.
lemma-V-3-residue : (N : Matrix 4 4 R2) -> N ∈ˡ lemma-V-3-forms ->
                    (k-drop-left? N ≡ false) × (k-drop-right? N ≡ false)
lemma-V-3-residue N hN = not-true (proj₁ parts) , not-true (proj₂ parts)
  where
    parts : (not (k-drop-left? N) ≡ true) × (not (k-drop-right? N) ≡ true)
    parts = ∧-true (all-of-∈ no-one-K-descent? lemma-V-3-forms v3-ok hN)

-- Lemma V.3 for pattern (ii) at lde 1, with the unitarity reduction
-- folded in: whatever the four free bits of the normal form are, as
-- long as they satisfy the condition that unitarity imposes, no
-- generalized permutation and single K gate lower the lde.
lemma-V-3-pii2k1 : (d e f g : Z2) -> pii2k1-unitary? d e f g ≡ true ->
                   (k-drop-left? (pii2k1 d e f g) ≡ false) ×
                   (k-drop-right? (pii2k1 d e f g) ≡ false)
lemma-V-3-pii2k1 d e f g h =
  lemma-V-3-residue (pii2k1 d e f g) (∈-++ˡ _ (pii2k1-restricted d e f g h))

-- For comparison: at lde 1 the pattern (iii) normal form does admit a
-- one-K-gate 1-descent, which is the edge (iii) → (i) of Figure 1.
lemma-V-3-iii-1 : all-of k-drop-left? (normal-forms III 1) ≡ true
lemma-V-3-iii-1 = refl

-- ----------------------------------------------------------------------
-- * The four checks, as booleans
--
-- These are the exhaustive checks that the type checker runs above
-- (inv-perm-ok, v3-ok, v4-ok, v6-ok), exported so that they can also
-- be evaluated at run time and cross-checked against the pattern
-- classifier of Test.KoptOptimalityRun.

inv-perm-check v3-check v4-check v6-check : Bool
inv-perm-check = all-of inv-perm-one six-cases
v3-check = all-of no-one-K-descent? lemma-V-3-forms
v4-check = all-of v4-one six-cases
v6-check = all-of v6-form vi-forms

