-- Section V of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the optimality theory. The definitions are in Kopt.Descent; this
-- module contains the results.
--
-- What is proved here, and what is not:
--
--  * Equation (3) (every circuit over 𝒢 is an alternating sequence of
--    generalized permutations and K₁ gates with the same K-count),
--    Remark II.10, second half (only K changes the lde), Lemma V.5
--    (the exterior of a K-optimal descent is K-optimal) and the
--    upper bound cs(A) ≤ kc(A)+1 of Theorem V.9 are PROVED.
--
--  * The finite verification "every generalized permutation is
--    implementable by at most 9 gates, at most one CS gate and no K
--    gate" is a decidable exhaustive check over the explicit list of
--    the 24·256 = 6144 generalized permutations, which the type
--    checker runs (gp-check-all). Together with the fact that every
--    generalized permutation occurs in that list (which is proved),
--    this is a proof.
--
--  * The lower bound kc(A)/2 - 1 ≤ cs(A) of Theorem V.9 is proved
--    from the hypothesis CliffordK2 ("every two-qubit Clifford
--    operator is implementable with at most two K gates"), which is a
--    finite statement about the 46080 two-qubit Clifford operators.
--    It is verified by execution in Test.KoptOptimalityRun, not by
--    the type checker.
--
--  * Lemmas V.3, V.4, V.6 and V.7 are STATED here (as the types
--    Lemma-V-3 … Lemma-V-7), and the results that depend on them (the
--    K-optimality half of Corollary V.8) take them as hypotheses. Two
--    further modules go beyond that:
--
--     - Kopt.NormalForms contains the residue-level content of Lemmas
--       V.3, V.4 and V.6 -- the finite enumerations that the paper's
--       proofs run -- as exhaustive checks that the type checker runs,
--       in the style of gp-check-all below. What is missing to obtain
--       the operator-level statements is the step from an operator to
--       its residue data (the correctness of lemma-six and refine,
--       which is checked by execution on the authors' data set), so
--       Lemma-V-3, Lemma-V-4 and Lemma-V-6 remain hypotheses.
--     - Kopt.OptInduction PROVES Lemma V.7 from Lemma V.4, Lemma V.6
--       and the pattern-(i) characterisation of Lemma IV.1, and its
--       cor-V-8-K-optimal′ is the K-optimality half of Corollary V.8
--       without Lemma V.7 as a hypothesis.

{-# OPTIONS --without-K --safe #-}

module Kopt.Optimality where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
import Data.List.Properties as ListP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s ; _∸_)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations using (gperm-of)
open import Kopt.Patterns using (SixCases ; I ; II ; III ; IV ; IVt ; V ; VI ; patof)
open import Kopt.Synth using (prkc ; synth)
open import Kopt.Properties.LdeLemmas using (lemma-II-8 ; lde-+ ; max-≤ˡ ; max-≤ʳ ; max-lub)
open import Kopt.Descent

-- ----------------------------------------------------------------------
-- * Booleans as propositions

private
  false≢true : false ≡ true -> ⊥
  false≢true ()

-- A boolean equality test that succeeds is an equality.
==⇒≡ : {A : Set} {{_ : DecEq A}} {x y : A} -> (x == y) ≡ true -> x ≡ y
==⇒≡ {x = x} {y} e with x ≟ y
... | yes p = p
... | no _ = ⊥-elim (false≢true e)

≤ᵇ⇒≤ : {m n : ℕ} -> (m Nat.≤ᵇ n) ≡ true -> m Nat.≤ n
≤ᵇ⇒≤ {m} {n} e = NatP.≤ᵇ⇒≤ m n (subst T (sym e) tt)

≡ᵇ⇒≡ : {m n : ℕ} -> (m Nat.≡ᵇ n) ≡ true -> m ≡ n
≡ᵇ⇒≡ {m} {n} e = NatP.≡ᵇ⇒≡ m n (subst T (sym e) tt)

-- ----------------------------------------------------------------------
-- * The gate counts of a concatenation

-- The K-count, the CS-count and the length of a single gate.
private
  kc1 : Gate -> ℕ
  kc1 K₀ = 1
  kc1 K₁ = 1
  kc1 _ = 0

  cs1 : Gate -> ℕ
  cs1 CS = 1
  cs1 _ = 0

kc-cons : (g : Gate) (c : Circuit) -> kc (g ∷ c) ≡ kc1 g Nat.+ kc c
kc-cons X₀ c = refl
kc-cons X₁ c = refl
kc-cons Z₀ c = refl
kc-cons Z₁ c = refl
kc-cons S₀ c = refl
kc-cons S₁ c = refl
kc-cons K₀ c = refl
kc-cons K₁ c = refl
kc-cons CZ c = refl
kc-cons CS c = refl
kc-cons CX c = refl
kc-cons XC c = refl
kc-cons Ex c = refl
kc-cons Ii c = refl
kc-cons CK c = refl
kc-cons KC c = refl

csc-cons : (g : Gate) (c : Circuit) -> csc (g ∷ c) ≡ cs1 g Nat.+ csc c
csc-cons X₀ c = refl
csc-cons X₁ c = refl
csc-cons Z₀ c = refl
csc-cons Z₁ c = refl
csc-cons S₀ c = refl
csc-cons S₁ c = refl
csc-cons K₀ c = refl
csc-cons K₁ c = refl
csc-cons CZ c = refl
csc-cons CS c = refl
csc-cons CX c = refl
csc-cons XC c = refl
csc-cons Ex c = refl
csc-cons Ii c = refl
csc-cons CK c = refl
csc-cons KC c = refl

kc-++ : (c d : Circuit) -> kc (c ++ d) ≡ kc c Nat.+ kc d
kc-++ [] d = refl
kc-++ (g ∷ c) d = begin
  kc (g ∷ (c ++ d))            ≡⟨ kc-cons g (c ++ d) ⟩
  kc1 g Nat.+ kc (c ++ d)      ≡⟨ cong (λ n -> kc1 g Nat.+ n) (kc-++ c d) ⟩
  kc1 g Nat.+ (kc c Nat.+ kc d) ≡⟨ sym (NatP.+-assoc (kc1 g) (kc c) (kc d)) ⟩
  (kc1 g Nat.+ kc c) Nat.+ kc d ≡⟨ cong (λ n -> n Nat.+ kc d) (sym (kc-cons g c)) ⟩
  kc (g ∷ c) Nat.+ kc d        ∎
  where open ≡-Reasoning

csc-++ : (c d : Circuit) -> csc (c ++ d) ≡ csc c Nat.+ csc d
csc-++ [] d = refl
csc-++ (g ∷ c) d = begin
  csc (g ∷ (c ++ d))              ≡⟨ csc-cons g (c ++ d) ⟩
  cs1 g Nat.+ csc (c ++ d)        ≡⟨ cong (λ n -> cs1 g Nat.+ n) (csc-++ c d) ⟩
  cs1 g Nat.+ (csc c Nat.+ csc d) ≡⟨ sym (NatP.+-assoc (cs1 g) (csc c) (csc d)) ⟩
  (cs1 g Nat.+ csc c) Nat.+ csc d ≡⟨ cong (λ n -> n Nat.+ csc d) (sym (csc-cons g c)) ⟩
  csc (g ∷ c) Nat.+ csc d         ∎
  where open ≡-Reasoning

rlen-++ : (c d : Circuit) -> rlen (c ++ d) ≡ rlen c Nat.+ rlen d
rlen-++ c d = ListP.length-++ c

over-𝒢-++ : (c d : Circuit) -> Over𝒢 c -> Over𝒢 d -> Over𝒢 (c ++ d)
over-𝒢-++ [] d _ hd = hd
over-𝒢-++ (g ∷ c) d hc hd =
  cong₂ _∧_ (proj₁ (∧-true hc)) (over-𝒢-++ c d (proj₂ (∧-true hc)) hd)

-- ----------------------------------------------------------------------
-- * Lemma II.8 for matrices: the lde of a product
--
-- The entries of A·B are sums of products of entries of A and of B,
-- and the lde of a matrix is the maximum of the ldes of its entries.

private
  module M = M4

  lde-0# : lde (0# {DComplex}) ≡ 0
  lde-0# = refl

  lde-vadd-≤ : {n : ℕ} (v w : Vector n DComplex) ->
               lde (vadd v w) Nat.≤ max (lde v) (lde w)
  lde-vadd-≤ [] [] = z≤n
  lde-vadd-≤ (x ∷ xs) (y ∷ ys) = max-lub
    (NatP.≤-trans (lde-+ x y)
      (max-lub (NatP.≤-trans (max-≤ˡ (lde x) (lde xs)) (max-≤ˡ P Q))
               (NatP.≤-trans (max-≤ˡ (lde y) (lde ys)) (max-≤ʳ P Q))))
    (NatP.≤-trans (lde-vadd-≤ xs ys)
      (max-lub (NatP.≤-trans (max-≤ʳ (lde x) (lde xs)) (max-≤ˡ P Q))
               (NatP.≤-trans (max-≤ʳ (lde y) (lde ys)) (max-≤ʳ P Q))))
    where
      P Q : ℕ
      P = max (lde x) (lde xs)
      Q = max (lde y) (lde ys)

  lde-smul-≤ : {n : ℕ} (x : DComplex) (v : Vector n DComplex) ->
               lde (smul x v) Nat.≤ lde x Nat.+ lde v
  lde-smul-≤ x [] = z≤n
  lde-smul-≤ x (a ∷ as) = max-lub
    (NatP.≤-trans (lemma-II-8 x a)
                  (NatP.+-monoʳ-≤ (lde x) (max-≤ˡ (lde a) (lde as))))
    (NatP.≤-trans (lde-smul-≤ x as)
                  (NatP.+-monoʳ-≤ (lde x) (max-≤ʳ (lde a) (lde as))))

  lde-zero-vec-≤ : {n : ℕ} -> lde (M.zero-vec {n}) Nat.≤ 0
  lde-zero-vec-≤ {zero} = z≤n
  lde-zero-vec-≤ {suc n} = max-lub (NatP.≤-reflexive lde-0#) (lde-zero-vec-≤ {n})

  lde-lcomb-≤ : {m n : ℕ} (a : Vector n (Vector m DComplex)) (v : Vector n DComplex) ->
                lde (lcomb a v) Nat.≤ lde a Nat.+ lde v
  lde-lcomb-≤ {m} [] [] = lde-zero-vec-≤ {m}
  lde-lcomb-≤ (h ∷ t) (w ∷ ws) = NatP.≤-trans (lde-vadd-≤ (smul w h) (lcomb t ws))
    (max-lub
      (NatP.≤-trans (lde-smul-≤ w h)
        (NatP.≤-trans (NatP.+-mono-≤ (max-≤ˡ (lde w) (lde ws)) (max-≤ˡ (lde h) (lde t)))
                      (NatP.≤-reflexive (NatP.+-comm (max (lde w) (lde ws)) (max (lde h) (lde t))))))
      (NatP.≤-trans (lde-lcomb-≤ t ws)
        (NatP.+-mono-≤ (max-≤ʳ (lde h) (lde t)) (max-≤ʳ (lde w) (lde ws)))))

  lde-mmul-≤ : (M N : Op) -> lde (mmul M N) Nat.≤ lde M Nat.+ lde N
  lde-mmul-≤ (Matrix' a) (Matrix' (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])) =
    lde-4-≤ (lcomb a b₀) (lcomb a b₁) (lcomb a b₂) (lcomb a b₃)
            (go b₀ (lde-4-0 b₀ b₁ b₂ b₃)) (go b₁ (lde-4-1 b₀ b₁ b₂ b₃))
            (go b₂ (lde-4-2 b₀ b₁ b₂ b₃)) (go b₃ (lde-4-3 b₀ b₁ b₂ b₃))
    where
      B : ℕ
      B = max (lde b₀) (max (lde b₁) (max (lde b₂) (max (lde b₃) 0)))
      go : (v : Vector 4 DComplex) -> lde v Nat.≤ B -> lde (lcomb a v) Nat.≤ lde a Nat.+ B
      go v h = NatP.≤-trans (lde-lcomb-≤ a v) (NatP.+-monoʳ-≤ (lde a) h)

-- Lemma II.8 for 4×4 matrices: lde(AB) ≤ lde(A) + lde(B).
-- (Abstract: unfolding it on a concrete matrix would make the type
-- checker normalise 4×4 products of dyadic complex numbers.)
abstract
  lde-*-≤ : (M N : Op) -> lde (M * N) Nat.≤ lde M Nat.+ lde N
  lde-*-≤ M N = subst (λ z -> lde z Nat.≤ lde M Nat.+ lde N) (sym (mmul-≡ M N)) (lde-mmul-≤ M N)

-- ----------------------------------------------------------------------
-- * Generalized permutations do not change the lde

abstract
 lde-gp-left : (G : GP) (A : Op) -> lde (gp-mat G * A) ≡ lde A
 lde-gp-left G A = NatP.≤-antisym le ge
  where
    le : lde (gp-mat G * A) Nat.≤ lde A
    le = subst (λ n -> lde (gp-mat G * A) Nat.≤ n Nat.+ lde A) (lde-gp G) (lde-*-≤ (gp-mat G) A)
    step : gp-mat (gp-inverse G) * (gp-mat G * A) ≡ A
    step = trans (sym (mat-*-assoc (gp-mat (gp-inverse G)) (gp-mat G) A))
                 (trans (cong (λ m -> m * A) (gp-inverse-left G)) (mat-*-identityˡ A))
    ge : lde A Nat.≤ lde (gp-mat G * A)
    ge = subst (λ z -> lde z Nat.≤ lde (gp-mat G * A)) step
         (subst (λ n -> lde (gp-mat (gp-inverse G) * (gp-mat G * A)) Nat.≤ n Nat.+ lde (gp-mat G * A))
                (lde-gp (gp-inverse G))
                (lde-*-≤ (gp-mat (gp-inverse G)) (gp-mat G * A)))

abstract
 lde-gp-right : (A : Op) (G : GP) -> lde (A * gp-mat G) ≡ lde A
 lde-gp-right A G = NatP.≤-antisym le ge
  where
    le : lde (A * gp-mat G) Nat.≤ lde A
    le = subst (λ n -> lde (A * gp-mat G) Nat.≤ n) (NatP.+-identityʳ (lde A))
           (subst (λ n -> lde (A * gp-mat G) Nat.≤ lde A Nat.+ n) (lde-gp G)
                  (lde-*-≤ A (gp-mat G)))
    step : (A * gp-mat G) * gp-mat (gp-inverse G) ≡ A
    step = trans (mat-*-assoc A (gp-mat G) (gp-mat (gp-inverse G)))
                 (trans (cong (λ m -> A * m) (gp-inverse-right G)) (mat-*-identityʳ A))
    ge : lde A Nat.≤ lde (A * gp-mat G)
    ge = subst (λ z -> lde z Nat.≤ lde (A * gp-mat G)) step
         (subst (λ n -> lde ((A * gp-mat G) * gp-mat (gp-inverse G)) Nat.≤ n)
                (NatP.+-identityʳ (lde (A * gp-mat G)))
                (subst (λ n -> lde ((A * gp-mat G) * gp-mat (gp-inverse G))
                                 Nat.≤ lde (A * gp-mat G) Nat.+ n)
                       (lde-gp (gp-inverse G))
                       (lde-*-≤ (A * gp-mat G) (gp-mat (gp-inverse G)))))

-- ----------------------------------------------------------------------
-- * The gates that are generalized permutations

-- Which gates are generalized permutations: all of 𝒢 except K₀ and
-- K₁ (and the derived gates CK and KC, which contain a K).
gate-gp? : Gate -> Bool
gate-gp? K₀ = false
gate-gp? K₁ = false
gate-gp? CK = false
gate-gp? KC = false
gate-gp? _ = true

gp-of-gate : Gate -> GP
gp-of-gate X₀ = gperm (p2 , p3 , p0 , p1) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate X₁ = gperm (p1 , p0 , p3 , p2) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Z₀ = gperm id4p (ph0 , ph0 , ph2 , ph2) refl
gp-of-gate Z₁ = gperm id4p (ph0 , ph2 , ph0 , ph2) refl
gp-of-gate S₀ = gperm id4p (ph0 , ph0 , ph1 , ph1) refl
gp-of-gate S₁ = gperm id4p (ph0 , ph1 , ph0 , ph1) refl
gp-of-gate CZ = gperm id4p (ph0 , ph0 , ph0 , ph2) refl
gp-of-gate CS = gperm id4p (ph0 , ph0 , ph0 , ph1) refl
gp-of-gate CX = gperm (p0 , p1 , p3 , p2) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate XC = gperm (p0 , p3 , p2 , p1) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Ex = gperm (p0 , p2 , p1 , p3) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Ii = gperm id4p (ph1 , ph1 , ph1 , ph1) refl
gp-of-gate _ = gp-one

-- Every gate of 𝒢 except K₀ and K₁ is a generalized permutation.
gate-gp-ok : (g : Gate) -> gate-gp? g ≡ true -> ⟦ g ⟧g ≡ gp-mat (gp-of-gate g)
gate-gp-ok K₀ ()
gate-gp-ok K₁ ()
gate-gp-ok CK ()
gate-gp-ok KC ()
gate-gp-ok X₀ _ = ==⇒≡ refl
gate-gp-ok X₁ _ = ==⇒≡ refl
gate-gp-ok Z₀ _ = ==⇒≡ refl
gate-gp-ok Z₁ _ = ==⇒≡ refl
gate-gp-ok S₀ _ = ==⇒≡ refl
gate-gp-ok S₁ _ = ==⇒≡ refl
gate-gp-ok CZ _ = ==⇒≡ refl
gate-gp-ok CS _ = ==⇒≡ refl
gate-gp-ok CX _ = ==⇒≡ refl
gate-gp-ok XC _ = ==⇒≡ refl
gate-gp-ok Ex _ = ==⇒≡ refl
gate-gp-ok Ii _ = ==⇒≡ refl

-- Remark II.10, second half: K is the only gate that changes the lde.
remark-II-10-gate : (g : Gate) -> gate-gp? g ≡ true -> (A : Op) -> lde (⟦ g ⟧g * A) ≡ lde A
remark-II-10-gate g h A =
  trans (cong (λ m -> lde (m * A)) (gate-gp-ok g h)) (lde-gp-left (gp-of-gate g) A)

remark-II-10-gate-right : (g : Gate) -> gate-gp? g ≡ true -> (A : Op) -> lde (A * ⟦ g ⟧g) ≡ lde A
remark-II-10-gate-right g h A =
  trans (cong (λ m -> lde (A * m)) (gate-gp-ok g h)) (lde-gp-right A (gp-of-gate g))

-- ----------------------------------------------------------------------
-- * K-free circuits implement generalized permutations

-- A circuit is K-free if every one of its gates is a generalized
-- permutation.
gp-circuit? : Circuit -> Bool
gp-circuit? [] = true
gp-circuit? (g ∷ c) = gate-gp? g ∧ gp-circuit? c

-- Every K-free circuit implements a generalized permutation: the
-- generalized permutations are closed under products (gp-mat-comp of
-- Kopt.Descent) and contain the identity.
kfree-gp : (c : Circuit) -> gp-circuit? c ≡ true -> IsGPerm ⟦ c ⟧
kfree-gp [] _ = gp-one , sym gp-one-mat
kfree-gp (g ∷ c) e = gp-comp (gp-of-gate g) G , eq
  where
    hg : gate-gp? g ≡ true
    hg = proj₁ (∧-true e)
    rec : IsGPerm ⟦ c ⟧
    rec = kfree-gp c (proj₂ (∧-true e))
    G : GP
    G = proj₁ rec
    eq : ⟦ g ⟧g * ⟦ c ⟧ ≡ gp-mat (gp-comp (gp-of-gate g) G)
    eq = trans (cong₂ _*_ (gate-gp-ok g hg) (proj₂ rec)) (gp-mat-comp (gp-of-gate g) G)

-- Multiplying by the operator of a K-free circuit does not change the lde.
remark-II-10 : (c : Circuit) -> gp-circuit? c ≡ true -> (A : Op) -> lde (⟦ c ⟧ * A) ≡ lde A
remark-II-10 c h A = trans (cong (λ m -> lde (m * A)) (proj₂ (kfree-gp c h)))
                           (lde-gp-left (proj₁ (kfree-gp c h)) A)

-- ----------------------------------------------------------------------
-- * Circuits for generalized permutations, by exhaustive check
--
-- Section III C: a generalized permutation is implementable by at
-- most 9 gates, at most one CS gate and no K gate. Kopt.Permutations
-- computes such a circuit (gperm-of); the following exhaustive check
-- over the explicit list of the 24·256 = 6144 generalized
-- permutations verifies all four properties at once. Since every
-- generalized permutation occurs in that list (∈-all-perm4 and
-- ∈-all-phase4 of Kopt.Descent), this is a proof of the general
-- statement.

private
  circuit-or-nil : Maybe Circuit -> Circuit
  circuit-or-nil (just c) = c
  circuit-or-nil nothing = []

  gp-ok : Circuit -> Op -> Bool
  gp-ok c m = (⟦ c ⟧ == m) ∧ (rlen c Nat.≤ᵇ 9) ∧ (kc c Nat.≡ᵇ 0) ∧ (csc c Nat.≤ᵇ 1) ∧ over-𝒢ᵇ c

  gp-go : Op -> Maybe Circuit -> Bool
  gp-go m nothing = false
  gp-go m (just c) = gp-ok c m

  gp-check : Pos4 × Phase4 -> Bool
  gp-check (t , e) = gp-go (gp-mat-of t e) (gperm-of (gp-mat-of t e))

  -- The exhaustive check: 6144 generalized permutations.
  gp-check-all : all-of gp-check (pairs all-perm4 all-phase4) ≡ true
  gp-check-all = refl

  gp-go-nil : (m : Op) (mc : Maybe Circuit) -> gp-go m mc ≡ true -> gp-ok (circuit-or-nil mc) m ≡ true
  gp-go-nil m (just c) e = e

-- The canonical circuit of a generalized permutation.
gp-circuit : GP -> Circuit
gp-circuit G = circuit-or-nil (gperm-of (gp-mat G))

-- Section III C, verified by the exhaustive check: gp-circuit G
-- implements G exactly, with at most 9 gates, no K gate and at most
-- one CS gate, using only gates of 𝒢.
gp-circuit-ok : (G : GP) ->
                (⟦ gp-circuit G ⟧ ≡ gp-mat G) × (rlen (gp-circuit G) Nat.≤ 9) ×
                (kc (gp-circuit G) ≡ 0) × (csc (gp-circuit G) Nat.≤ 1) × Over𝒢 (gp-circuit G)
gp-circuit-ok G = ==⇒≡ (proj₁ parts) , ≤ᵇ⇒≤ (proj₁ (proj₂ parts)) ,
                  ≡ᵇ⇒≡ (proj₁ (proj₂ (proj₂ parts))) ,
                  ≤ᵇ⇒≤ (proj₁ (proj₂ (proj₂ (proj₂ parts)))) ,
                  proj₂ (proj₂ (proj₂ (proj₂ parts)))
  where
    chk : gp-ok (gp-circuit G) (gp-mat G) ≡ true
    chk = gp-go-nil (gp-mat G) (gperm-of (gp-mat G))
            (all-of-∈ gp-check (pairs all-perm4 all-phase4) gp-check-all
              (∈-pairs (∈-all-perm4 (gp-pos G) (gp-distinct G)) (∈-all-phase4 (gp-ph G))))
    parts : ((⟦ gp-circuit G ⟧ == gp-mat G) ≡ true) × ((rlen (gp-circuit G) Nat.≤ᵇ 9) ≡ true) ×
            ((kc (gp-circuit G) Nat.≡ᵇ 0) ≡ true) × ((csc (gp-circuit G) Nat.≤ᵇ 1) ≡ true) ×
            (over-𝒢ᵇ (gp-circuit G) ≡ true)
    parts = ∧-true₅ chk

-- ----------------------------------------------------------------------
-- * Equation (3): the alternating normal form

-- An alternating sequence P₀·K₁·P₁·K₁·…·Pₙ of generalized
-- permutations and K₁ gates.
data Alt : Set where
  alt-nil : GP -> Alt
  alt-cons : GP -> Alt -> Alt

alt-mat : Alt -> Op
alt-mat (alt-nil G) = gp-mat G
alt-mat (alt-cons G a) = gp-mat G * (⟦ K₁ ⟧g * alt-mat a)

alt-kc : Alt -> ℕ
alt-kc (alt-nil G) = 0
alt-kc (alt-cons G a) = suc (alt-kc a)

-- Multiplying the leading generalized permutation on the left.
alt-scale : GP -> Alt -> Alt
alt-scale H (alt-nil G) = alt-nil (gp-comp H G)
alt-scale H (alt-cons G a) = alt-cons (gp-comp H G) a

alt-scale-mat : (H : GP) (a : Alt) -> alt-mat (alt-scale H a) ≡ gp-mat H * alt-mat a
alt-scale-mat H (alt-nil G) = sym (gp-mat-comp H G)
alt-scale-mat H (alt-cons G a) =
  trans (cong (λ m -> m * (⟦ K₁ ⟧g * alt-mat a)) (sym (gp-mat-comp H G)))
        (mat-*-assoc (gp-mat H) (gp-mat G) (⟦ K₁ ⟧g * alt-mat a))

alt-scale-kc : (H : GP) (a : Alt) -> alt-kc (alt-scale H a) ≡ alt-kc a
alt-scale-kc H (alt-nil G) = refl
alt-scale-kc H (alt-cons G a) = refl

private
  -- K₀ = Ex·K₁·Ex.
  ex-gp : GP
  ex-gp = gp-of-gate Ex

  k0-decomp : ⟦ K₀ ⟧g ≡ gp-mat ex-gp * (⟦ K₁ ⟧g * gp-mat ex-gp)
  k0-decomp = ==⇒≡ refl

  -- A gate that is a generalized permutation is not a K gate.
  kc1-0 : (g : Gate) -> gate-gp? g ≡ true -> kc1 g ≡ 0
  kc1-0 X₀ _ = refl
  kc1-0 X₁ _ = refl
  kc1-0 Z₀ _ = refl
  kc1-0 Z₁ _ = refl
  kc1-0 S₀ _ = refl
  kc1-0 S₁ _ = refl
  kc1-0 CZ _ = refl
  kc1-0 CS _ = refl
  kc1-0 CX _ = refl
  kc1-0 XC _ = refl
  kc1-0 Ex _ = refl
  kc1-0 Ii _ = refl
  kc1-0 K₀ ()
  kc1-0 K₁ ()
  kc1-0 CK ()
  kc1-0 KC ()

  kc-cons-gp : (g : Gate) -> gate-gp? g ≡ true -> (c : Circuit) -> kc (g ∷ c) ≡ kc c
  kc-cons-gp g h c = trans (kc-cons g c) (cong (λ n -> n Nat.+ kc c) (kc1-0 g h))

  -- One step of the construction of Equation (3): a leading
  -- generalized permutation is absorbed into the leading factor.
  alt-step-gp : (g : Gate) -> gate-gp? g ≡ true -> (c : Circuit) ->
                Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c)) ->
                Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ g ∷ c ⟧) × (alt-kc a ≡ kc (g ∷ c)))
  alt-step-gp g hg c (a , ma , ka) = alt-scale (gp-of-gate g) a ,
    trans (alt-scale-mat (gp-of-gate g) a) (cong₂ _*_ (sym (gate-gp-ok g hg)) ma) ,
    trans (alt-scale-kc (gp-of-gate g) a) (trans ka (sym (kc-cons-gp g hg c)))

-- Equation (3): every circuit over 𝒢 is equivalent to an alternating
-- sequence of generalized permutations and K₁ gates with the same
-- K-count.
equation-3 : (c : Circuit) -> Over𝒢 c -> Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c))
equation-3 [] _ = alt-nil gp-one , gp-one-mat , refl
equation-3 (K₀ ∷ c) ov = go (equation-3 c ov)
  where
    go : Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c)) ->
         Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ K₀ ∷ c ⟧) × (alt-kc a ≡ kc (K₀ ∷ c)))
    go (a , ma , ka) = alt-cons ex-gp (alt-scale ex-gp a) , eq , cong suc (trans (alt-scale-kc ex-gp a) ka)
      where
        eq : gp-mat ex-gp * (⟦ K₁ ⟧g * alt-mat (alt-scale ex-gp a)) ≡ ⟦ K₀ ⟧g * ⟦ c ⟧
        eq = begin
          gp-mat ex-gp * (⟦ K₁ ⟧g * alt-mat (alt-scale ex-gp a))
            ≡⟨ cong (λ m -> gp-mat ex-gp * (⟦ K₁ ⟧g * m)) (alt-scale-mat ex-gp a) ⟩
          gp-mat ex-gp * (⟦ K₁ ⟧g * (gp-mat ex-gp * alt-mat a))
            ≡⟨ cong (λ m -> gp-mat ex-gp * m) (sym (mat-*-assoc ⟦ K₁ ⟧g (gp-mat ex-gp) (alt-mat a))) ⟩
          gp-mat ex-gp * ((⟦ K₁ ⟧g * gp-mat ex-gp) * alt-mat a)
            ≡⟨ sym (mat-*-assoc (gp-mat ex-gp) (⟦ K₁ ⟧g * gp-mat ex-gp) (alt-mat a)) ⟩
          (gp-mat ex-gp * (⟦ K₁ ⟧g * gp-mat ex-gp)) * alt-mat a
            ≡⟨ cong₂ _*_ (sym k0-decomp) ma ⟩
          ⟦ K₀ ⟧g * ⟦ c ⟧ ∎
          where open ≡-Reasoning
equation-3 (K₁ ∷ c) ov = go (equation-3 c ov)
  where
    go : Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c)) ->
         Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ K₁ ∷ c ⟧) × (alt-kc a ≡ kc (K₁ ∷ c)))
    go (a , ma , ka) = alt-cons gp-one a , eq , cong suc ka
      where
        eq : gp-mat gp-one * (⟦ K₁ ⟧g * alt-mat a) ≡ ⟦ K₁ ⟧g * ⟦ c ⟧
        eq = trans (cong (λ m -> m * (⟦ K₁ ⟧g * alt-mat a)) gp-one-mat)
             (trans (mat-*-identityˡ (⟦ K₁ ⟧g * alt-mat a))
                    (cong (λ m -> ⟦ K₁ ⟧g * m) ma))
equation-3 (CK ∷ c) ov = ⊥-elim (false≢true ov)
equation-3 (KC ∷ c) ov = ⊥-elim (false≢true ov)
equation-3 (X₀ ∷ c) ov = alt-step-gp X₀ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (X₁ ∷ c) ov = alt-step-gp X₁ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (Z₀ ∷ c) ov = alt-step-gp Z₀ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (Z₁ ∷ c) ov = alt-step-gp Z₁ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (S₀ ∷ c) ov = alt-step-gp S₀ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (S₁ ∷ c) ov = alt-step-gp S₁ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (CZ ∷ c) ov = alt-step-gp CZ refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (CS ∷ c) ov = alt-step-gp CS refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (CX ∷ c) ov = alt-step-gp CX refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (XC ∷ c) ov = alt-step-gp XC refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (Ex ∷ c) ov = alt-step-gp Ex refl c (equation-3 c (proj₂ (∧-true ov)))
equation-3 (Ii ∷ c) ov = alt-step-gp Ii refl c (equation-3 c (proj₂ (∧-true ov)))

-- ----------------------------------------------------------------------
-- ** The circuit of an alternating sequence

-- The circuit P₀·K₁·P₁·…·Pₙ, with each generalized permutation
-- replaced by its canonical circuit.
alt-circuit : Alt -> Circuit
alt-circuit (alt-nil G) = gp-circuit G
alt-circuit (alt-cons G a) = gp-circuit G ++ (K₁ ∷ alt-circuit a)

alt-circuit-ok : (a : Alt) -> ⟦ alt-circuit a ⟧ ≡ alt-mat a
alt-circuit-ok (alt-nil G) = proj₁ (gp-circuit-ok G)
alt-circuit-ok (alt-cons G a) =
  trans (⟦⟧-++ (gp-circuit G) (K₁ ∷ alt-circuit a))
        (cong₂ _*_ (proj₁ (gp-circuit-ok G)) (cong (λ m -> ⟦ K₁ ⟧g * m) (alt-circuit-ok a)))

alt-circuit-kc : (a : Alt) -> kc (alt-circuit a) ≡ alt-kc a
alt-circuit-kc (alt-nil G) = proj₁ (proj₂ (proj₂ (gp-circuit-ok G)))
alt-circuit-kc (alt-cons G a) = begin
  kc (gp-circuit G ++ (K₁ ∷ alt-circuit a))
    ≡⟨ kc-++ (gp-circuit G) (K₁ ∷ alt-circuit a) ⟩
  kc (gp-circuit G) Nat.+ suc (kc (alt-circuit a))
    ≡⟨ cong (λ n -> n Nat.+ suc (kc (alt-circuit a))) (proj₁ (proj₂ (proj₂ (gp-circuit-ok G)))) ⟩
  suc (kc (alt-circuit a))
    ≡⟨ cong suc (alt-circuit-kc a) ⟩
  suc (alt-kc a) ∎
  where open ≡-Reasoning

alt-circuit-cs : (a : Alt) -> csc (alt-circuit a) Nat.≤ suc (alt-kc a)
alt-circuit-cs (alt-nil G) = proj₁ (proj₂ (proj₂ (proj₂ (gp-circuit-ok G))))
alt-circuit-cs (alt-cons G a) =
  subst (λ n -> n Nat.≤ suc (suc (alt-kc a))) (sym (csc-++ (gp-circuit G) (K₁ ∷ alt-circuit a)))
        (NatP.+-mono-≤ (proj₁ (proj₂ (proj₂ (proj₂ (gp-circuit-ok G))))) (alt-circuit-cs a))

private
  len-eq : (k : ℕ) -> 9 Nat.+ suc (10 Nat.* k Nat.+ 9) ≡ 10 Nat.* suc k Nat.+ 9
  len-eq k = trans (NatP.+-suc 9 (10 Nat.* k Nat.+ 9))
             (trans (sym (NatP.+-assoc 10 (10 Nat.* k) 9))
                    (cong (λ n -> n Nat.+ 9) (sym (NatP.*-suc 10 k))))

alt-circuit-len : (a : Alt) -> rlen (alt-circuit a) Nat.≤ 10 Nat.* alt-kc a Nat.+ 9
alt-circuit-len (alt-nil G) = proj₁ (proj₂ (gp-circuit-ok G))
alt-circuit-len (alt-cons G a) =
  subst (λ n -> n Nat.≤ 10 Nat.* suc (alt-kc a) Nat.+ 9)
        (sym (rlen-++ (gp-circuit G) (K₁ ∷ alt-circuit a)))
        (NatP.≤-trans (NatP.+-mono-≤ (proj₁ (proj₂ (gp-circuit-ok G))) (s≤s (alt-circuit-len a)))
                      (NatP.≤-reflexive (len-eq (alt-kc a))))

alt-circuit-𝒢 : (a : Alt) -> Over𝒢 (alt-circuit a)
alt-circuit-𝒢 (alt-nil G) = proj₂ (proj₂ (proj₂ (proj₂ (gp-circuit-ok G))))
alt-circuit-𝒢 (alt-cons G a) =
  over-𝒢-++ (gp-circuit G) (K₁ ∷ alt-circuit a)
            (proj₂ (proj₂ (proj₂ (proj₂ (gp-circuit-ok G))))) (alt-circuit-𝒢 a)

-- ----------------------------------------------------------------------
-- * Corollary V.8, the counting half
--
-- Every circuit over 𝒢 can be rewritten, with the same K-count, so
-- that it uses at most rkc+1 CS gates and at most 10·rkc+9 gates: it
-- is an alternating sequence of rkc+1 generalized permutations and
-- rkc K gates (Equation (3)), and each generalized permutation costs
-- at most one CS gate and at most 9 gates (Section III C).
cor-V-8-counts : (A : Op) (c : Circuit) -> Over𝒢 c -> Implements A c ->
                 Σ[ c' ∈ Circuit ] (Over𝒢 c' × Implements A c' × (kc c' ≡ kc c) ×
                                    (csc c' Nat.≤ suc (kc c)) ×
                                    (rlen c' Nat.≤ 10 Nat.* kc c Nat.+ 9))
cor-V-8-counts A c ov impl = go (equation-3 c ov)
  where
    go : Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c)) ->
         Σ[ c' ∈ Circuit ] (Over𝒢 c' × Implements A c' × (kc c' ≡ kc c) ×
                            (csc c' Nat.≤ suc (kc c)) × (rlen c' Nat.≤ 10 Nat.* kc c Nat.+ 9))
    go (a , ma , ka) = alt-circuit a , alt-circuit-𝒢 a ,
      trans (alt-circuit-ok a) (trans ma impl) ,
      trans (alt-circuit-kc a) ka ,
      subst (λ n -> csc (alt-circuit a) Nat.≤ suc n) ka (alt-circuit-cs a) ,
      subst (λ n -> rlen (alt-circuit a) Nat.≤ 10 Nat.* n Nat.+ 9) ka (alt-circuit-len a)

-- ----------------------------------------------------------------------
-- * Theorem V.9, upper bound: cs(A) ≤ kc(A) + 1

thm-V9-upper : (A : Op) (k s : ℕ) -> HasKCount A k -> IsMinimalCSCount A s -> s Nat.≤ suc k
thm-V9-upper A k s (c , ov , impl , kc≡) mincs = go (cor-V-8-counts A c ov impl)
  where
    go : Σ[ c' ∈ Circuit ] (Over𝒢 c' × Implements A c' × (kc c' ≡ kc c) ×
                            (csc c' Nat.≤ suc (kc c)) × (rlen c' Nat.≤ 10 Nat.* kc c Nat.+ 9)) ->
         s Nat.≤ suc k
    go (c' , ov' , impl' , _ , cs≤ , _) =
      NatP.≤-trans (minimal-≤-raw-cs mincs c' ov' impl')
                   (subst (λ n -> csc c' Nat.≤ suc n) kc≡ cs≤)

-- ----------------------------------------------------------------------
-- * Theorem V.9, lower bound: kc(A)/2 - 1 ≤ cs(A)
--
-- Equation (2) of the paper: every Clifford+CS operator is an
-- alternating sequence of Clifford operators and CS gates. Every
-- two-qubit Clifford operator is implementable with at most two K
-- gates -- a finite statement, verified by execution in
-- Test.KoptOptimalityRun -- so kc(A) ≤ 2·(rcs(A)+1).

is-cs? : Gate -> Bool
is-cs? CS = true
is-cs? _ = false

private
  cs1-0 : (g : Gate) -> is-cs? g ≡ false -> cs1 g ≡ 0
  cs1-0 X₀ _ = refl
  cs1-0 X₁ _ = refl
  cs1-0 Z₀ _ = refl
  cs1-0 Z₁ _ = refl
  cs1-0 S₀ _ = refl
  cs1-0 S₁ _ = refl
  cs1-0 K₀ _ = refl
  cs1-0 K₁ _ = refl
  cs1-0 CZ _ = refl
  cs1-0 CX _ = refl
  cs1-0 XC _ = refl
  cs1-0 Ex _ = refl
  cs1-0 Ii _ = refl
  cs1-0 CK _ = refl
  cs1-0 KC _ = refl
  cs1-0 CS ()

  csc-cons-0 : (g : Gate) -> is-cs? g ≡ false -> (c : Circuit) -> csc (g ∷ c) ≡ csc c
  csc-cons-0 g h c = trans (csc-cons g c) (cong (λ n -> n Nat.+ csc c) (cs1-0 g h))

-- A Clifford operator: one implementable without CS gates.
IsClifford : Op -> Set
IsClifford C = Σ[ c ∈ Circuit ] (Over𝒢 c × Implements C c × (csc c ≡ 0))

clifford-1 : IsClifford 1#
clifford-1 = [] , refl , refl , refl

clifford-gate : (g : Gate) -> in-𝒢 g ≡ true -> is-cs? g ≡ false ->
                (C : Op) -> IsClifford C -> IsClifford (⟦ g ⟧g * C)
clifford-gate g hg hcs C (c , ov , impl , cs0) =
  g ∷ c , cong₂ _∧_ hg ov , cong (λ m -> ⟦ g ⟧g * m) impl , trans (csc-cons-0 g hcs c) cs0

-- The finite statement verified by enumeration: every two-qubit
-- Clifford operator is implementable with at most two K gates.
CliffordK2 : Set
CliffordK2 = (C : Op) -> IsClifford C ->
             Σ[ c ∈ Circuit ] (Over𝒢 c × Implements C c × (kc c Nat.≤ 2))

private
  SplitResult : Circuit -> Set
  SplitResult c = Σ[ C ∈ Op ] Σ[ r ∈ Circuit ]
                    (IsClifford C × Over𝒢 r × (C * ⟦ r ⟧ ≡ ⟦ c ⟧) × (kc r Nat.≤ 2 Nat.* csc c))

  split-step : (g : Gate) -> in-𝒢 g ≡ true -> is-cs? g ≡ false ->
               (c : Circuit) -> SplitResult c -> SplitResult (g ∷ c)
  split-step g hg hcs c (C , r , cl , ovr , eq , kr) =
    ⟦ g ⟧g * C , r , clifford-gate g hg hcs C cl , ovr ,
    trans (mat-*-assoc ⟦ g ⟧g C ⟦ r ⟧) (cong (λ m -> ⟦ g ⟧g * m) eq) ,
    subst (λ n -> kc r Nat.≤ 2 Nat.* n) (sym (csc-cons-0 g hcs c)) kr

  split-cs-step : CliffordK2 -> (c : Circuit) -> SplitResult c -> SplitResult (CS ∷ c)
  split-cs-step h c (C , r , cl , ovr , eq , kr) = go2 (h C cl)
    where
      go2 : Σ[ d ∈ Circuit ] (Over𝒢 d × Implements C d × (kc d Nat.≤ 2)) -> SplitResult (CS ∷ c)
      go2 (d , ovd , impld , kd) =
        1# , CS ∷ (d ++ r) , clifford-1 , cong₂ _∧_ refl (over-𝒢-++ d r ovd ovr) , eqn , kbd
        where
          eqn : 1# * ⟦ CS ∷ (d ++ r) ⟧ ≡ ⟦ CS ∷ c ⟧
          eqn = trans (mat-*-identityˡ ⟦ CS ∷ (d ++ r) ⟧)
                (cong (λ m -> ⟦ CS ⟧g * m)
                      (trans (⟦⟧-++ d r) (trans (cong (λ m -> m * ⟦ r ⟧) impld) eq)))
          kbd : kc (CS ∷ (d ++ r)) Nat.≤ 2 Nat.* csc (CS ∷ c)
          kbd = subst (λ n -> kc (CS ∷ (d ++ r)) Nat.≤ n) (sym (NatP.*-suc 2 (csc c)))
                (subst (λ n -> n Nat.≤ 2 Nat.+ 2 Nat.* csc c)
                       (sym (trans (kc-cons CS (d ++ r)) (kc-++ d r)))
                       (NatP.+-mono-≤ kd kr))

  split-cs : CliffordK2 -> (c : Circuit) -> Over𝒢 c -> SplitResult c
  split-cs h [] ov = 1# , [] , clifford-1 , refl , mat-*-identityˡ 1# , z≤n
  split-cs h (CS ∷ c) ov = split-cs-step h c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (CK ∷ c) ov = ⊥-elim (false≢true ov)
  split-cs h (KC ∷ c) ov = ⊥-elim (false≢true ov)
  split-cs h (X₀ ∷ c) ov = split-step X₀ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (X₁ ∷ c) ov = split-step X₁ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (Z₀ ∷ c) ov = split-step Z₀ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (Z₁ ∷ c) ov = split-step Z₁ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (S₀ ∷ c) ov = split-step S₀ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (S₁ ∷ c) ov = split-step S₁ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (K₀ ∷ c) ov = split-step K₀ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (K₁ ∷ c) ov = split-step K₁ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (CZ ∷ c) ov = split-step CZ refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (CX ∷ c) ov = split-step CX refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (XC ∷ c) ov = split-step XC refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (Ex ∷ c) ov = split-step Ex refl refl c (split-cs h c (proj₂ (∧-true ov)))
  split-cs h (Ii ∷ c) ov = split-step Ii refl refl c (split-cs h c (proj₂ (∧-true ov)))

-- Every circuit over 𝒢 can be replaced by one with at most
-- 2·rcs(c)+2 K gates.
kc-bound : CliffordK2 -> (c : Circuit) -> Over𝒢 c ->
           Σ[ c' ∈ Circuit ] (Over𝒢 c' × (⟦ c' ⟧ ≡ ⟦ c ⟧) × (kc c' Nat.≤ 2 Nat.* csc c Nat.+ 2))
kc-bound h c ov = go (split-cs h c ov)
  where
    Goal : Set
    Goal = Σ[ c' ∈ Circuit ] (Over𝒢 c' × (⟦ c' ⟧ ≡ ⟦ c ⟧) × (kc c' Nat.≤ 2 Nat.* csc c Nat.+ 2))
    go : SplitResult c -> Goal
    go (C , r , cl , ovr , eq , kr) = go2 (h C cl)
      where
        go2 : Σ[ d ∈ Circuit ] (Over𝒢 d × Implements C d × (kc d Nat.≤ 2)) -> Goal
        go2 (d , ovd , impld , kd) = d ++ r , over-𝒢-++ d r ovd ovr ,
          trans (⟦⟧-++ d r) (trans (cong (λ m -> m * ⟦ r ⟧) impld) eq) ,
          subst (λ n -> n Nat.≤ 2 Nat.* csc c Nat.+ 2) (sym (kc-++ d r))
            (subst (λ n -> kc d Nat.+ kc r Nat.≤ n) (NatP.+-comm 2 (2 Nat.* csc c))
                   (NatP.+-mono-≤ kd kr))

-- Theorem V.9, lower bound, in the integral form kc(A) ≤ 2·cs(A) + 2
-- (equivalently kc(A)/2 - 1 ≤ cs(A)).
thm-V9-lower : CliffordK2 -> (A : Op) (k s : ℕ) ->
               IsMinimalKCount A k -> HasCSCount A s -> k Nat.≤ 2 Nat.* s Nat.+ 2
thm-V9-lower h A k s mink (c , ov , impl , cs≡) = go (kc-bound h c ov)
  where
    go : Σ[ c' ∈ Circuit ] (Over𝒢 c' × (⟦ c' ⟧ ≡ ⟦ c ⟧) × (kc c' Nat.≤ 2 Nat.* csc c Nat.+ 2)) ->
         k Nat.≤ 2 Nat.* s Nat.+ 2
    go (c' , ov' , eq' , kb) =
      NatP.≤-trans (minimal-≤-raw-kc mink c' ov' (trans eq' impl))
                   (subst (λ n -> kc c' Nat.≤ 2 Nat.* n Nat.+ 2) cs≡ kb)

-- ----------------------------------------------------------------------
-- * Corollary V.10 and Remark V.11

-- Corollary V.10, with the CORRECTED constant: from cs ≥ k/2 - 1 one
-- gets (k+1)/cs ≤ 2(k+1)/(k-2) = 2 + 6/(k-2), and not 2 + 4/(k-2) as
-- printed in the paper. Since the counts are natural numbers, the
-- statement is given in cross-multiplied form; for k > 2 it says
--
--   (k+1)/cs ≤ (2·(k-2) + 6)/(k-2) = 2 + 6/(k-2).
cor-V-10 : (k s : ℕ) -> k Nat.≤ 2 Nat.* s Nat.+ 2 ->
           suc k Nat.* (k ∸ 2) Nat.≤ (2 Nat.* (k ∸ 2) Nat.+ 6) Nat.* s
cor-V-10 k s h = NatP.≤-trans step1 step2
  where
    k-2≤2s : k ∸ 2 Nat.≤ 2 Nat.* s
    k-2≤2s = subst (λ n -> k ∸ 2 Nat.≤ n) (NatP.m+n∸n≡m (2 Nat.* s) 2) (NatP.∸-monoˡ-≤ 2 h)
    step1 : suc k Nat.* (k ∸ 2) Nat.≤ suc k Nat.* (2 Nat.* s)
    step1 = NatP.*-monoʳ-≤ (suc k) k-2≤2s
    lin : suc k Nat.* (2 Nat.* s) ≡ (2 Nat.* suc k) Nat.* s
    lin = trans (sym (NatP.*-assoc (suc k) 2 s)) (cong (λ n -> n Nat.* s) (NatP.*-comm (suc k) 2))
    aux : (n : ℕ) -> 2 Nat.* suc n Nat.≤ 2 Nat.* (n ∸ 2) Nat.+ 6
    aux zero = s≤s (s≤s z≤n)
    aux (suc zero) = s≤s (s≤s (s≤s (s≤s z≤n)))
    aux (suc (suc n)) = NatP.≤-reflexive eq
      where
        sixify : (m : ℕ) -> 2 Nat.+ (2 Nat.+ (2 Nat.+ m)) ≡ m Nat.+ 6
        sixify m = trans (NatP.+-comm 2 (2 Nat.+ (2 Nat.+ m)))
                   (trans (cong (λ u -> u Nat.+ 2) (NatP.+-comm 2 (2 Nat.+ m)))
                   (trans (cong (λ u -> u Nat.+ 2 Nat.+ 2) (NatP.+-comm 2 m))
                          (trans (NatP.+-assoc (m Nat.+ 2) 2 2)
                                 (NatP.+-assoc m 2 4))))
        eq : 2 Nat.* suc (suc (suc n)) ≡ 2 Nat.* n Nat.+ 6
        eq = trans (NatP.*-suc 2 (suc (suc n)))
             (trans (cong (λ m -> 2 Nat.+ m) (NatP.*-suc 2 (suc n)))
             (trans (cong (λ m -> 2 Nat.+ (2 Nat.+ m)) (NatP.*-suc 2 n))
                    (sixify (2 Nat.* n))))
    step2 : suc k Nat.* (2 Nat.* s) Nat.≤ (2 Nat.* (k ∸ 2) Nat.+ 6) Nat.* s
    step2 = subst (λ n -> n Nat.≤ (2 Nat.* (k ∸ 2) Nat.+ 6) Nat.* s) (sym lin)
                  (NatP.*-monoˡ-≤ s (aux k))

-- The constant 4 printed in the paper is wrong: with k = 4 and
-- cs = 1 -- a pair that satisfies the hypothesis k ≤ 2·cs+2 of
-- Theorem V.9, and that occurs in the authors' own data set (21 of
-- the 12000 records have K-count 4 and CS-count 1) -- the claimed
-- bound (k+1)/cs ≤ 2 + 4/(k-2) reads 5 ≤ 4, which is false.
cor-V-10-paper-hypothesis : 4 Nat.≤ 2 Nat.* 1 Nat.+ 2
cor-V-10-paper-hypothesis = NatP.≤-refl

cor-V-10-paper-fails : ¬ (suc 4 Nat.* (4 ∸ 2) Nat.≤ (2 Nat.* (4 ∸ 2) Nat.+ 4) Nat.* 1)
cor-V-10-paper-fails h = NatP.≤⇒≤ᵇ h

-- The corrected bound is tight at k = 4, cs = 1.
cor-V-10-tight : suc 4 Nat.* (4 ∸ 2) ≡ (2 Nat.* (4 ∸ 2) Nat.+ 6) Nat.* 1
cor-V-10-tight = refl

-- Remark V.11: l - 2 ≤ cs(A) ≤ 2l + 1, given the bounds
-- 2l - 2 ≤ kc(A) ≤ 2l of Lemma IV.7 (Table II).
remark-V-11-upper : (l k s : ℕ) -> k Nat.≤ 2 Nat.* l -> s Nat.≤ suc k -> s Nat.≤ suc (2 Nat.* l)
remark-V-11-upper l k s hk hs = NatP.≤-trans hs (s≤s hk)

remark-V-11-lower : (l k s : ℕ) -> 2 Nat.* l ∸ 2 Nat.≤ k -> k Nat.≤ 2 Nat.* s Nat.+ 2 ->
                    l ∸ 2 Nat.≤ s
remark-V-11-lower l k s hk hs =
  subst (λ n -> l ∸ 2 Nat.≤ n) (NatP.m+n∸n≡m s 2) (NatP.∸-monoˡ-≤ 2 l≤s+2)
  where
    h1 : 2 Nat.* l ∸ 2 Nat.≤ 2 Nat.* s Nat.+ 2
    h1 = NatP.≤-trans hk hs
    h2 : 2 Nat.* l Nat.≤ 2 Nat.+ (2 Nat.* s Nat.+ 2)
    h2 = NatP.≤-trans (NatP.m≤n+m∸n (2 Nat.* l) 2) (NatP.+-monoʳ-≤ 2 h1)
    h3 : 2 Nat.+ (2 Nat.* s Nat.+ 2) ≡ 2 Nat.* (s Nat.+ 2)
    h3 = trans (trans (NatP.+-comm 2 (2 Nat.* s Nat.+ 2)) (NatP.+-assoc (2 Nat.* s) 2 2))
               (sym (NatP.*-distribˡ-+ 2 s 2))
    h4 : 2 Nat.* l Nat.≤ 2 Nat.* (s Nat.+ 2)
    h4 = subst (λ n -> 2 Nat.* l Nat.≤ n) h3 h2
    l≤s+2 : l Nat.≤ s Nat.+ 2
    l≤s+2 = NatP.*-cancelˡ-≤ 2 h4

-- ----------------------------------------------------------------------
-- * Lemma V.5: the exterior of a K-optimal descent is K-optimal

-- If a descent of A is K-optimal and is split into a sub-descent
-- (a prefix) and its exterior (the remaining steps, including all
-- their K gates), then the exterior is a K-optimal descent of the
-- target of the sub-descent. This is the exchange argument of the
-- paper: a cheaper exterior could be substituted into the whole
-- descent.
lemma-V-5 : (A : Op) (pre post : List Step) ->
            K-optimal-descent A (pre ++ post) ->
            K-optimal-descent (run pre A) post
lemma-V-5 A pre post (_ , least) = (post , NatP.≤-refl , refl) , minimality
  where
    tgt : lde (run post (run pre A)) ≡ lde (run (pre ++ post) A)
    tgt = cong (λ M -> lde M) (sym (run-++ pre post A))
    minimality : (j : ℕ) -> HasDescentKCount (run pre A) (lde (run post (run pre A))) j ->
                 steps-kc post Nat.≤ j
    minimality j (ss , hss , kss) = NatP.+-cancelˡ-≤ (steps-kc pre) _ _ bound
      where
        reach : lde (run (pre ++ ss) A) Nat.≤ lde (run (pre ++ post) A)
        reach = subst₂ (λ x y -> lde x Nat.≤ lde y)
                       (sym (run-++ pre ss A)) (sym (run-++ pre post A)) hss
          where
            subst₂ : {X : Set} {x x' y y' : X} (P : X -> X -> Set) -> x ≡ x' -> y ≡ y' -> P x y -> P x' y'
            subst₂ P refl refl p = p
        cand : HasDescentKCount A (lde (run (pre ++ post) A)) (steps-kc pre Nat.+ j)
        cand = pre ++ ss , reach , trans (steps-kc-++ pre ss) (cong (λ n -> steps-kc pre Nat.+ n) kss)
        bound : steps-kc pre Nat.+ steps-kc post Nat.≤ steps-kc pre Nat.+ j
        bound = subst (λ n -> n Nat.≤ steps-kc pre Nat.+ j) (steps-kc-++ pre post)
                      (least (steps-kc pre Nat.+ j) cand)

-- ----------------------------------------------------------------------
-- * From circuits to descents, and back
--
-- A circuit for A with raw K-count n gives a descent of A to lde 0
-- with K-count n, and conversely (Lemma IV.9). K⁻¹ = iK, so the
-- inverse of a K₁ gate is a K₁ gate followed by a generalized
-- permutation.

private
  i-gp minus-i-gp : GP
  i-gp = gperm id4p (ph1 , ph1 , ph1 , ph1) refl
  minus-i-gp = gperm id4p (ph3 , ph3 , ph3 , ph3) refl

  k1k1 : ⟦ K₁ ⟧g * ⟦ K₁ ⟧g ≡ gp-mat minus-i-gp
  k1k1 = ==⇒≡ refl

  i-minus-i : gp-mat i-gp * gp-mat minus-i-gp ≡ 1#
  i-minus-i = trans (gp-mat-comp i-gp minus-i-gp) gp-one-mat

  lde-1 : lde (1# {A = Op}) ≡ 0
  lde-1 = refl

-- Remark II.10, first half (K decreases the lde by at most one), is
-- proved for a pair of entries in Kopt.Properties.LdeLemmas, under
-- the name remark-II-10. Its matrix form,
--
--    lde A ≤ suc (lde (⟦K₁⟧g · A)),
--
-- follows from lde-*-≤ and K₁⁻¹ = i·K₁. Proving it here would make the
-- type checker normalise concrete 4×4 products of dyadic complex
-- numbers and push this module past the twenty minute limit of
-- agda-check.sh, so it is proved in Kopt.OptInduction instead
-- (lde-K-down and lde-K-down-r, with the K-free directions lde-K-up
-- and lde-K-up-r).

alt-descent : (a : Alt) ->
              Σ[ ss ∈ List Step ] ((run ss (alt-mat a) ≡ 1#) × (steps-kc ss ≡ alt-kc a))
alt-descent (alt-nil G) = gp-left (gp-inverse G) ∷ [] , gp-inverse-left G , refl
alt-descent (alt-cons G a) = go (alt-descent a)
  where
    M : Op
    M = gp-mat G * (⟦ K₁ ⟧g * alt-mat a)
    reduce : gp-mat i-gp * (⟦ K₁ ⟧g * (gp-mat (gp-inverse G) * M)) ≡ alt-mat a
    reduce = begin
      gp-mat i-gp * (⟦ K₁ ⟧g * (gp-mat (gp-inverse G) * M))
        ≡⟨ cong (λ m -> gp-mat i-gp * (⟦ K₁ ⟧g * m)) inner ⟩
      gp-mat i-gp * (⟦ K₁ ⟧g * (⟦ K₁ ⟧g * alt-mat a))
        ≡⟨ cong (λ m -> gp-mat i-gp * m) (sym (mat-*-assoc ⟦ K₁ ⟧g ⟦ K₁ ⟧g (alt-mat a))) ⟩
      gp-mat i-gp * ((⟦ K₁ ⟧g * ⟦ K₁ ⟧g) * alt-mat a)
        ≡⟨ cong (λ m -> gp-mat i-gp * (m * alt-mat a)) k1k1 ⟩
      gp-mat i-gp * (gp-mat minus-i-gp * alt-mat a)
        ≡⟨ sym (mat-*-assoc (gp-mat i-gp) (gp-mat minus-i-gp) (alt-mat a)) ⟩
      (gp-mat i-gp * gp-mat minus-i-gp) * alt-mat a
        ≡⟨ cong (λ m -> m * alt-mat a) i-minus-i ⟩
      1# * alt-mat a
        ≡⟨ mat-*-identityˡ (alt-mat a) ⟩
      alt-mat a ∎
      where
        open ≡-Reasoning
        inner : gp-mat (gp-inverse G) * M ≡ ⟦ K₁ ⟧g * alt-mat a
        inner = trans (sym (mat-*-assoc (gp-mat (gp-inverse G)) (gp-mat G) (⟦ K₁ ⟧g * alt-mat a)))
                      (trans (cong (λ m -> m * (⟦ K₁ ⟧g * alt-mat a)) (gp-inverse-left G))
                             (mat-*-identityˡ (⟦ K₁ ⟧g * alt-mat a)))
    go : Σ[ ss ∈ List Step ] ((run ss (alt-mat a) ≡ 1#) × (steps-kc ss ≡ alt-kc a)) ->
         Σ[ ss ∈ List Step ] ((run ss M ≡ 1#) × (steps-kc ss ≡ suc (alt-kc a)))
    go (ss , r , k) =
      gp-left (gp-inverse G) ∷ K-left ∷ gp-left i-gp ∷ ss ,
      trans (cong (λ m -> run ss m) reduce) r ,
      cong suc k

-- A circuit for A with raw K-count n yields a descent of A to lde 0
-- with K-count n.
circuit-to-descent : (A : Op) (n : ℕ) -> HasKCount A n -> HasDescentKCount A 0 n
circuit-to-descent A n (c , ov , impl , kc≡) = go (equation-3 c ov)
  where
    go : Σ[ a ∈ Alt ] ((alt-mat a ≡ ⟦ c ⟧) × (alt-kc a ≡ kc c)) -> HasDescentKCount A 0 n
    go (a , ma , ka) = go2 (alt-descent a)
      where
        A≡ : alt-mat a ≡ A
        A≡ = trans ma impl
        go2 : Σ[ ss ∈ List Step ] ((run ss (alt-mat a) ≡ 1#) × (steps-kc ss ≡ alt-kc a)) ->
              HasDescentKCount A 0 n
        go2 (ss , r , k) = ss ,
          NatP.≤-reflexive (trans (cong (λ m -> lde m)
                                        (trans (cong (λ m -> run ss m) (sym A≡)) r)) lde-1) ,
          trans k (trans ka kc≡)

-- The K-optimality half of Corollary V.8: a K-optimal descent of A
-- that reaches lde 0 bounds the K-count of every circuit for A.
K-optimal-descent-bound : (A : Op) (ss : List Step) ->
  K-optimal-descent A ss -> lde (run ss A) ≡ 0 ->
  (n : ℕ) -> HasKCount A n -> steps-kc ss Nat.≤ n
K-optimal-descent-bound A ss (_ , least) z n hn =
  least n (subst (λ m -> HasDescentKCount A m n) (sym z) (circuit-to-descent A n hn))

-- ----------------------------------------------------------------------
-- * The statements that are not proved here
--
-- Lemmas V.3, V.4, V.6 and V.7 are proved in the paper "by
-- enumeration" over the finite residue data. They are stated here,
-- and the results that use them take them as hypotheses.

-- The undashed (lde-decreasing) edges of Figure 1, on patterns.
fig1-drop-of : Maybe SixCases -> Maybe SixCases -> Bool
fig1-drop-of (just s) (just t) = fig1-drop s t
fig1-drop-of _ _ = false

-- Lemma V.3: any path 1-descent is K-optimal.
Lemma-V-3 : Set
Lemma-V-3 = (A : Op) (ss : List Step) -> IsPathDescent A ss ->
            suc (lde (run ss A)) ≡ lde A -> K-optimal-descent A ss

-- Lemma V.4 (pattern-locking): the source-target pattern of any
-- K-count-1 1-descent matches an undashed edge of Figure 1.
Lemma-V-4 : Set
Lemma-V-4 = (A : Op) (ss : List Step) -> steps-kc ss ≡ 1 ->
            suc (lde (run ss A)) ≡ lde A ->
            fig1-drop-of (patof A) (patof (run ss A)) ≡ true

-- Lemma V.6: a K-count-1 0-descent from pattern (vi) cannot reach
-- pattern (ii) or pattern (v).
Lemma-V-6 : Set
Lemma-V-6 = (A : Op) (ss : List Step) -> steps-kc ss ≡ 1 ->
            lde (run ss A) ≡ lde A -> patof A ≡ just VI ->
            ¬ (patof (run ss A) ≡ just II) × ¬ (patof (run ss A) ≡ just V)

-- Lemma V.7: every complete path descent is K-optimal.
Lemma-V-7 : Set
Lemma-V-7 = (A : Op) (ss : List Step) -> IsCompletePathDescent A ss -> K-optimal-descent A ss

-- ----------------------------------------------------------------------
-- * Corollary V.8 and Lemma IV.9

-- Lemma IV.9: kc(A) ≤ prkc(A). The hypothesis is that the circuit
-- produced by synth implements A with raw K-count prkc(A); that is a
-- property of the algorithm of Section IV C, checked on the authors'
-- data set in Test.KoptSynthRun and Test.KoptOptimalityRun, and not
-- proved here.
lemma-IV-9 : (A : Op) -> HasKCount A (prkc A) -> (n : ℕ) -> IsMinimalKCount A n -> n Nat.≤ prkc A
lemma-IV-9 A h n (_ , least) = least (prkc A) h

-- Corollary V.8, K-optimality half: if the descent realised by synth
-- is a complete path descent with K-count prkc(A), and Lemma V.7
-- holds, then prkc(A) is the optimal K-count kc(A).
cor-V-8-K-optimal : Lemma-V-7 -> (A : Op) (ss : List Step) ->
                    IsCompletePathDescent A ss -> steps-kc ss ≡ prkc A ->
                    HasKCount A (prkc A) -> IsMinimalKCount A (prkc A)
cor-V-8-K-optimal lem A ss cpd k≡ has = has , least
  where
    least : (m : ℕ) -> HasKCount A m -> prkc A Nat.≤ m
    least m hm = subst (λ n -> n Nat.≤ m) k≡
      (K-optimal-descent-bound A ss (lem A ss cpd) (proj₂ cpd) m hm)
