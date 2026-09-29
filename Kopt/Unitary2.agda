-- Lemmas IV.2 and IV.3 of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026),
--
-- at the residue level: the counting facts that their proofs rest on.
--
-- This is the second half of Kopt.Unitary, which it re-exports. The
-- first half reads the entries of U†U, UU† and ρˡ₁(U) off the entries
-- of U; this half is the arithmetic: Lemma II.5 makes
-- parity : ℤ[i] → ℤ₂ additive and multiplicative, so from
--
--   Σₖ Uₖ꜀·(Uₖᵣ)† = t   (t = 1 for r = c and 0 otherwise)
--
-- and γˡUₖⱼ = Xₖⱼ ∈ ℤ[i] one gets Σₖ parity(Xₖ꜀)·parity(Xₖᵣ) =
-- parity(t·2ˡ), which is
--
--  * for l > 0 and r = c: the number of odd entries of a column of
--    ρˡ₁(U) is EVEN -- the key fact in the paper's proof of Lemma IV.2
--    ("Σ∥wⱼ∥² = ∥w∥² ≡ 0 mod γ");
--  * for l = 0 and r = c: it is ODD;
--  * for r ≠ c: the number of positions where two distinct columns are
--    both odd is EVEN -- the key fact of Lemma IV.3;
--
-- and the same for the rows. The module is split off from Kopt.Unitary
-- so that each half stays inside the twenty minute limit of
-- agda-check.sh.

{-# OPTIONS --without-K --safe #-}

module Kopt.Unitary2 where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Properties.Algebra
open import Kopt.Unitary public

private
  module DR = IsCommutativeRing isCommutativeRing-DComplex
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex
  module AD = IsInvolutiveRingEndo adj-DComplex

  Op : Set
  Op = Matrix 4 4 DComplex

-- ----------------------------------------------------------------------
-- * Parity of a sum of four products (Lemma II.5)

private
  P : ZComplex -> Z2
  P = parityℤ[i]

  parity-sum4 : (X₀ X₁ X₂ X₃ : ZComplex) ->
                P (sum4 X₀ X₁ X₂ X₃) ≡ sum4 (P X₀) (P X₁) (P X₂) (P X₃)
  parity-sum4 X₀ X₁ X₂ X₃ =
    trans (parity-+ X₀ (X₁ + (X₂ + X₃)))
          (cong (λ z -> P X₀ + z)
                (trans (parity-+ X₁ (X₂ + X₃))
                       (cong (λ z -> P X₁ + z) (parity-+ X₂ X₃))))

-- The parity of Σₖ XₖYₖ is Σₖ parity(Xₖ)·parity(Yₖ).
parity-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ZComplex) ->
             P (sum4 (X₀ * Y₀) (X₁ * Y₁) (X₂ * Y₂) (X₃ * Y₃))
               ≡ sum4 (P X₀ * P Y₀) (P X₁ * P Y₁) (P X₂ * P Y₂) (P X₃ * P Y₃)
parity-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
  trans (parity-sum4 (X₀ * Y₀) (X₁ * Y₁) (X₂ * Y₂) (X₃ * Y₃))
        (cong₂ (λ p q -> p + q) (parity-* X₀ Y₀)
               (cong₂ (λ p q -> p + q) (parity-* X₁ Y₁)
                      (cong₂ (λ p q -> p + q) (parity-* X₂ Y₂) (parity-* X₃ Y₃))))

-- ρ₂ is stable under conjugation (Section II B), so parity is too.
parity-adj : (X : ZComplex) -> P (X †) ≡ P X
parity-adj X = trans (sym (ρ-head 1 (X †))) (trans (cong Vec.head (ρ₂-adj X)) (ρ-head 1 X))
  where open import Data.Vec.Base as Vec using (head)

-- ----------------------------------------------------------------------
-- ----------------------------------------------------------------------
-- * Scaling an inner product to ℤ[i]
--
-- If g·g† = G and each xₖ·g and yₖ·g is the Gaussian integer Xₖ resp.
-- Yₖ, then Σₖ Xₖ(Yₖ)† = (Σₖ xₖ(yₖ)†)·G.
--
-- Performance: this is pure bookkeeping -- the ring axioms plus the fact
-- that from-whole is an injective ring homomorphism commuting with the
-- adjoint -- so it is proved for an ABSTRACT commutative ring A with an
-- injective homomorphism from a ring B, and instantiated at 𝔻[i] and
-- ℤ[i] afterwards. This is the rule recorded in Kopt.Unitary: over 𝔻[i]
-- every product unfolds into the dyadic arithmetic, a smart constructor
-- with a stuck parity test inside an eta record, and each line of the
-- chain below contains four threefold products, so the 𝔻[i] version of
-- this one lemma needed more than four gigabytes of heap.
private
  from-whole-adj : (X : ZComplex) -> (DComplex ∋ from-whole (X †)) ≡ (from-whole X) †
  from-whole-adj (Cplx a b) = cong (λ z -> Cplx (from-whole a) z) (fromℤ-neg b)

module ScaleGen {A B : Set} {{_ : Ring A}} {{_ : Adjoint A}} {{_ : Ring B}} {{_ : Adjoint B}}
                (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
                (adj-* : (x y : A) -> ((x * y) †) ≡ (x †) * (y †))
                (f : B -> A)
                (f-+ : (x y : B) -> f (x + y) ≡ f x + f y)
                (f-* : (x y : B) -> f (x * y) ≡ f x * f y)
                (f-adj : (x : B) -> f (x †) ≡ (f x) †)
                (f-inj : {x y : B} -> f x ≡ f y -> x ≡ y) where
  private
    module R = IsCommutativeRing isCR
    module L = CRLemmas isCR

    distrib4 : (x y z w e : A) ->
               sum4 (x * e) (y * e) (z * e) (w * e) ≡ sum4 x y z w * e
    distrib4 x y z w e =
      sym (trans (R.distribʳ e x (y + (z + w)))
                 (cong (λ u -> x * e + u)
                       (trans (R.distribʳ e y (z + w))
                              (cong (λ u -> y * e + u) (R.distribʳ e z w)))))

    -- (x·g)·((y·g)†) = (x·y†)·(g·g†)
    one-term : (x y g : A) -> (x * g) * ((y * g) †) ≡ (x * (y †)) * (g * (g †))
    one-term x y g = trans (cong (λ u -> (x * g) * u) (adj-* y g))
                           (L.interchange x g (y †) (g †))

    -- f of a four-term inner product.
    f-ip4 : (X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : B) ->
            f (sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
              ≡ sum4 (f X₀ * ((f Y₀) †)) (f X₁ * ((f Y₁) †))
                     (f X₂ * ((f Y₂) †)) (f X₃ * ((f Y₃) †))
    f-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ =
      trans (f-+ (X₀ * (Y₀ †)) _)
            (cong₂ (λ p q -> p + q) (term X₀ Y₀)
                   (trans (f-+ (X₁ * (Y₁ †)) _)
                          (cong₂ (λ p q -> p + q) (term X₁ Y₁)
                                 (trans (f-+ (X₂ * (Y₂ †)) _)
                                        (cong₂ (λ p q -> p + q) (term X₂ Y₂) (term X₃ Y₃))))))
      where
        term : (X Y : B) -> f (X * (Y †)) ≡ f X * ((f Y) †)
        term X Y = trans (f-* X (Y †)) (cong (λ z -> f X * z) (f-adj Y))

    cg8 : {p₀ q₀ p₁ q₁ p₂ q₂ p₃ q₃ u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ : A} ->
          p₀ ≡ u₀ -> q₀ ≡ v₀ -> p₁ ≡ u₁ -> q₁ ≡ v₁ ->
          p₂ ≡ u₂ -> q₂ ≡ v₂ -> p₃ ≡ u₃ -> q₃ ≡ v₃ ->
          sum4 (p₀ * (q₀ †)) (p₁ * (q₁ †)) (p₂ * (q₂ †)) (p₃ * (q₃ †))
            ≡ sum4 (u₀ * (v₀ †)) (u₁ * (v₁ †)) (u₂ * (v₂ †)) (u₃ * (v₃ †))
    cg8 refl refl refl refl refl refl refl refl = refl

    cg4 : {p₀ p₁ p₂ p₃ u₀ u₁ u₂ u₃ : A} ->
          p₀ ≡ u₀ -> p₁ ≡ u₁ -> p₂ ≡ u₂ -> p₃ ≡ u₃ ->
          sum4 p₀ p₁ p₂ p₃ ≡ sum4 u₀ u₁ u₂ u₃
    cg4 refl refl refl refl = refl

  scale-ipc′ : (g : A) (G : B) -> g * (g †) ≡ f G ->
               (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : A)
               (X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ T : B) ->
               x₀ * g ≡ f X₀ -> x₁ * g ≡ f X₁ ->
               x₂ * g ≡ f X₂ -> x₃ * g ≡ f X₃ ->
               y₀ * g ≡ f Y₀ -> y₁ * g ≡ f Y₁ ->
               y₂ * g ≡ f Y₂ -> y₃ * g ≡ f Y₃ ->
               ipc (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ []) ≡ f T ->
               sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)) ≡ T * G
  scale-ipc′ g G hg x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ T
             e₀ e₁ e₂ e₃ f₀ f₁ f₂ f₃ hip = f-inj (begin
    f (sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
      ≡⟨ f-ip4 X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ ⟩
    sum4 (f X₀ * ((f Y₀) †)) (f X₁ * ((f Y₁) †)) (f X₂ * ((f Y₂) †)) (f X₃ * ((f Y₃) †))
      ≡⟨ cg8 (sym e₀) (sym f₀) (sym e₁) (sym f₁) (sym e₂) (sym f₂) (sym e₃) (sym f₃) ⟩
    sum4 ((x₀ * g) * ((y₀ * g) †)) ((x₁ * g) * ((y₁ * g) †))
         ((x₂ * g) * ((y₂ * g) †)) ((x₃ * g) * ((y₃ * g) †))
      ≡⟨ cg4 (one-term x₀ y₀ g) (one-term x₁ y₁ g) (one-term x₂ y₂ g) (one-term x₃ y₃ g) ⟩
    sum4 ((x₀ * (y₀ †)) * (g * (g †))) ((x₁ * (y₁ †)) * (g * (g †)))
         ((x₂ * (y₂ †)) * (g * (g †))) ((x₃ * (y₃ †)) * (g * (g †)))
      ≡⟨ distrib4 (x₀ * (y₀ †)) (x₁ * (y₁ †)) (x₂ * (y₂ †)) (x₃ * (y₃ †)) (g * (g †)) ⟩
    ipc (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ []) * (g * (g †))
      ≡⟨ cong₂ (λ p q -> p * q) hip hg ⟩
    f T * f G
      ≡⟨ sym (f-* T G) ⟩
    f (T * G) ∎)
    where open ≡-Reasoning

-- The instance used: A = 𝔻[i], B = ℤ[i], f = from-whole.
--
-- Performance, and a trap worth recording: from-whole is a class method,
--
--   from-whole : {A B : Set} {{_ : WholePart A B}} -> B -> A,
--
-- so handing the bare method to a module whose two type parameters are
-- still metavariables makes instance search enumerate every WholePart
-- instance of the framework and elaborate the remaining twelve arguments
-- against each of them; with that the instantiation below did not finish
-- in 200 s, although the generic proof itself takes 0.4 s. Both types are
-- therefore pinned, in fw and in the module application. (This is the
-- same failure mode as writing `fromℕ 2 {ZComplex}`.)
private
  fw : ZComplex -> DComplex
  fw X = from-whole X

  module SG = ScaleGen {DComplex} {ZComplex} isCommutativeRing-DComplex AD.f-* fw
                       from-whole-+ from-whole-* from-whole-adj from-whole-injective

abstract
  scale-ipc : (g : DComplex) (G : ZComplex) -> g * (g †) ≡ from-whole G ->
              (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : DComplex)
              (X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ T : ZComplex) ->
              x₀ * g ≡ from-whole X₀ -> x₁ * g ≡ from-whole X₁ ->
              x₂ * g ≡ from-whole X₂ -> x₃ * g ≡ from-whole X₃ ->
              y₀ * g ≡ from-whole Y₀ -> y₁ * g ≡ from-whole Y₁ ->
              y₂ * g ≡ from-whole Y₂ -> y₃ * g ≡ from-whole Y₃ ->
              ipc (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ []) ≡ from-whole T ->
              sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)) ≡ T * G
  scale-ipc = SG.scale-ipc′

-- The same for the shape Σₖ (uₖ)†·wₖ of U·U†.
private
  ipr-ipc : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}}
            (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) ->
            (u w : Vector 4 A) -> ipr u w ≡ ipc w u
  ipr-ipc {A} isCR (u₀ ∷ u₁ ∷ u₂ ∷ u₃ ∷ []) (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []) =
    cg8w (R.*-comm (u₀ †) w₀) (R.*-comm (u₁ †) w₁) (R.*-comm (u₂ †) w₂) (R.*-comm (u₃ †) w₃)
    where
      module R = IsCommutativeRing isCR
      cg8w : {p₀ p₁ p₂ p₃ u₀ u₁ u₂ u₃ : A} ->
              p₀ ≡ u₀ -> p₁ ≡ u₁ -> p₂ ≡ u₂ -> p₃ ≡ u₃ ->
              sum4 p₀ p₁ p₂ p₃ ≡ sum4 u₀ u₁ u₂ u₃
      cg8w refl refl refl refl = refl

ipr-ipc-D : (u w : Vector 4 DComplex) -> ipr u w ≡ ipc w u
ipr-ipc-D = ipr-ipc isCommutativeRing-DComplex

-- ----------------------------------------------------------------------
-- * The norm of γˡ

-- The Gaussian integer 2 = γ·γ†. It is named, and public, because the
-- type of every parity count below mentions 2ˡ: the type argument of
-- fromℕ precedes its natural number argument (Typeclasses opens
-- SemiRing with {{...}}), so `fromℕ 2 {ZComplex}` is not well formed,
-- and leaving the type to instance search does not determine it.
2ℤℂ : ZComplex
2ℤℂ = fromℕ 2

-- γˡ·(γˡ)† = 2ˡ.
gamma-norm : (l : ℕ) -> (γ {DComplex} ↑ l) * ((γ {DComplex} ↑ l) †)
                          ≡ from-whole (2ℤℂ ↑ l)
gamma-norm zero = trans (cong (λ z -> 1# * z) AD.f-1) (DR.*-identityˡ 1#)
gamma-norm (suc l) = begin
  (γ * (γ ↑ l)) * ((γ * (γ ↑ l)) †)
    ≡⟨ cong (λ z -> (γ * (γ ↑ l)) * z) (AD.f-* γ (γ ↑ l)) ⟩
  (γ * (γ ↑ l)) * ((γ †) * ((γ ↑ l) †))
    ≡⟨ DL.interchange γ (γ ↑ l) (γ †) ((γ ↑ l) †) ⟩
  (γ * (γ †)) * ((γ ↑ l) * ((γ ↑ l) †))
    ≡⟨ cong₂ (λ p q -> p * q) base (gamma-norm l) ⟩
  from-whole 2ℤℂ * from-whole (2ℤℂ ↑ l)
    ≡⟨ sym (from-whole-* 2ℤℂ (2ℤℂ ↑ l)) ⟩
  (DComplex ∋ from-whole (2ℤℂ * (2ℤℂ ↑ l))) ∎
  where
    open ≡-Reasoning
    base : (γ {DComplex}) * ((γ {DComplex}) †) ≡ from-whole 2ℤℂ
    base = refl

-- The parity of 2ˡ: odd for l = 0, even for l > 0.
parity-2↑ : (k : ℕ) -> P (2ℤℂ ↑ suc k) ≡ Even
parity-2↑ k = trans (parity-* 2ℤℂ (2ℤℂ ↑ k))
                    (cong (λ z -> z * P (2ℤℂ ↑ k)) two-even)
  where
    two-even : P 2ℤℂ ≡ Even
    two-even = refl

parity-2↑0 : P (2ℤℂ ↑ 0) ≡ Odd
parity-2↑0 = refl

-- ----------------------------------------------------------------------
-- * Small η laws for 4-vectors

vec4-η : {A : Set} (v : Vector 4 A) ->
         v ≡ (vsel ι0 v ∷ vsel ι1 v ∷ vsel ι2 v ∷ vsel ι3 v ∷ [])
vec4-η (a ∷ b ∷ c ∷ d ∷ []) = refl

odd-count-η : (v : Vector 4 Z2) ->
              odd-count v ≡ sum4 (vsel ι0 v) (vsel ι1 v) (vsel ι2 v) (vsel ι3 v)
odd-count-η (a ∷ b ∷ c ∷ d ∷ []) = refl

meet-count-η : (v w : Vector 4 Z2) ->
               meet-count v w ≡ sum4 (vsel ι0 v * vsel ι0 w) (vsel ι1 v * vsel ι1 w)
                                     (vsel ι2 v * vsel ι2 w) (vsel ι3 v * vsel ι3 w)
meet-count-η (a ∷ b ∷ c ∷ d ∷ []) (p ∷ q ∷ r ∷ s ∷ []) = refl

-- ----------------------------------------------------------------------
-- * The residue of an entry

-- If γˡ·x is the Gaussian integer X, then ρˡ₁ of that entry is the
-- parity of X.
res1-of : (U : Op) (l : ℕ) (r c : Ix) (X : ZComplex) ->
          ment r c U * (γ ↑ l) ≡ from-whole X ->
          ment r c (residue1-matrix l U) ≡ P X
res1-of U l r c X hx =
  trans (entry-res1 U l r c) (cong P (trans (cong to-whole hx) (to-whole-from-whole X)))

-- ----------------------------------------------------------------------
-- * The counting core
--
-- Everything below is an instance of this one statement, whose
-- arguments are ℤ[i]-variables ONLY: if Σₖ Xₖ(Yₖ)† = t·2ˡ in ℤ[i], then
--
--   Σₖ parity(Xₖ)·parity(Yₖ) = parity(t·2ˡ).
--
-- The 𝔻[i] half -- that the Gaussian integers γˡ·Uᵣ꜀ of two columns or
-- two rows do satisfy that equation -- is col-ints and row-ints below,
-- each a single instance of scale-ipc. Keeping the two halves apart is
-- what makes this module affordable: scale-ipc is the expensive
-- statement (eight 𝔻[i] variables, eight integrality equations and an
-- inner product, all of which the conversion checker has to unify
-- against terms in which a matrix variable appears as sixteen
-- projections), and it is now instantiated twice -- once for columns,
-- once for rows -- instead of four times.
private
  z2-square : (p : Z2) -> p * p ≡ p
  z2-square Even = refl
  z2-square Odd = refl

  pair-parity : (X Y : ZComplex) -> P X * P (Y †) ≡ P X * P Y
  pair-parity X Y = cong (λ z -> P X * z) (parity-adj Y)

  sum4-cong : {A : Set} {{_ : SemiRing A}} {p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : A} ->
              p₀ ≡ q₀ -> p₁ ≡ q₁ -> p₂ ≡ q₂ -> p₃ ≡ q₃ ->
              sum4 p₀ p₁ p₂ p₃ ≡ sum4 q₀ q₁ q₂ q₃
  sum4-cong refl refl refl refl = refl

count-core : (X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ S : ZComplex) ->
             sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)) ≡ S ->
             sum4 (P X₀ * P Y₀) (P X₁ * P Y₁) (P X₂ * P Y₂) (P X₃ * P Y₃) ≡ P S
count-core X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ S hip = begin
  sum4 (P X₀ * P Y₀) (P X₁ * P Y₁) (P X₂ * P Y₂) (P X₃ * P Y₃)
    ≡⟨ sym (sum4-cong (pair-parity X₀ Y₀) (pair-parity X₁ Y₁)
                      (pair-parity X₂ Y₂) (pair-parity X₃ Y₃)) ⟩
  sum4 (P X₀ * P (Y₀ †)) (P X₁ * P (Y₁ †)) (P X₂ * P (Y₂ †)) (P X₃ * P (Y₃ †))
    ≡⟨ sym (parity-ip4 X₀ (Y₀ †) X₁ (Y₁ †) X₂ (Y₂ †) X₃ (Y₃ †)) ⟩
  P (sum4 (X₀ * (Y₀ †)) (X₁ * (Y₁ †)) (X₂ * (Y₂ †)) (X₃ * (Y₃ †)))
    ≡⟨ cong P hip ⟩
  P S ∎
  where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * The Gaussian integers γˡ·Uᵣ꜀

private
  wit : (U : Op) (l : ℕ) -> lde U Nat.≤ l -> (r c : Ix) -> DenomExpγ l (ment r c U)
  wit U l hl r c =
    DenomExpγ-≤ (NatP.≤-trans (entry-lde U r c) hl) (lde-denom-exp (ment r c U))

  W : (U : Op) (l : ℕ) -> lde U Nat.≤ l -> Ix -> Ix -> ZComplex
  W U l hl r c = whole (wit U l hl r c)

  Weq : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) ->
        ment r c U * (γ ↑ l) ≡ from-whole (W U l hl r c)
  Weq U l hl r c = whole-eq (wit U l hl r c)

  -- The kth entry of a row.
  vsel-mrow : {A : Set} (M : Matrix 4 4 A) (r c : Ix) -> vsel c (mrow r M) ≡ ment r c M
  vsel-mrow (Matrix' (u ∷ v ∷ w ∷ z ∷ [])) r ι0 = refl
  vsel-mrow (Matrix' (u ∷ v ∷ w ∷ z ∷ [])) r ι1 = refl
  vsel-mrow (Matrix' (u ∷ v ∷ w ∷ z ∷ [])) r ι2 = refl
  vsel-mrow (Matrix' (u ∷ v ∷ w ∷ z ∷ [])) r ι3 = refl

  subst2 : {A B : Set} {x x2 : A} {y y2 : B} (Q : A -> B -> Set) ->
           x ≡ x2 -> y ≡ y2 -> Q x y -> Q x2 y2
  subst2 Q refl refl q = q

  mul2 : Z2 -> Z2 -> Z2
  mul2 p q = p * q

  cong4D : {p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : DComplex} ->
           p₀ ≡ q₀ -> p₁ ≡ q₁ -> p₂ ≡ q₂ -> p₃ ≡ q₃ ->
           (Vector 4 DComplex ∋ (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ [])) ≡ (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ [])
  cong4D refl refl refl refl = refl

  row-η4 : (U : Op) (j : Ix) ->
           mrow j U ≡ (ment j ι0 U ∷ ment j ι1 U ∷ ment j ι2 U ∷ ment j ι3 U ∷ [])
  row-η4 U j = trans (vec4-η (mrow j U))
                     (cong4D (vsel-mrow U j ι0) (vsel-mrow U j ι1)
                             (vsel-mrow U j ι2) (vsel-mrow U j ι3))

-- ----------------------------------------------------------------------
-- * The Gaussian integers of the entries, exported
--
-- Kopt.PatternFacts needs the integers γˡ·Uᵣ꜀ themselves, not only the
-- parity counts: at lde 0 the norm identity Σₖ ∥Xₖ∥² = 1 is what forces
-- ρ⁰₁(U) to be a permutation matrix over ℤ₂ (a column cannot have
-- three odd entries).

-- Abstract: int-entry hides the witness whole (wit U l hl r c), whose
-- unfolding is a chain of DenomExpγ-suc applications (the most expensive
-- definition of Kopt.Properties.Lde), and col-ints/row-ints hide the two
-- instances of scale-ipc. Kopt.PatternFacts uses all five heavily.
abstract
  -- The Gaussian integer γˡ·Uᵣ꜀, for l a denominator exponent of U.
  int-entry : (U : Op) (l : ℕ) -> lde U Nat.≤ l -> Ix -> Ix -> ZComplex
  int-entry = W

  int-entry-eq : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) ->
                 ment r c U * (γ ↑ l) ≡ from-whole (int-entry U l hl r c)
  int-entry-eq = Weq

  -- ρˡ₁(U) entrywise is the parity of that integer.
  res1-entry : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) ->
               ment r c (residue1-matrix l U) ≡ parityℤ[i] (int-entry U l hl r c)
  res1-entry U l hl r c = res1-of U l r c (W U l hl r c) (Weq U l hl r c)

  -- Σₖ Xₖ꜀·(Xₖᵣ)† = t·2ˡ for the Gaussian integers of two columns.
  col-ints : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
             ipc (mcol c U) (mcol r U) ≡ from-whole T ->
             sum4 (int-entry U l hl ι0 c * ((int-entry U l hl ι0 r) †))
                  (int-entry U l hl ι1 c * ((int-entry U l hl ι1 r) †))
                  (int-entry U l hl ι2 c * ((int-entry U l hl ι2 r) †))
                  (int-entry U l hl ι3 c * ((int-entry U l hl ι3 r) †))
               ≡ T * (2ℤℂ ↑ l)
  col-ints U l hl r c T hip =
    scale-ipc (γ ↑ l) (2ℤℂ ↑ l) (gamma-norm l)
              (ment ι0 c U) (ment ι1 c U) (ment ι2 c U) (ment ι3 c U)
              (ment ι0 r U) (ment ι1 r U) (ment ι2 r U) (ment ι3 r U)
              (W U l hl ι0 c) (W U l hl ι1 c) (W U l hl ι2 c) (W U l hl ι3 c)
              (W U l hl ι0 r) (W U l hl ι1 r) (W U l hl ι2 r) (W U l hl ι3 r) T
              (Weq U l hl ι0 c) (Weq U l hl ι1 c) (Weq U l hl ι2 c) (Weq U l hl ι3 c)
              (Weq U l hl ι0 r) (Weq U l hl ι1 r) (Weq U l hl ι2 r) (Weq U l hl ι3 r)
              (subst2 (λ v w -> ipc v w ≡ from-whole T)
                      (vec4-η (mcol c U)) (vec4-η (mcol r U)) hip)

  -- The same for two rows.
  row-ints : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
             ipc (mrow c U) (mrow r U) ≡ from-whole T ->
             sum4 (int-entry U l hl c ι0 * ((int-entry U l hl r ι0) †))
                  (int-entry U l hl c ι1 * ((int-entry U l hl r ι1) †))
                  (int-entry U l hl c ι2 * ((int-entry U l hl r ι2) †))
                  (int-entry U l hl c ι3 * ((int-entry U l hl r ι3) †))
               ≡ T * (2ℤℂ ↑ l)
  row-ints U l hl r c T hip =
    scale-ipc (γ ↑ l) (2ℤℂ ↑ l) (gamma-norm l)
              (ment c ι0 U) (ment c ι1 U) (ment c ι2 U) (ment c ι3 U)
              (ment r ι0 U) (ment r ι1 U) (ment r ι2 U) (ment r ι3 U)
              (W U l hl c ι0) (W U l hl c ι1) (W U l hl c ι2) (W U l hl c ι3)
              (W U l hl r ι0) (W U l hl r ι1) (W U l hl r ι2) (W U l hl r ι3) T
              (Weq U l hl c ι0) (Weq U l hl c ι1) (Weq U l hl c ι2) (Weq U l hl c ι3)
              (Weq U l hl r ι0) (Weq U l hl r ι1) (Weq U l hl r ι2) (Weq U l hl r ι3)
              (subst2 (λ v w -> ipc v w ≡ from-whole T) (row-η4 U c) (row-η4 U r) hip)

-- ----------------------------------------------------------------------
-- * Two columns

-- Abstract: meet-col is applied at T = 1 (odd-count-col) and T = 0
-- (lemma-IV-3-col), and Kopt.PatternFacts applies those in turn; with a
-- transparent body each of those instantiations re-checks this chain.
abstract
  -- The number of positions where the cth and the rth column of ρˡ₁(U)
  -- are both odd, modulo 2, in terms of the inner product of the two
  -- columns of U.
  meet-col : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
             ipc (mcol c U) (mcol r U) ≡ from-whole T ->
             meet-count (mcol c (residue1-matrix l U)) (mcol r (residue1-matrix l U))
               ≡ P (T * (2ℤℂ ↑ l))
  meet-col U l hl r c T hip = begin
    meet-count (mcol c R) (mcol r R)
      ≡⟨ meet-count-η (mcol c R) (mcol r R) ⟩
    sum4 (ment ι0 c R * ment ι0 r R) (ment ι1 c R * ment ι1 r R)
         (ment ι2 c R * ment ι2 r R) (ment ι3 c R * ment ι3 r R)
      ≡⟨ sum4-cong (cong₂ mul2 (col-res ι0 c) (col-res ι0 r))
                   (cong₂ mul2 (col-res ι1 c) (col-res ι1 r))
                   (cong₂ mul2 (col-res ι2 c) (col-res ι2 r))
                   (cong₂ mul2 (col-res ι3 c) (col-res ι3 r)) ⟩
    sum4 (P (int-entry U l hl ι0 c) * P (int-entry U l hl ι0 r)) (P (int-entry U l hl ι1 c) * P (int-entry U l hl ι1 r))
         (P (int-entry U l hl ι2 c) * P (int-entry U l hl ι2 r)) (P (int-entry U l hl ι3 c) * P (int-entry U l hl ι3 r))
      ≡⟨ count-core (int-entry U l hl ι0 c) (int-entry U l hl ι1 c) (int-entry U l hl ι2 c) (int-entry U l hl ι3 c)
                    (int-entry U l hl ι0 r) (int-entry U l hl ι1 r) (int-entry U l hl ι2 r) (int-entry U l hl ι3 r)
                    (T * (2ℤℂ ↑ l)) (col-ints U l hl r c T hip) ⟩
    P (T * (2ℤℂ ↑ l)) ∎
    where
      open ≡-Reasoning
      R : Matrix 4 4 Z2
      R = residue1-matrix l U
      col-res : (k j : Ix) -> ment k j R ≡ P (int-entry U l hl k j)
      col-res k j = res1-entry U l hl k j

-- ----------------------------------------------------------------------
-- * Two rows

-- Abstract: see meet-col.
abstract
  meet-row : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) (r c : Ix) (T : ZComplex) ->
             ipc (mrow c U) (mrow r U) ≡ from-whole T ->
             meet-count (mrow c (residue1-matrix l U)) (mrow r (residue1-matrix l U))
               ≡ P (T * (2ℤℂ ↑ l))
  meet-row U l hl r c T hip = begin
    meet-count (mrow c R) (mrow r R)
      ≡⟨ meet-count-η (mrow c R) (mrow r R) ⟩
    sum4 (vsel ι0 (mrow c R) * vsel ι0 (mrow r R)) (vsel ι1 (mrow c R) * vsel ι1 (mrow r R))
         (vsel ι2 (mrow c R) * vsel ι2 (mrow r R)) (vsel ι3 (mrow c R) * vsel ι3 (mrow r R))
      ≡⟨ sum4-cong (cong₂ mul2 (row-res ι0 c) (row-res ι0 r))
                   (cong₂ mul2 (row-res ι1 c) (row-res ι1 r))
                   (cong₂ mul2 (row-res ι2 c) (row-res ι2 r))
                   (cong₂ mul2 (row-res ι3 c) (row-res ι3 r)) ⟩
    sum4 (P (int-entry U l hl c ι0) * P (int-entry U l hl r ι0)) (P (int-entry U l hl c ι1) * P (int-entry U l hl r ι1))
         (P (int-entry U l hl c ι2) * P (int-entry U l hl r ι2)) (P (int-entry U l hl c ι3) * P (int-entry U l hl r ι3))
      ≡⟨ count-core (int-entry U l hl c ι0) (int-entry U l hl c ι1) (int-entry U l hl c ι2) (int-entry U l hl c ι3)
                    (int-entry U l hl r ι0) (int-entry U l hl r ι1) (int-entry U l hl r ι2) (int-entry U l hl r ι3)
                    (T * (2ℤℂ ↑ l)) (row-ints U l hl r c T hip) ⟩
    P (T * (2ℤℂ ↑ l)) ∎
    where
      open ≡-Reasoning
      R : Matrix 4 4 Z2
      R = residue1-matrix l U
      row-res : (k j : Ix) -> vsel k (mrow j R) ≡ P (int-entry U l hl j k)
      row-res k j = trans (vsel-mrow R j k) (res1-entry U l hl j k)

-- ----------------------------------------------------------------------
-- * Lemma IV.2: the number of odd entries of a column or a row

private
  -- The two values of parity(t·2ˡ) that occur: t = 1, l > 0 gives
  -- Even, t = 1, l = 0 gives Odd, and t = 0 gives Even.
  one-2↑ : (l : ℕ) -> P ((1# {A = ZComplex}) * (2ℤℂ ↑ l))
                        ≡ P (2ℤℂ ↑ l)
  one-2↑ l = cong P (ZR.*-identityˡ (2ℤℂ ↑ l))

  zero-2↑ : (l : ℕ) -> P ((0# {A = ZComplex}) * (2ℤℂ ↑ l)) ≡ Even
  zero-2↑ l = cong P (ZR.zeroˡ (2ℤℂ ↑ l))

  one-D : (1# {A = DComplex}) ≡ from-whole (1# {A = ZComplex})
  one-D = sym from-whole-1

  zero-D : (0# {A = DComplex}) ≡ from-whole (0# {A = ZComplex})
  zero-D = sym from-whole-0

-- The number of odd entries of a column of ρˡ₁(U) has the parity of 2ˡ:
-- EVEN for l > 0 (the key fact of Lemma IV.2) and ODD for l = 0.
-- Abstract: applied at the concrete T = 1 and T = 0 below, and a
-- concrete constant in a 𝔻[i] chain is what the README warns about.
abstract
  odd-count-col : (U : Op) (l : ℕ) -> adjoint U * U ≡ 1# -> lde U Nat.≤ l -> (c : Ix) ->
                  odd-count (mcol c (residue1-matrix l U)) ≡ P (2ℤℂ ↑ l)
  odd-count-col U l hu hl c = begin
    odd-count (mcol c R)
      ≡⟨ odd-count-η (mcol c R) ⟩
    sum4 (ment ι0 c R) (ment ι1 c R) (ment ι2 c R) (ment ι3 c R)
      ≡⟨ sym (sum4-cong (z2-square (ment ι0 c R)) (z2-square (ment ι1 c R))
                        (z2-square (ment ι2 c R)) (z2-square (ment ι3 c R))) ⟩
    sum4 (ment ι0 c R * ment ι0 c R) (ment ι1 c R * ment ι1 c R)
         (ment ι2 c R * ment ι2 c R) (ment ι3 c R * ment ι3 c R)
      ≡⟨ sym (meet-count-η (mcol c R) (mcol c R)) ⟩
    meet-count (mcol c R) (mcol c R)
      ≡⟨ meet-col U l hl c c 1# (trans (u-col U hu c) one-D) ⟩
    P ((1# {A = ZComplex}) * (2ℤℂ ↑ l))
      ≡⟨ one-2↑ l ⟩
    P (2ℤℂ ↑ l) ∎
    where
      open ≡-Reasoning
      R : Matrix 4 4 Z2
      R = residue1-matrix l U

  odd-count-row : (U : Op) (l : ℕ) -> U * adjoint U ≡ 1# -> lde U Nat.≤ l -> (r : Ix) ->
                  odd-count (mrow r (residue1-matrix l U)) ≡ P (2ℤℂ ↑ l)
  odd-count-row U l hu hl r = begin
    odd-count (mrow r R)
      ≡⟨ odd-count-η (mrow r R) ⟩
    sum4 (vsel ι0 (mrow r R)) (vsel ι1 (mrow r R)) (vsel ι2 (mrow r R)) (vsel ι3 (mrow r R))
      ≡⟨ sym (sum4-cong (z2-square (vsel ι0 (mrow r R))) (z2-square (vsel ι1 (mrow r R)))
                        (z2-square (vsel ι2 (mrow r R))) (z2-square (vsel ι3 (mrow r R)))) ⟩
    sum4 (vsel ι0 (mrow r R) * vsel ι0 (mrow r R)) (vsel ι1 (mrow r R) * vsel ι1 (mrow r R))
         (vsel ι2 (mrow r R) * vsel ι2 (mrow r R)) (vsel ι3 (mrow r R) * vsel ι3 (mrow r R))
      ≡⟨ sym (meet-count-η (mrow r R) (mrow r R)) ⟩
    meet-count (mrow r R) (mrow r R)
      ≡⟨ meet-row U l hl r r 1# (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow r U))) (u-row U hu r)) one-D) ⟩
    P ((1# {A = ZComplex}) * (2ℤℂ ↑ l))
      ≡⟨ one-2↑ l ⟩
    P (2ℤℂ ↑ l) ∎
    where
      open ≡-Reasoning
      R : Matrix 4 4 Z2
      R = residue1-matrix l U

-- ----------------------------------------------------------------------
-- * The four statements of Lemmas IV.2 and IV.3
--
-- For a unitary U and a denominator exponent l = k+1 > 0 of U:
-- every column and every row of ρˡ₁(U) has an even number of odd
-- entries (Lemma IV.2), and two distinct columns, or two distinct
-- rows, are both odd at an even number of positions (Lemma IV.3).

lemma-IV-2-col : (U : Op) (k : ℕ) -> adjoint U * U ≡ 1# -> lde U Nat.≤ suc k -> (c : Ix) ->
                 odd-count (mcol c (residue1-matrix (suc k) U)) ≡ Even
lemma-IV-2-col U k hu hl c = trans (odd-count-col U (suc k) hu hl c) (parity-2↑ k)

lemma-IV-2-row : (U : Op) (k : ℕ) -> U * adjoint U ≡ 1# -> lde U Nat.≤ suc k -> (r : Ix) ->
                 odd-count (mrow r (residue1-matrix (suc k) U)) ≡ Even
lemma-IV-2-row U k hu hl r = trans (odd-count-row U (suc k) hu hl r) (parity-2↑ k)

lemma-IV-3-col : (U : Op) (l : ℕ) -> adjoint U * U ≡ 1# -> lde U Nat.≤ l -> (r c : Ix) ->
                 ix/= r c ≡ true ->
                 meet-count (mcol c (residue1-matrix l U)) (mcol r (residue1-matrix l U)) ≡ Even
lemma-IV-3-col U l hu hl r c d =
  trans (meet-col U l hl r c 0# (trans (o-col U hu r c d) zero-D)) (zero-2↑ l)

lemma-IV-3-row : (U : Op) (l : ℕ) -> U * adjoint U ≡ 1# -> lde U Nat.≤ l -> (r c : Ix) ->
                 ix/= r c ≡ true ->
                 meet-count (mrow c (residue1-matrix l U)) (mrow r (residue1-matrix l U)) ≡ Even
lemma-IV-3-row U l hu hl r c d =
  trans (meet-row U l hl r c 0#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow c U)))
                        (o-row U hu c r (ix/=-sym r c d))) zero-D))
        (zero-2↑ l)

-- ----------------------------------------------------------------------
-- * The lde-0 case (Section III C)
--
-- At lde 0 the counts are odd instead: every column and every row of
-- ρ⁰₁(U) has an odd number of odd entries. Together with the two
-- statements of Lemma IV.3 this says that ρ⁰₁(U) is a permutation
-- matrix over ℤ₂ once one knows that a column cannot have three odd
-- entries, which needs the integrality of the norms (see
-- Kopt.PatternFacts).

odd-count-col-0 : (U : Op) -> adjoint U * U ≡ 1# -> lde U Nat.≤ 0 -> (c : Ix) ->
                  odd-count (mcol c (residue1-matrix 0 U)) ≡ Odd
odd-count-col-0 U hu hl c = trans (odd-count-col U 0 hu hl c) parity-2↑0

odd-count-row-0 : (U : Op) -> U * adjoint U ≡ 1# -> lde U Nat.≤ 0 -> (r : Ix) ->
                  odd-count (mrow r (residue1-matrix 0 U)) ≡ Odd
odd-count-row-0 U hu hl r = trans (odd-count-row U 0 hu hl r) parity-2↑0

col-norm-ints : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> adjoint U * U ≡ 1# -> (c : Ix) ->
                sum4 (int-entry U l hl ι0 c * ((int-entry U l hl ι0 c) †))
                     (int-entry U l hl ι1 c * ((int-entry U l hl ι1 c) †))
                     (int-entry U l hl ι2 c * ((int-entry U l hl ι2 c) †))
                     (int-entry U l hl ι3 c * ((int-entry U l hl ι3 c) †))
                  ≡ 2ℤℂ ↑ l
col-norm-ints U l hl hu c =
  trans (col-ints U l hl c c 1# (trans (u-col U hu c) one-D))
        (ZR.*-identityˡ (2ℤℂ ↑ l))

row-norm-ints : (U : Op) (l : ℕ) (hl : lde U Nat.≤ l) -> U * adjoint U ≡ 1# -> (r : Ix) ->
                sum4 (int-entry U l hl r ι0 * ((int-entry U l hl r ι0) †))
                     (int-entry U l hl r ι1 * ((int-entry U l hl r ι1) †))
                     (int-entry U l hl r ι2 * ((int-entry U l hl r ι2) †))
                     (int-entry U l hl r ι3 * ((int-entry U l hl r ι3) †))
                  ≡ 2ℤℂ ↑ l
row-norm-ints U l hl hu r =
  trans (row-ints U l hl r r 1#
          (trans (trans (sym (ipr-ipc-D (mrow r U) (mrow r U))) (u-row U hu r)) one-D))
        (ZR.*-identityˡ (2ℤℂ ↑ l))

-- ----------------------------------------------------------------------
-- * Lemma II.7 for a matrix: at lde l > 0 some entry of ρˡ₁ is odd

private
  max-either : (a b : ℕ) -> (max a b ≡ a) ⊎ (max a b ≡ b)
  max-either a b with a Nat.≤ᵇ b
  ... | true = inj₂ refl
  ... | false = inj₁ refl

  -- The lde of a 4-vector is the lde of one of its four entries.
  lde4-attained : {T : Set} {{_ : LamDenomExp T}} (x y z w : T) ->
                  (lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ [])) ≡ lde x)
                    ⊎ ((lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ [])) ≡ lde y)
                    ⊎ ((lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ [])) ≡ lde z)
                    ⊎ (lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ [])) ≡ lde w)))
  lde4-attained x y z w with max-either (lde x) (max (lde y) (max (lde z) (max (lde w) 0)))
  ... | inj₁ e = inj₁ e
  ... | inj₂ e with max-either (lde y) (max (lde z) (max (lde w) 0))
  ...   | inj₁ e2 = inj₂ (inj₁ (trans e e2))
  ...   | inj₂ e2 with max-either (lde z) (max (lde w) 0)
  ...     | inj₁ e3 = inj₂ (inj₂ (inj₁ (trans e (trans e2 e3))))
  ...     | inj₂ e3 with max-either (lde w) 0
  ...       | inj₁ e4 = inj₂ (inj₂ (inj₂ (trans e (trans e2 (trans e3 e4)))))
  ...       | inj₂ e4 = inj₂ (inj₂ (inj₂ (trans e (trans e2 (trans e3 (trans e4 (sym zero-w)))))))
              where
                zero-w : lde w ≡ 0
                zero-w = NatP.n≤0⇒n≡0 (subst (λ n -> lde w Nat.≤ n) e4 (max-≤ˡ (lde w) 0))

  vec4-attained : {T : Set} {{_ : LamDenomExp T}} (v : Vector 4 T) ->
                  Σ[ r ∈ Ix ] lde (vsel r v) ≡ lde v
  vec4-attained (x ∷ y ∷ z ∷ w ∷ []) = pick (lde4-attained x y z w)
    where
      pick : _ -> Σ[ r ∈ Ix ] lde (vsel r (x ∷ y ∷ z ∷ w ∷ [])) ≡ lde (Vector 4 _ ∋ (x ∷ y ∷ z ∷ w ∷ []))
      pick (inj₁ h) = ι0 , sym h
      pick (inj₂ (inj₁ h)) = ι1 , sym h
      pick (inj₂ (inj₂ (inj₁ h))) = ι2 , sym h
      pick (inj₂ (inj₂ (inj₂ h))) = ι3 , sym h

  mat4-attained : (U : Op) -> Σ[ c ∈ Ix ] lde (mcol c U) ≡ lde U
  mat4-attained (Matrix' cs) = vec4-attained cs

-- Some entry of U has the same lde as U.
lde-attained : (U : Op) -> Σ[ r ∈ Ix ] Σ[ c ∈ Ix ] lde (ment r c U) ≡ lde U
lde-attained U with mat4-attained U
... | (c , ec) with vec4-attained (mcol c U)
...   | (r , er) = r , c , trans er ec

-- Lemma II.7 for a matrix: at lde l = k+1 some entry of ρˡ₁(U) is odd.
res1-has-odd : (U : Op) (k : ℕ) (hl : lde U ≡ suc k) ->
               Σ[ r ∈ Ix ] Σ[ c ∈ Ix ] ment r c (residue1-matrix (suc k) U) ≡ Odd
res1-has-odd U k hl = go (lde-attained U)
  where
    le : lde U Nat.≤ suc k
    le = NatP.≤-reflexive hl
    go : Σ[ r ∈ Ix ] Σ[ c ∈ Ix ] lde (ment r c U) ≡ lde U ->
         Σ[ r ∈ Ix ] Σ[ c ∈ Ix ] ment r c (residue1-matrix (suc k) U) ≡ Odd
    go (r , c , e) = r , c ,
      trans (res1-entry U (suc k) le r c)
            (lemma-II-7 (ment r c U) k (int-entry U (suc k) le r c)
                        (trans e hl) (int-entry-eq U (suc k) le r c))
