-- Multiplying on the left by a permutation matrix permutes the rows.
--
-- Kopt.Descent's lcomb-unit covers the other side: there the unit
-- vectors are the right factor's columns, and each of them selects one
-- column of the left factor, which is a computation that goes through
-- with the permutation still a variable. Here the unit vectors are the
-- LEFT factor's columns, so each scatters one entry of the right
-- factor's column to the row that the permutation names, and the
-- result's entry in a given row is the entry of the right factor in
-- whatever row the permutation sends there -- the inverse permutation.
--
-- Finding that row is a four-way case analysis on `selp (inv4p t) p`,
-- and in each case three of the four terms vanish because a permutation
-- is injective. Four cases, not 4⁴: the analysis is on the value of the
-- inverse at one position, and the rest follows from distinctness.

{-# OPTIONS --without-K --safe #-}

module Kopt.PermScatter where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; if_then_else_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Descent
  using (Op ; Pos ; p0 ; p1 ; p2 ; p3 ; Pos4 ; Phase ; ph0 ; phase-val ; Phase4
        ; selp ; selph ; inv4p ; inv4p-right ; selp-comp ; selp-id ; id4p ; comp4p
        ; distinct4p ; _==p_ ; ==p-sound ; unit-vec ; gp-mat-of ; mcol4
        ; smul ; vadd ; lcomb ; vec4-≡ ; mat4-≡ ; ∧-true ; module Mat4)
open import Kopt.PermIndex using (vselp)



-- All phases trivial: a permutation matrix is the generalized
-- permutation with no phases.
ph0s : Phase4
ph0s = ph0 , ph0 , ph0 , ph0

==p-refl : (p : Pos) -> (p ==p p) ≡ true
==p-refl p0 = refl
==p-refl p1 = refl
==p-refl p2 = refl
==p-refl p3 = refl

-- ----------------------------------------------------------------------
-- * A permutation is injective

-- The six components of distinct4p.
private
  d6 : (t : Pos4) -> distinct4p t ≡ true ->
       (not (selp t p0 ==p selp t p1) ≡ true)
         × ((not (selp t p0 ==p selp t p2) ≡ true)
         × ((not (selp t p0 ==p selp t p3) ≡ true)
         × ((not (selp t p1 ==p selp t p2) ≡ true)
         × ((not (selp t p1 ==p selp t p3) ≡ true)
         × (not (selp t p2 ==p selp t p3) ≡ true)))))
  -- The six booleans are matched directly. Peeling the conjunction with
  -- ∧-true instead leaves its two implicit arguments to unification,
  -- which cannot tell how to split a six-fold conjunction and reports
  -- unsolved constraints.
  d6 (a , b , c , d) h = go (a ==p b) (a ==p c) (a ==p d) (b ==p c) (b ==p d) (c ==p d) h
    where
      go : (x₁ x₂ x₃ x₄ x₅ x₆ : Bool) ->
           (not x₁ ∧ not x₂ ∧ not x₃ ∧ not x₄ ∧ not x₅ ∧ not x₆) ≡ true ->
           (not x₁ ≡ true)
             × ((not x₂ ≡ true) × ((not x₃ ≡ true)
             × ((not x₄ ≡ true) × ((not x₅ ≡ true) × (not x₆ ≡ true)))))
      go false false false false false false _ = refl , refl , refl , refl , refl , refl
      go true _ _ _ _ _ ()
      go false true _ _ _ _ ()
      go false false true _ _ _ ()
      go false false false true _ _ ()
      go false false false false true _ ()
      go false false false false false true ()

  not-true : {b : Bool} -> not b ≡ true -> b ≡ false
  not-true {false} _ = refl

  sym-false : (q r : Pos) -> (q ==p r) ≡ false -> (r ==p q) ≡ false
  sym-false p0 p0 ()
  sym-false p0 p1 _ = refl
  sym-false p0 p2 _ = refl
  sym-false p0 p3 _ = refl
  sym-false p1 p0 _ = refl
  sym-false p1 p1 ()
  sym-false p1 p2 _ = refl
  sym-false p1 p3 _ = refl
  sym-false p2 p0 _ = refl
  sym-false p2 p1 _ = refl
  sym-false p2 p2 ()
  sym-false p2 p3 _ = refl
  sym-false p3 p0 _ = refl
  sym-false p3 p1 _ = refl
  sym-false p3 p2 _ = refl
  sym-false p3 p3 ()

-- Distinct positions have distinct images.
distinct-pair : (t : Pos4) -> distinct4p t ≡ true -> (k j : Pos) -> (k ==p j) ≡ false ->
                (selp t k ==p selp t j) ≡ false
distinct-pair t h p0 p0 ()
distinct-pair t h p0 p1 _ = not-true (proj₁ (d6 t h))
distinct-pair t h p0 p2 _ = not-true (proj₁ (proj₂ (d6 t h)))
distinct-pair t h p0 p3 _ = not-true (proj₁ (proj₂ (proj₂ (d6 t h))))
distinct-pair t h p1 p0 _ = sym-false _ _ (not-true (proj₁ (d6 t h)))
distinct-pair t h p1 p1 ()
distinct-pair t h p1 p2 _ = not-true (proj₁ (proj₂ (proj₂ (proj₂ (d6 t h)))))
distinct-pair t h p1 p3 _ = not-true (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (d6 t h))))))
distinct-pair t h p2 p0 _ = sym-false _ _ (not-true (proj₁ (proj₂ (d6 t h))))
distinct-pair t h p2 p1 _ = sym-false _ _ (not-true (proj₁ (proj₂ (proj₂ (proj₂ (d6 t h))))))
distinct-pair t h p2 p2 ()
distinct-pair t h p2 p3 _ = not-true (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (d6 t h))))))
distinct-pair t h p3 p0 _ = sym-false _ _ (not-true (proj₁ (proj₂ (proj₂ (d6 t h)))))
distinct-pair t h p3 p1 _ =
  sym-false _ _ (not-true (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (d6 t h)))))))
distinct-pair t h p3 p2 _ =
  sym-false _ _ (not-true (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (d6 t h)))))))
distinct-pair t h p3 p3 ()

-- t sends the inverse's value at p back to p.
inv-sel : (t : Pos4) -> distinct4p t ≡ true -> (p : Pos) -> selp t (selp (inv4p t) p) ≡ p
inv-sel t h p = trans (sym (selp-comp t (inv4p t) p))
                      (trans (cong (λ u -> selp u p) (inv4p-right t h)) (selp-id p))

-- Reordering a 4-vector along a Pos4, the Pos-indexed form of
-- Kopt.Patterns.select4 (Kopt.PermIndex.select4-pos relates the two).
select4p : {A : Set} -> Pos4 -> Vector 4 A -> Vector 4 A
select4p s v = vselp (selp s p0) v ∷ vselp (selp s p1) v
             ∷ vselp (selp s p2) v ∷ vselp (selp s p3) v ∷ []

-- Its entries, which is how it meets the scatter.
vselp-select4p : {A : Set} (s : Pos4) (v : Vector 4 A) (p : Pos) ->
                 vselp p (select4p s v) ≡ vselp (selp s p) v
vselp-select4p s v p0 = refl
vselp-select4p s v p1 = refl
vselp-select4p s v p2 = refl
vselp-select4p s v p3 = refl

-- Extensionality for 4-vectors, indexed by Pos. The left-hand side below
-- is a stuck lcomb, so it cannot be compared entry by entry with vec4-≡.
vec4-extp : {A : Set} (v w : Vector 4 A) -> ((p : Pos) -> vselp p v ≡ vselp p w) -> v ≡ w
vec4-extp (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) hp =
  vec4-≡ (hp p0) (hp p1) (hp p2) (hp p3)

-- ----------------------------------------------------------------------
-- * Performance
--
-- The scatter below is proved for an ABSTRACT commutative ring and
-- instantiated at the dyadic complex numbers afterwards. The sum whose
-- terms it collapses has factors `if selp t k ==p p then 1# else 0#`,
-- which are stuck, since the permutation is a variable; over the dyadic
-- complex numbers each product of such a stuck conditional with a matrix
-- entry expands into the dyadic arithmetic, a smart constructor with a
-- stuck parity test inside an eta record. That cost this module 241 s.
-- Everything above is about Pos alone and mentions no ring at all.


module Scatter {A : Set} {{RA : Ring A}}
               (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  private
    module R = IsCommutativeRing isCR
  open Mat4 isCR using (pick0 ; pick1 ; pick2 ; pick3 ; mmul-≡)

  -- The unit vector with 1# at position q.
  uvec : Pos -> Vector 4 A
  uvec p0 = 1# ∷ 0# ∷ 0# ∷ 0# ∷ []
  uvec p1 = 0# ∷ 1# ∷ 0# ∷ 0# ∷ []
  uvec p2 = 0# ∷ 0# ∷ 1# ∷ 0# ∷ []
  uvec p3 = 0# ∷ 0# ∷ 0# ∷ 1# ∷ []

  -- The matrix of a permutation.
  pmat : Pos4 -> Matrix 4 4 A
  pmat t = Matrix' (uvec (selp t p0) ∷ uvec (selp t p1) ∷ uvec (selp t p2) ∷ uvec (selp t p3) ∷ [])

  private
    vselp-vadd : (p : Pos) (v w : Vector 4 A) -> vselp p (vadd v w) ≡ vselp p v + vselp p w
    vselp-vadd p0 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-vadd p1 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-vadd p2 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-vadd p3 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl

    vselp-smul : (p : Pos) (a : A) (v : Vector 4 A) -> vselp p (smul a v) ≡ a * vselp p v
    vselp-smul p0 a (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-smul p1 a (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-smul p2 a (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl
    vselp-smul p3 a (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) = refl

    vselp-zero : (p : Pos) -> vselp p (vector-repeat (0# {A = A})) ≡ 0#
    vselp-zero p0 = refl
    vselp-zero p1 = refl
    vselp-zero p2 = refl
    vselp-zero p3 = refl

    vselp-lcomb : (p : Pos) (u₀ u₁ u₂ u₃ : Vector 4 A) (w₀ w₁ w₂ w₃ : A) ->
                  vselp p (lcomb (u₀ ∷ u₁ ∷ u₂ ∷ u₃ ∷ []) (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []))
                    ≡ (w₀ * vselp p u₀)
                      + ((w₁ * vselp p u₁) + ((w₂ * vselp p u₂) + ((w₃ * vselp p u₃) + 0#)))
    vselp-lcomb p u₀ u₁ u₂ u₃ w₀ w₁ w₂ w₃ =
      trans (vselp-vadd p (smul w₀ u₀) _)
            (cong₂ (λ s t -> s + t) (vselp-smul p w₀ u₀)
              (trans (vselp-vadd p (smul w₁ u₁) _)
                (cong₂ (λ s t -> s + t) (vselp-smul p w₁ u₁)
                  (trans (vselp-vadd p (smul w₂ u₂) _)
                    (cong₂ (λ s t -> s + t) (vselp-smul p w₂ u₂)
                      (trans (vselp-vadd p (smul w₃ u₃) _)
                        (cong₂ (λ s t -> s + t) (vselp-smul p w₃ u₃) (vselp-zero p))))))))

    uvec-entry : (q p : Pos) -> vselp p (uvec q) ≡ (if q ==p p then 1# else 0#)
    uvec-entry p0 p0 = refl
    uvec-entry p0 p1 = refl
    uvec-entry p0 p2 = refl
    uvec-entry p0 p3 = refl
    uvec-entry p1 p0 = refl
    uvec-entry p1 p1 = refl
    uvec-entry p1 p2 = refl
    uvec-entry p1 p3 = refl
    uvec-entry p2 p0 = refl
    uvec-entry p2 p1 = refl
    uvec-entry p2 p2 = refl
    uvec-entry p2 p3 = refl
    uvec-entry p3 p0 = refl
    uvec-entry p3 p1 = refl
    uvec-entry p3 p2 = refl
    uvec-entry p3 p3 = refl

  -- The sum of wk times the unit vector at t(k) has its pth entry at
  -- w at t-inverse of p.
  scatter : (t : Pos4) -> distinct4p t ≡ true -> (p : Pos) (w₀ w₁ w₂ w₃ : A) ->
            vselp p (lcomb (uvec (selp t p0) ∷ uvec (selp t p1)
                          ∷ uvec (selp t p2) ∷ uvec (selp t p3) ∷ [])
                          (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []))
              ≡ vselp (selp (inv4p t) p) (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ [])
  scatter t h p w₀ w₁ w₂ w₃ = go (selp (inv4p t) p) refl
    where
      e : Pos -> A
      e k = if selp t k ==p p then 1# else 0#

      cong-sum4 : {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : A} ->
                  a₀ ≡ b₀ -> a₁ ≡ b₁ -> a₂ ≡ b₂ -> a₃ ≡ b₃ ->
                  (w₀ * a₀) + ((w₁ * a₁) + ((w₂ * a₂) + ((w₃ * a₃) + 0#)))
                    ≡ (w₀ * b₀) + ((w₁ * b₁) + ((w₂ * b₂) + ((w₃ * b₃) + 0#)))
      cong-sum4 refl refl refl refl = refl

      sum≡ : vselp p (lcomb (uvec (selp t p0) ∷ uvec (selp t p1)
                           ∷ uvec (selp t p2) ∷ uvec (selp t p3) ∷ [])
                           (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []))
               ≡ (w₀ * e p0) + ((w₁ * e p1) + ((w₂ * e p2) + ((w₃ * e p3) + 0#)))
      sum≡ = trans (vselp-lcomb p (uvec (selp t p0)) (uvec (selp t p1))
                                  (uvec (selp t p2)) (uvec (selp t p3)) w₀ w₁ w₂ w₃)
                   (cong-sum4 (uvec-entry (selp t p0) p) (uvec-entry (selp t p1) p)
                              (uvec-entry (selp t p2) p) (uvec-entry (selp t p3) p))

      at : (j : Pos) -> selp (inv4p t) p ≡ j -> selp t j ≡ p
      at j ee = subst (λ u -> selp t u ≡ p) ee (inv-sel t h p)

      kept : (j : Pos) -> selp t j ≡ p -> e j ≡ 1#
      kept j eq = cong (λ β -> if β then 1# else 0#)
                       (trans (cong (λ q -> q ==p p) eq) (==p-refl p))

      drop : (j k : Pos) -> selp t j ≡ p -> (k ==p j) ≡ false -> e k ≡ 0#
      drop j k eq ne = cong (λ β -> if β then 1# else 0#)
                            (trans (cong (λ q -> selp t k ==p q) (sym eq))
                                   (distinct-pair t h k j ne))

      mul0 : (a b : A) -> b ≡ 0# -> a * b ≡ 0#
      mul0 a b hb = trans (cong (λ z -> a * z) hb) (R.zeroʳ a)

      mul1 : (a b : A) -> b ≡ 1# -> a * b ≡ a
      mul1 a b hb = trans (cong (λ z -> a * z) hb) (R.*-identityʳ a)

      go : (j : Pos) -> selp (inv4p t) p ≡ j ->
           vselp p (lcomb (uvec (selp t p0) ∷ uvec (selp t p1)
                         ∷ uvec (selp t p2) ∷ uvec (selp t p3) ∷ [])
                         (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []))
             ≡ vselp j (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ [])
      go p0 ee = trans sum≡
                   (trans (pick0 (w₀ * e p0) (w₁ * e p1) (w₂ * e p2) (w₃ * e p3)
                                 (mul0 w₁ _ (drop p0 p1 (at p0 ee) refl))
                                 (mul0 w₂ _ (drop p0 p2 (at p0 ee) refl))
                                 (mul0 w₃ _ (drop p0 p3 (at p0 ee) refl)))
                          (mul1 w₀ _ (kept p0 (at p0 ee))))
      go p1 ee = trans sum≡
                   (trans (pick1 (w₀ * e p0) (w₁ * e p1) (w₂ * e p2) (w₃ * e p3)
                                 (mul0 w₀ _ (drop p1 p0 (at p1 ee) refl))
                                 (mul0 w₂ _ (drop p1 p2 (at p1 ee) refl))
                                 (mul0 w₃ _ (drop p1 p3 (at p1 ee) refl)))
                          (mul1 w₁ _ (kept p1 (at p1 ee))))
      go p2 ee = trans sum≡
                   (trans (pick2 (w₀ * e p0) (w₁ * e p1) (w₂ * e p2) (w₃ * e p3)
                                 (mul0 w₀ _ (drop p2 p0 (at p2 ee) refl))
                                 (mul0 w₁ _ (drop p2 p1 (at p2 ee) refl))
                                 (mul0 w₃ _ (drop p2 p3 (at p2 ee) refl)))
                          (mul1 w₂ _ (kept p2 (at p2 ee))))
      go p3 ee = trans sum≡
                   (trans (pick3 (w₀ * e p0) (w₁ * e p1) (w₂ * e p2) (w₃ * e p3)
                                 (mul0 w₀ _ (drop p3 p0 (at p3 ee) refl))
                                 (mul0 w₁ _ (drop p3 p1 (at p3 ee) refl))
                                 (mul0 w₂ _ (drop p3 p2 (at p3 ee) refl)))
                          (mul1 w₃ _ (kept p3 (at p3 ee))))

  -- Row r of the product of the permutation matrix with M is row
  -- t-inverse of r of M.
  pmat-mul : (t : Pos4) -> distinct4p t ≡ true -> (M : Matrix 4 4 A) ->
             pmat t * M
               ≡ Matrix' ( select4p (inv4p t) (vselp p0 (unMatrix M))
                         ∷ select4p (inv4p t) (vselp p1 (unMatrix M))
                         ∷ select4p (inv4p t) (vselp p2 (unMatrix M))
                         ∷ select4p (inv4p t) (vselp p3 (unMatrix M)) ∷ [])
  pmat-mul t h (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) =
    trans (mmul-≡ (pmat t) (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])))
          (mat4-≡ (col a₀) (col a₁) (col a₂) (col a₃))
    where
      col : (v : Vector 4 A) ->
            lcomb (uvec (selp t p0) ∷ uvec (selp t p1)
                 ∷ uvec (selp t p2) ∷ uvec (selp t p3) ∷ []) v
              ≡ select4p (inv4p t) v
      col (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []) =
        vec4-extp _ _ (λ p -> trans (scatter t h p w₀ w₁ w₂ w₃)
                                    (sym (vselp-select4p (inv4p t) (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []) p)))

-- ----------------------------------------------------------------------
-- * At the dyadic complex numbers

private
  module SD = Scatter isCommutativeRing-DComplex

mcol4-vselp : (q : Pos) (A : Op) -> mcol4 q A ≡ vselp q (unMatrix A)
mcol4-vselp p0 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p1 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p2 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p3 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl

-- The generic unit vector is the phase-free one of Kopt.Descent.
uvec-unit : (q : Pos) -> SD.uvec q ≡ unit-vec q ph0
uvec-unit p0 = refl
uvec-unit p1 = refl
uvec-unit p2 = refl
uvec-unit p3 = refl

pmat-gp : (t : Pos4) -> SD.pmat t ≡ gp-mat-of t ph0s
pmat-gp t = mat4-≡ (uvec-unit (selp t p0)) (uvec-unit (selp t p1))
                   (uvec-unit (selp t p2)) (uvec-unit (selp t p3))

-- Row r of the product of a permutation matrix with A is row t-inverse
-- of r of A.
perm-mul-left : (t : Pos4) -> distinct4p t ≡ true -> (A : Op) ->
                gp-mat-of t ph0s * A
                  ≡ Matrix' ( select4p (inv4p t) (mcol4 p0 A)
                            ∷ select4p (inv4p t) (mcol4 p1 A)
                            ∷ select4p (inv4p t) (mcol4 p2 A)
                            ∷ select4p (inv4p t) (mcol4 p3 A) ∷ [])
perm-mul-left t h A =
  trans (cong (λ m -> m * A) (sym (pmat-gp t)))
        (trans (SD.pmat-mul t h A) (mat4-≡ (cl p0) (cl p1) (cl p2) (cl p3)))
  where
    cl : (q : Pos) -> select4p (inv4p t) (vselp q (unMatrix A))
                        ≡ select4p (inv4p t) (mcol4 q A)
    cl q = cong (select4p (inv4p t)) (sym (mcol4-vselp q A))

