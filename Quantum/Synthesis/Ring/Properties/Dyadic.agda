-- The dyadic fractions 𝔻 = ℤ[½] form a commutative ring.
--
-- Proof: the map toℚ : Dyadic → ℚ (ToRationalDyadic instance) is an
-- injective ring homomorphism (injective, since the representation
-- of dyadic fractions is canonical), so the ring laws transfer from
-- ℚ. To compute with the smart constructor "dyadic a n" = a/2ⁿ, we
-- go through the unnormalised rationals ℚᵘ, where a/2ⁿ is simply the
-- pair (a, 2ⁿ).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Dyadic where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing ; RawRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.Morphism.Structures using (IsRingMonomorphism)
import Algebra.Morphism.RingMonomorphism as RingMonomorphisms
open import Data.Bool.Base using (Bool ; true ; false ; T ; not)
open import Data.Empty using (⊥ ; ⊥-elim ; ⊥-elim-irr)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕDM
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
import Data.Integer.DivMod as IDM
import Data.Integer.Solver as ℤSolver
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Base as ℚᵘ
open import Data.Rational.Unnormalised.Base using (ℚᵘ ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Instances hiding (_≟_ ; _/_ ; _%_ ; _≤_ ; _<_)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; dyadic ; SemiRingDyadic ; RingDyadic ; ToRationalDyadic ;
         evenℤ ; evenℕ ; shiftR ; shiftL ; 2^ ; 2^ℤ ; pow2 ; Canonical ; integer-of-dyadic)

open ℤSolver.+-*-Solver using (solve ; _:=_ ; _:+_ ; _:*_ ; con)

-- ----------------------------------------------------------------------
-- * Auxiliary lemmas

-- 2ⁿ is non-zero.
nz : ∀ n -> ℕ.NonZero (2^ n)
nz n = ℕP.m^n≢0 2 n

private

  -- Recovering a relevant proof of T b.
  recompute-T : ∀ b -> .(T b) -> T b
  recompute-T true _ = tt
  recompute-T false p = ⊥-elim-irr p

  -- ℚᵘ fractions with a positive denominator d.
  /ᵘ-≃ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         a ℤ.* + e ≡ b ℤ.* + d -> (a ℚᵘ./ d) ℚᵘ.≃ (b ℚᵘ./ e)
  /ᵘ-≃ a b (suc d) (suc e) eq = *≡* eq

  /ᵘ-≃⁻¹ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
           (a ℚᵘ./ d) ℚᵘ.≃ (b ℚᵘ./ e) -> a ℤ.* + e ≡ b ℤ.* + d
  /ᵘ-≃⁻¹ a b (suc d) (suc e) (*≡* eq) = eq

  /ᵘ-+ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         (a ℚᵘ./ d) ℚᵘ.+ (b ℚᵘ./ e) ≡ ((a ℤ.* + e ℤ.+ b ℤ.* + d) ℚᵘ./ (d ℕ.* e)) {{ℕP.m*n≢0 d e}}
  /ᵘ-+ a b (suc d) (suc e) = refl

  /ᵘ-* : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         (a ℚᵘ./ d) ℚᵘ.* (b ℚᵘ./ e) ≡ ((a ℤ.* b) ℚᵘ./ (d ℕ.* e)) {{ℕP.m*n≢0 d e}}
  /ᵘ-* a b (suc d) (suc e) = refl

  /ᵘ-neg : ∀ a d .{{_ : ℕ.NonZero d}} -> ℚᵘ.- (a ℚᵘ./ d) ≡ (ℤ.- a) ℚᵘ./ d
  /ᵘ-neg a (suc d) = refl

  fromℚᵘ-/ : ∀ a d .{{_ : ℕ.NonZero d}} -> ℚ.fromℚᵘ (a ℚᵘ./ d) ≡ a ℚ./ d
  fromℚᵘ-/ a (suc d) = refl

  -- fromℚᵘ is a ring homomorphism.
  fromℚᵘ-+ : ∀ p q -> ℚ.fromℚᵘ (p ℚᵘ.+ q) ≡ ℚ.fromℚᵘ p ℚ.+ ℚ.fromℚᵘ q
  fromℚᵘ-+ p q = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (p ℚᵘ.+ q))
    (ℚᵘP.≃-trans (ℚᵘP.+-cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)) (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ q)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo-+ (ℚ.fromℚᵘ p) (ℚ.fromℚᵘ q)))))

  fromℚᵘ-* : ∀ p q -> ℚ.fromℚᵘ (p ℚᵘ.* q) ≡ ℚ.fromℚᵘ p ℚ.* ℚ.fromℚᵘ q
  fromℚᵘ-* p q = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (p ℚᵘ.* q))
    (ℚᵘP.≃-trans (ℚᵘP.*-cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)) (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ q)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo-* (ℚ.fromℚᵘ p) (ℚ.fromℚᵘ q)))))

  fromℚᵘ-neg : ∀ p -> ℚ.fromℚᵘ (ℚᵘ.- p) ≡ ℚ.- ℚ.fromℚᵘ p
  fromℚᵘ-neg p = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (ℚᵘ.- p))
    (ℚᵘP.≃-trans (ℚᵘP.-‿cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo‿- (ℚ.fromℚᵘ p)))))

  -- If a is even, then a = 2 * (a/2).
  even⇒%2≡0 : ∀ a -> evenℤ a ≡ true -> a ℤ.%ℕ 2 ≡ 0
  even⇒%2≡0 (+ n) eq = ℕP.≡ᵇ⇒≡ (n ℕ.% 2) 0 (subst T (sym eq) tt)
  even⇒%2≡0 -[1+ n ] eq with suc n ℕ.% 2 | ℕP.≡ᵇ⇒≡ (suc n ℕ.% 2) 0 (subst T (sym eq) tt)
  ... | zero | _ = refl
  ... | suc _ | ()

  shiftR-even : ∀ a -> evenℤ a ≡ true -> shiftR a 1 ℤ.* + 2 ≡ a
  shiftR-even a eq = sym (begin
    a                                   ≡⟨ IDM.a≡a%n+[a/n]*n a (+ 2) ⟩
    + (a ℤ.%ℕ 2) ℤ.+ shiftR a 1 ℤ.* + 2  ≡⟨ cong (λ r -> + r ℤ.+ shiftR a 1 ℤ.* + 2) (even⇒%2≡0 a eq) ⟩
    + 0 ℤ.+ shiftR a 1 ℤ.* + 2           ≡⟨ ℤP.+-identityˡ _ ⟩
    shiftR a 1 ℤ.* + 2                   ∎)
    where open ≡-Reasoning

  -- Even numbers.
  even-* : ∀ a k -> evenℤ (a ℤ.* + (2 ℕ.* k)) ≡ true
  even-* a k = begin
    evenℕ ℤ.∣ a ℤ.* + (2 ℕ.* k) ∣       ≡⟨ cong evenℕ (ℤP.abs-* a (+ (2 ℕ.* k))) ⟩
    evenℕ (ℤ.∣ a ∣ ℕ.* (2 ℕ.* k))      ≡⟨ cong evenℕ (lemma ℤ.∣ a ∣) ⟩
    evenℕ ((ℤ.∣ a ∣ ℕ.* k) ℕ.* 2)      ≡⟨ cong (ℕ._≡ᵇ 0) (ℕDM.m*n%n≡0 (ℤ.∣ a ∣ ℕ.* k) 2) ⟩
    true ∎
    where
      open ≡-Reasoning
      lemma : ∀ m -> m ℕ.* (2 ℕ.* k) ≡ (m ℕ.* k) ℕ.* 2
      lemma m = trans (cong (m ℕ.*_) (ℕP.*-comm 2 k)) (sym (ℕP.*-assoc m k 2))

  -- a * 2^(n+1+j) = b * 2^n implies that b is even.
  odd-lemma : ∀ a b n j -> a ℤ.* + 2^ (suc (n ℕ.+ j)) ≡ b ℤ.* + 2^ n -> evenℤ b ≡ true
  odd-lemma a b n j eq = trans (cong evenℤ (sym b≡)) (even-* a (2^ j))
    where
      N J : ℕ
      N = 2^ n
      J = 2^ j
      open ≡-Reasoning
      lemma : a ℤ.* + (2 ℕ.* (N ℕ.* J)) ≡ (a ℤ.* + (2 ℕ.* J)) ℤ.* + N
      lemma = begin
        a ℤ.* + (2 ℕ.* (N ℕ.* J))            ≡⟨ cong (a ℤ.*_) (ℤP.pos-* 2 (N ℕ.* J)) ⟩
        a ℤ.* (+ 2 ℤ.* + (N ℕ.* J))          ≡⟨ cong (λ z -> a ℤ.* (+ 2 ℤ.* z)) (ℤP.pos-* N J) ⟩
        a ℤ.* (+ 2 ℤ.* (+ N ℤ.* + J))        ≡⟨ solve 4 (λ a t n j -> a :* (t :* (n :* j)) := (a :* (t :* j)) :* n)
                                                   refl a (+ 2) (+ N) (+ J) ⟩
        (a ℤ.* (+ 2 ℤ.* + J)) ℤ.* + N        ≡⟨ cong (λ z -> (a ℤ.* z) ℤ.* + N) (sym (ℤP.pos-* 2 J)) ⟩
        (a ℤ.* + (2 ℕ.* J)) ℤ.* + N ∎
      b≡ : a ℤ.* + (2 ℕ.* J) ≡ b
      b≡ = ℤP.*-cancelʳ-≡ _ _ (+ N) {{nz n}} (begin
        (a ℤ.* + (2 ℕ.* J)) ℤ.* + N           ≡⟨ sym lemma ⟩
        a ℤ.* + (2 ℕ.* (N ℕ.* J))             ≡⟨ cong (λ k -> a ℤ.* + (2 ℕ.* k)) (sym (ℕP.^-distribˡ-+-* 2 n j)) ⟩
        a ℤ.* + 2^ (suc (n ℕ.+ j))            ≡⟨ eq ⟩
        b ℤ.* + N ∎)

-- ----------------------------------------------------------------------
-- * Dyadic fractions as unnormalised rationals

infix 8 _/2^_
_/2^_ : ℤ -> ℕ -> ℚᵘ
a /2^ n = (a ℚᵘ./ 2^ n) {{nz n}}

-- The value of a dyadic fraction as an unnormalised rational.
u : Dyadic -> ℚᵘ
u (Dyadic' a n _) = a /2^ n

toℚ-u : ∀ x -> toℚ x ≡ ℚ.fromℚᵘ (u x)
toℚ-u (Dyadic' a n _) = sym (fromℚᵘ-/ a (2^ n) {{nz n}})

toℚ-0 : toℚ (0# {Dyadic}) ≡ ℚ.0ℚ
toℚ-0 = refl

toℚ-1 : toℚ (1# {Dyadic}) ≡ ℚ.1ℚ
toℚ-1 = refl

-- ----------------------------------------------------------------------
-- * toℚ is injective (since the representation is canonical)

private
  Dyadic'-cong : ∀ {a b n m} .{c c'} -> a ≡ b -> n ≡ m -> Dyadic' a n c ≡ Dyadic' b m c'
  Dyadic'-cong refl refl = refl

  -- Canonical representations of the same number are equal.
  canonical-unique : ∀ a n b m -> T (Canonical a n) -> T (Canonical b m) ->
                     a ℤ.* + 2^ m ≡ b ℤ.* + 2^ n -> (a ≡ b) × (n ≡ m)
  canonical-unique a n b m ca cb eq with ℕP.<-cmp n m
  ... | tri≈ _ refl _ = ℤP.*-cancelʳ-≡ a b (+ 2^ n) {{nz n}} eq , refl
  ... | tri< n<m _ _ = ⊥-elim (subst (λ t -> T (not t)) (odd-lemma a b n j eq') cb')
    where
      j = m ℕ.∸ suc n
      hm : suc (n ℕ.+ j) ≡ m
      hm = ℕP.m+[n∸m]≡n n<m
      eq' : a ℤ.* + 2^ (suc (n ℕ.+ j)) ≡ b ℤ.* + 2^ n
      eq' = subst (λ k -> a ℤ.* + 2^ k ≡ b ℤ.* + 2^ n) (sym hm) eq
      cb' : T (Canonical b (suc (n ℕ.+ j)))
      cb' = subst (λ k -> T (Canonical b k)) (sym hm) cb
  ... | tri> _ _ m<n = ⊥-elim (subst (λ t -> T (not t)) (odd-lemma b a m j eq') ca')
    where
      j = n ℕ.∸ suc m
      hn : suc (m ℕ.+ j) ≡ n
      hn = ℕP.m+[n∸m]≡n m<n
      eq' : b ℤ.* + 2^ (suc (m ℕ.+ j)) ≡ a ℤ.* + 2^ m
      eq' = subst (λ k -> b ℤ.* + 2^ k ≡ a ℤ.* + 2^ m) (sym hn) (sym eq)
      ca' : T (Canonical a (suc (m ℕ.+ j)))
      ca' = subst (λ k -> T (Canonical a k)) (sym hn) ca

toℚ-injective : ∀ {x y : Dyadic} -> toℚ x ≡ toℚ y -> x ≡ y
toℚ-injective {x@(Dyadic' a n c)} {y@(Dyadic' b m c')} eq
  with canonical-unique a n b m (recompute-T _ c) (recompute-T _ c')
         (/ᵘ-≃⁻¹ a b (2^ n) (2^ m) {{nz n}} {{nz m}}
           (ℚP.fromℚᵘ-injective (trans (sym (toℚ-u x)) (trans eq (toℚ-u y)))))
... | a≡b , n≡m = Dyadic'-cong a≡b n≡m

private
  +-lemma : ∀ a b (P J M : ℕ) -> M ≡ P ℕ.* J ->
            (a ℤ.* + J ℤ.+ b) ℤ.* + (P ℕ.* M) ≡ (a ℤ.* + M ℤ.+ b ℤ.* + P) ℤ.* + M
  +-lemma a b P J .(P ℕ.* J) refl = begin
    (a ℤ.* + J ℤ.+ b) ℤ.* + (P ℕ.* (P ℕ.* J))
      ≡⟨ cong (λ z -> (a ℤ.* + J ℤ.+ b) ℤ.* z) (trans (ℤP.pos-* P (P ℕ.* J)) (cong (+ P ℤ.*_) (ℤP.pos-* P J))) ⟩
    (a ℤ.* + J ℤ.+ b) ℤ.* (+ P ℤ.* (+ P ℤ.* + J))
      ≡⟨ solve 4 (λ a b p j -> (a :* j :+ b) :* (p :* (p :* j)) := (a :* (p :* j) :+ b :* p) :* (p :* j))
           refl a b (+ P) (+ J) ⟩
    (a ℤ.* (+ P ℤ.* + J) ℤ.+ b ℤ.* + P) ℤ.* (+ P ℤ.* + J)
      ≡⟨ cong₂ (λ z w -> (a ℤ.* z ℤ.+ b ℤ.* + P) ℤ.* w) (sym (ℤP.pos-* P J)) (sym (ℤP.pos-* P J)) ⟩
    (a ℤ.* + (P ℕ.* J) ℤ.+ b ℤ.* + P) ℤ.* + (P ℕ.* J) ∎
    where open ≡-Reasoning

  +-lemma' : ∀ a b (P J N : ℕ) -> N ≡ P ℕ.* J ->
             (a ℤ.+ b ℤ.* + J) ℤ.* + (N ℕ.* P) ≡ (a ℤ.* + P ℤ.+ b ℤ.* + N) ℤ.* + N
  +-lemma' a b P J .(P ℕ.* J) refl = begin
    (a ℤ.+ b ℤ.* + J) ℤ.* + ((P ℕ.* J) ℕ.* P)
      ≡⟨ cong (λ z -> (a ℤ.+ b ℤ.* + J) ℤ.* z) (trans (ℤP.pos-* (P ℕ.* J) P) (cong (ℤ._* + P) (ℤP.pos-* P J))) ⟩
    (a ℤ.+ b ℤ.* + J) ℤ.* ((+ P ℤ.* + J) ℤ.* + P)
      ≡⟨ solve 4 (λ a b p j -> (a :+ b :* j) :* ((p :* j) :* p) := (a :* p :+ b :* (p :* j)) :* (p :* j))
           refl a b (+ P) (+ J) ⟩
    (a ℤ.* + P ℤ.+ b ℤ.* (+ P ℤ.* + J)) ℤ.* (+ P ℤ.* + J)
      ≡⟨ cong₂ (λ z w -> (a ℤ.* + P ℤ.+ b ℤ.* z) ℤ.* w) (sym (ℤP.pos-* P J)) (sym (ℤP.pos-* P J)) ⟩
    (a ℤ.* + P ℤ.+ b ℤ.* + (P ℕ.* J)) ℤ.* + (P ℕ.* J) ∎
    where open ≡-Reasoning

  2^-split : ∀ n m -> n ℕ.≤ m -> 2^ m ≡ 2^ n ℕ.* 2^ (m ℕ.∸ n)
  2^-split n m n≤m = trans (cong 2^ (sym (ℕP.m+[n∸m]≡n n≤m))) (ℕP.^-distribˡ-+-* 2 n (m ℕ.∸ n))

  -- 2ⁿ = (2ᵏ)^⌊n/k⌋ ⋅ 2^(n mod k).
  2^-divmod : ∀ n k .{{_ : ℕ.NonZero k}} -> 2^ n ≡ (2^ k) ℕ.^ (n ℕ./ k) ℕ.* 2^ (n ℕ.% k)
  2^-divmod n k = begin
    2^ n                                    ≡⟨ cong 2^ (ℕDM.m≡m%n+[m/n]*n n k) ⟩
    2^ (n ℕ.% k ℕ.+ (n ℕ./ k) ℕ.* k)          ≡⟨ ℕP.^-distribˡ-+-* 2 (n ℕ.% k) ((n ℕ./ k) ℕ.* k) ⟩
    2^ (n ℕ.% k) ℕ.* 2^ ((n ℕ./ k) ℕ.* k)     ≡⟨ cong (λ z -> 2^ (n ℕ.% k) ℕ.* 2^ z) (ℕP.*-comm (n ℕ./ k) k) ⟩
    2^ (n ℕ.% k) ℕ.* 2^ (k ℕ.* (n ℕ./ k))     ≡⟨ cong (2^ (n ℕ.% k) ℕ.*_) (sym (ℕP.^-*-assoc 2 k (n ℕ./ k))) ⟩
    2^ (n ℕ.% k) ℕ.* (2^ k) ℕ.^ (n ℕ./ k)     ≡⟨ ℕP.*-comm (2^ (n ℕ.% k)) _ ⟩
    (2^ k) ℕ.^ (n ℕ./ k) ℕ.* 2^ (n ℕ.% k) ∎
    where open ≡-Reasoning

-- The fast power of two of Quantum.Synthesis.Ring is 2^.
pow2≡2^ : ∀ n -> pow2 n ≡ 2^ n
pow2≡2^ n = sym (trans (2^-divmod n 64) (cong ((2^ 64) ℕ.^ (n ℕ./ 64) ℕ.*_) (2^-divmod (n ℕ.% 64) 8)))

-- Hence shiftL a n = a ⋅ 2ⁿ.
shiftL≡ : ∀ a n -> shiftL a n ≡ a ℤ.* + 2^ n
shiftL≡ a n = cong (λ z -> a ℤ.* + z) (pow2≡2^ n)

-- ----------------------------------------------------------------------
-- * The smart constructor dyadic
--
-- The smart constructor "dyadic a n" of Quantum.Synthesis.Ring should
-- satisfy the following specification.

DyadicSpec : Set
DyadicSpec = ∀ a n -> toℚ (dyadic a n) ≡ (a ℚ./ 2^ n) {{nz n}}

-- However, this cannot be proved in Agda for the present definition
--
--   dyadic a (suc n) with evenℤ a in eq
--   ... | true = dyadic (shiftR a 1) n
--   ... | false = Dyadic' a (suc n) (subst (λ b -> T (not b)) (sym eq) _)
--
-- The generated with-function takes the proof refl : evenℤ a ≡ evenℤ a
-- as an argument, so in a goal containing "dyadic a (suc n)" (for a
-- variable a) no with-abstraction (or rewrite) over evenℤ a is
-- well-typed, and "dyadic a (suc n)" can never be reduced. Hence the
-- rest of this module takes DyadicSpec as a module parameter.
--
-- The following definition computes the same values with the same
-- algorithm, but avoids the problem (the case split is on T? (evenℤ a),
-- which does not occur in any type). We prove that it satisfies the
-- specification; if Quantum.Synthesis.Ring adopts this definition,
-- dyadic-spec′ proves DyadicSpec.

private
  ¬T⇒T-not : ∀ {b} -> ¬ T b -> T (not b)
  ¬T⇒T-not {true} ¬t = ¬t tt
  ¬T⇒T-not {false} _ = tt

  T⇒≡true : ∀ {b} -> T b -> b ≡ true
  T⇒≡true {true} _ = refl

-- Since Ring.agda now defines dyadic by a case split on T? (evenℤ a),
-- dyadic′ is just dyadic.
dyadic′ : ℤ -> ℕ -> Dyadic
dyadic′ = dyadic

private
  -- Halving an even numerator: (a/2)/2ⁿ = a/2ⁿ⁺¹.
  halve-≃ : ∀ a n -> T (evenℤ a) -> shiftR a 1 /2^ n ℚᵘ.≃ a /2^ (suc n)
  halve-≃ a n e = /ᵘ-≃ (shiftR a 1) a (2^ n) (2^ (suc n)) {{nz n}} {{nz (suc n)}} lemma
    where
      lemma : shiftR a 1 ℤ.* + 2^ (suc n) ≡ a ℤ.* + 2^ n
      lemma = begin
        shiftR a 1 ℤ.* + (2 ℕ.* 2^ n)         ≡⟨ cong (shiftR a 1 ℤ.*_) (ℤP.pos-* 2 (2^ n)) ⟩
        shiftR a 1 ℤ.* (+ 2 ℤ.* + 2^ n)       ≡⟨ sym (ℤP.*-assoc (shiftR a 1) (+ 2) (+ 2^ n)) ⟩
        (shiftR a 1 ℤ.* + 2) ℤ.* + 2^ n       ≡⟨ cong (ℤ._* + 2^ n) (shiftR-even a (T⇒≡true e)) ⟩
        a ℤ.* + 2^ n ∎
        where open ≡-Reasoning

-- (dyadic first distinguishes the numerator 0, so the cases a = + suc _
-- and a = -[1+ _ ] are treated separately.)
u-dyadic′ : ∀ a n -> u (dyadic′ a n) ℚᵘ.≃ a /2^ n
u-dyadic′ (+ zero) n = /ᵘ-≃ (+ zero) (+ zero) 1 (2^ n) {{_}} {{nz n}} refl
u-dyadic′ a@(+ suc _) zero = ℚᵘP.≃-refl
u-dyadic′ a@(-[1+ _ ]) zero = ℚᵘP.≃-refl
u-dyadic′ a@(+ suc _) (suc n) with T? (evenℤ a)
... | yes e = ℚᵘP.≃-trans (u-dyadic′ (shiftR a 1) n) (halve-≃ a n e)
... | no _ = ℚᵘP.≃-refl
u-dyadic′ a@(-[1+ _ ]) (suc n) with T? (evenℤ a)
... | yes e = ℚᵘP.≃-trans (u-dyadic′ (shiftR a 1) n) (halve-≃ a n e)
... | no _ = ℚᵘP.≃-refl

dyadic-spec′ : ∀ a n -> toℚ (dyadic′ a n) ≡ (a ℚ./ 2^ n) {{nz n}}
dyadic-spec′ a n = trans (toℚ-u (dyadic′ a n))
  (trans (ℚP.fromℚᵘ-cong (u-dyadic′ a n)) (fromℚᵘ-/ a (2^ n) {{nz n}}))

-- Changing a denominator bound preserves the represented number.
abstract
  dyadic-canonical : ∀ (x : Dyadic) -> dyadic (Dyadic.numerator x) (Dyadic.exponent x) ≡ x
  dyadic-canonical x@(Dyadic' a n _) = toℚ-injective {x = dyadic a n} {y = x} (dyadic-spec′ a n)

  dyadic-equal : ∀ a b n m -> a ℤ.* + 2^ m ≡ b ℤ.* + 2^ n -> dyadic a n ≡ dyadic b m
  dyadic-equal a b n m h = toℚ-injective {x = dyadic a n} {y = dyadic b m}
    (trans (toℚ-u (dyadic a n))
      (trans (ℚP.fromℚᵘ-cong
        (ℚᵘP.≃-trans (u-dyadic′ a n)
          (ℚᵘP.≃-trans (/ᵘ-≃ a b (2^ n) (2^ m) {{nz n}} {{nz m}} h)
            (ℚᵘP.≃-sym (u-dyadic′ b m)))))
        (sym (toℚ-u (dyadic b m)))))

  dyadic-upscale : ∀ a n m -> n ℕ.≤ m -> dyadic (shiftL a (m ℕ.∸ n)) m ≡ dyadic a n
  dyadic-upscale a n m h = dyadic-equal (shiftL a (m ℕ.∸ n)) a m n
    (trans (cong (λ t -> t ℤ.* + 2^ n) (shiftL≡ a (m ℕ.∸ n)))
      (trans (ℤP.*-assoc a (+ 2^ (m ℕ.∸ n)) (+ 2^ n))
        (cong (a ℤ.*_) (trans (sym (ℤP.pos-* (2^ (m ℕ.∸ n)) (2^ n)))
          (cong +_ (trans (ℕP.*-comm (2^ (m ℕ.∸ n)) (2^ n)) (sym (2^-split n m h))))))))

  dyadic-numerator-injective : ∀ a b n -> dyadic a n ≡ dyadic b n -> a ≡ b
  dyadic-numerator-injective a b n h = ℤP.*-cancelʳ-≡ a b (+ 2^ n) {{nz n}}
    (/ᵘ-≃⁻¹ a b (2^ n) (2^ n) {{nz n}} {{nz n}}
      (ℚᵘP.≃-trans (ℚᵘP.≃-sym (u-dyadic′ a n))
        (ℚᵘP.≃-trans (ℚᵘP.≃-reflexive (cong u h)) (u-dyadic′ b n))))

dyadic-exponent-bound : ∀ a n -> Dyadic.exponent (dyadic a n) ℕ.≤ n
dyadic-exponent-bound (+ zero) n = ℕ.z≤n
dyadic-exponent-bound (+ suc a) zero = ℕ.z≤n
dyadic-exponent-bound -[1+ a ] zero = ℕ.z≤n
dyadic-exponent-bound a@(+ suc _) (suc n) with T? (evenℤ a)
... | yes e = ℕP.m≤n⇒m≤1+n (dyadic-exponent-bound (shiftR a 1) n)
... | no e = ℕP.≤-refl
dyadic-exponent-bound a@(-[1+ _ ]) (suc n) with T? (evenℤ a)
... | yes e = ℕP.m≤n⇒m≤1+n (dyadic-exponent-bound (shiftR a 1) n)
... | no e = ℕP.≤-refl

integer-of-dyadic-correct : ∀ x m -> Dyadic.exponent x ℕ.≤ m -> dyadic (integer-of-dyadic x m) m ≡ x
integer-of-dyadic-correct x@(Dyadic' a n _) m h with n ℕ.≤ᵇ m in eq
... | true = trans (dyadic-upscale a n m h) (dyadic-canonical x)
... | false = ⊥-elim (subst T eq (ℕP.≤⇒≤ᵇ h))

-- ----------------------------------------------------------------------
-- * toℚ is a ring homomorphism (given the specification of dyadic)

module _ (dyadic-spec : DyadicSpec) where

  u-dyadic : ∀ a n -> u (dyadic a n) ℚᵘ.≃ a /2^ n
  u-dyadic a n = ℚP.fromℚᵘ-injective
    (trans (sym (toℚ-u (dyadic a n))) (trans (dyadic-spec a n) (sym (fromℚᵘ-/ a (2^ n) {{nz n}}))))

  u-+ : ∀ x y -> u (x + y) ℚᵘ.≃ u x ℚᵘ.+ u y
  u-+ (Dyadic' a n _) (Dyadic' b m _) with n ℕ.≤ᵇ m in le
  ... | true = ℚᵘP.≃-trans (u-dyadic (shiftL a (m ℕ.∸ n) ℤ.+ b) m)
                 (ℚᵘP.≃-trans (ℚᵘP.≃-reflexive (cong (λ z -> (z ℤ.+ b) /2^ m) (shiftL≡ a (m ℕ.∸ n))))
                 (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (2^ m) (2^ n ℕ.* 2^ m) {{nz m}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                                 (+-lemma a b (2^ n) (2^ (m ℕ.∸ n)) (2^ m) (2^-split n m n≤m)))
                   (ℚᵘP.≃-reflexive (sym (/ᵘ-+ a b (2^ n) (2^ m) {{nz n}} {{nz m}})))))
    where
      n≤m : n ℕ.≤ m
      n≤m = ℕP.≤ᵇ⇒≤ n m (subst T (sym le) tt)
  ... | false = ℚᵘP.≃-trans (u-dyadic (a ℤ.+ shiftL b (n ℕ.∸ m)) n)
                 (ℚᵘP.≃-trans (ℚᵘP.≃-reflexive (cong (λ z -> (a ℤ.+ z) /2^ n) (shiftL≡ b (n ℕ.∸ m))))
                 (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (2^ n) (2^ n ℕ.* 2^ m) {{nz n}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                                 (+-lemma' a b (2^ m) (2^ (n ℕ.∸ m)) (2^ n) (2^-split m n m≤n)))
                   (ℚᵘP.≃-reflexive (sym (/ᵘ-+ a b (2^ n) (2^ m) {{nz n}} {{nz m}})))))
    where
      m≤n : m ℕ.≤ n
      m≤n = ℕP.≰⇒≥ (λ n≤m -> subst T le (ℕP.≤⇒≤ᵇ n≤m))

  u-* : ∀ x y -> u (x * y) ℚᵘ.≃ u x ℚᵘ.* u y
  u-* (Dyadic' a n _) (Dyadic' b m _) =
    ℚᵘP.≃-trans (u-dyadic (a ℤ.* b) (n ℕ.+ m))
      (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (2^ (n ℕ.+ m)) (2^ n ℕ.* 2^ m) {{nz (n ℕ.+ m)}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                      (cong (λ k -> (a ℤ.* b) ℤ.* + k) (sym (ℕP.^-distribˡ-+-* 2 n m))))
        (ℚᵘP.≃-reflexive (sym (/ᵘ-* a b (2^ n) (2^ m) {{nz n}} {{nz m}}))))

  u-neg : ∀ x -> u (- x) ℚᵘ.≃ ℚᵘ.- u x
  u-neg (Dyadic' a n _) = ℚᵘP.≃-trans (u-dyadic (ℤ.- a) n) (ℚᵘP.≃-reflexive (sym (/ᵘ-neg a (2^ n) {{nz n}})))

  toℚ-+ : ∀ x y -> toℚ (x + y) ≡ toℚ x ℚ.+ toℚ y
  toℚ-+ x y = begin
    toℚ (x + y)                         ≡⟨ toℚ-u (x + y) ⟩
    ℚ.fromℚᵘ (u (x + y))                ≡⟨ ℚP.fromℚᵘ-cong (u-+ x y) ⟩
    ℚ.fromℚᵘ (u x ℚᵘ.+ u y)             ≡⟨ fromℚᵘ-+ (u x) (u y) ⟩
    ℚ.fromℚᵘ (u x) ℚ.+ ℚ.fromℚᵘ (u y)   ≡⟨ sym (cong₂ ℚ._+_ (toℚ-u x) (toℚ-u y)) ⟩
    toℚ x ℚ.+ toℚ y ∎
    where open ≡-Reasoning

  toℚ-* : ∀ x y -> toℚ (x * y) ≡ toℚ x ℚ.* toℚ y
  toℚ-* x y = begin
    toℚ (x * y)                         ≡⟨ toℚ-u (x * y) ⟩
    ℚ.fromℚᵘ (u (x * y))                ≡⟨ ℚP.fromℚᵘ-cong (u-* x y) ⟩
    ℚ.fromℚᵘ (u x ℚᵘ.* u y)             ≡⟨ fromℚᵘ-* (u x) (u y) ⟩
    ℚ.fromℚᵘ (u x) ℚ.* ℚ.fromℚᵘ (u y)   ≡⟨ sym (cong₂ ℚ._*_ (toℚ-u x) (toℚ-u y)) ⟩
    toℚ x ℚ.* toℚ y ∎
    where open ≡-Reasoning

  toℚ-neg : ∀ x -> toℚ (- x) ≡ ℚ.- toℚ x
  toℚ-neg x = begin
    toℚ (- x)                  ≡⟨ toℚ-u (- x) ⟩
    ℚ.fromℚᵘ (u (- x))         ≡⟨ ℚP.fromℚᵘ-cong (u-neg x) ⟩
    ℚ.fromℚᵘ (ℚᵘ.- u x)        ≡⟨ fromℚᵘ-neg (u x) ⟩
    ℚ.- ℚ.fromℚᵘ (u x)         ≡⟨ sym (cong ℚ.-_ (toℚ-u x)) ⟩
    ℚ.- toℚ x ∎
    where open ≡-Reasoning

  -- ----------------------------------------------------------------------
  -- * The commutative ring 𝔻

  rawRing-Dyadic : RawRing 0ℓ 0ℓ
  rawRing-Dyadic = record
    { Carrier = Dyadic ; _≈_ = _≡_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = -_ ; 0# = 0# ; 1# = 1# }

  toℚ-isRingMonomorphism : IsRingMonomorphism rawRing-Dyadic ℚ.+-*-rawRing toℚ
  toℚ-isRingMonomorphism = record
    { isRingHomomorphism = record
      { isSemiringHomomorphism = record
        { isNearSemiringHomomorphism = record
          { +-isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = cong toℚ }
              ; homo = toℚ-+ }
            ; ε-homo = toℚ-0 }
          ; *-homo = toℚ-* }
        ; 1#-homo = toℚ-1 }
      ; -‿homo = toℚ-neg }
    ; injective = toℚ-injective }

  isCommutativeRing-Dyadic : IsCommutativeRing (_≡_ {A = Dyadic}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-Dyadic =
    RingMonomorphisms.isCommutativeRing toℚ-isRingMonomorphism ℚP.+-*-isCommutativeRing

  commutativeRing-Dyadic : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Dyadic = record { isCommutativeRing = isCommutativeRing-Dyadic }
