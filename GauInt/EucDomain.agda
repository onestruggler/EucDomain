-- We show Gausssian Integers forms an Euclidean domain. The proofs
-- are straightforward.

{-# OPTIONS --without-K --safe #-}

module GauInt.EucDomain where

-- imports from local.

-- Hiding the usual div and mod function. We will the new instance in
-- Integer.EucDomain2
import Instances hiding (DMℤ)
open Instances

open import Integer.EucDomain2
  renaming (div' to divℤ ; mod' to modℤ ; euc-eq' to euc-eqℤ ; euc-rank' to euc-rankℤ)
open import Integer.Properties

open import GauInt.Base
  using (𝔾 ; _+_i ; _ᶜ ; Re ; Im ; _+0i ; _+0i' ; 0𝔾 ; 1𝔾)
open import GauInt.Properties
open import GauInt.Instances


-- imports from stdlib and Agda. 
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality 

open import Data.Product as P using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum as S renaming ([_,_]′ to ⊎-elim)

open import Data.Nat as Nat using (ℕ ; suc ; zero ; z≤n)
import Data.Nat.Properties as NatP
open import Data.Integer as Int
  using (0ℤ ; +0 ; +_ ; _≥_ ; +≤+ ; +[1+_] ; -[1+_] ; ℤ ; ∣_∣)
import Data.Integer.Properties as IntP

import Data.Nat.Solver as NS
import Data.Integer.Solver as IS
import GauInt.Solver as GS
open import Algebra.Properties.Ring +-*-ring
open import Algebra.Definitions (_≡_ {A = 𝔾}) using (AlmostLeftCancellative)

open import Function.Base using (_$_)

-- ----------------------------------------------------------------------
-- Euclidean Structure on 𝔾

-- As explained in the imports part, we will use the div and mod
-- function defined in Integer.EucDomain2.


-- A special case when the divisor is a positive natural number. The proof:
-- Let x = a + b i, and y = d. By integer euc-eq and euc-rank we have
-- step-a : a = ra + qa * d, with rank ra ≤ d / 2.
-- step-b : b = rb + qb * d, with rank rb ≤ d / 2.
-- We let q = qa + qb i, r = ra + rb i. Easy to check that
-- eq : x = r + q y. Slightly harder to check
-- le : rank r ≤ d / 2 (see below).

div' : 𝔾 -> (d : ℕ) -> ¬ d ≡ 0# -> 𝔾
div' n zero n0 with n0 refl
... | ()
div' (a + b i) d@(suc e) n0 = qa + qb i
  where
    qa = a / + d
    qb = b / + d    

mod' : 𝔾 -> (d : ℕ) -> ¬ d ≡ 0# -> 𝔾
mod' n zero n0 with n0 refl
... | ()
mod' (a + b i) d@(suc e) n0 = ra + rb i
  where
    ra = a % + d
    rb = b % + d    

div : (x y : 𝔾) -> ¬ y ≡ 0# -> 𝔾
div x y n0 = div' (x * y ᶜ) y*yᶜ n0'
  where
    y*yᶜ : ℕ
    y*yᶜ = rank y

    n0' :  ¬ rank y ≡ 0#
    n0' = y≠0#⇒rank≠0 n0

mod : (x y : 𝔾) -> ¬ y ≡ 0# -> 𝔾
mod x y n0 = (x - q * y)
  where
    q = div x y n0


-- ----------------------------------------------------------------------
-- euc-eq and euc-rank property for div' and mod'

-- Dividend = reminder + quotient * divisor.
euc-eq' : ∀ (x : 𝔾) (d : ℕ) (n0 : ¬ d ≡ 0) ->
             let r = mod' x d n0 in let q = div' x d n0 in 
             x ≡ r + q * (d +0i) 
euc-eq' n zero n0 with n0 refl
... | ()
euc-eq' x@(a + b i) d@(suc e) n0 = eq
  where
    -- setting up q and r.
    n0' : ¬ + d ≡ 0#
    n0' p = n0 (IntP.+-injective p)
    
    qa = a / + d
    qb = b / + d
    ra = a % + d
    rb = b % + d

    ea : a ≡ ra + qa * + d 
    ea = euc-eqℤ a (+ d) n0'
    eb : b ≡ rb + qb * + d 
    eb = euc-eqℤ b (+ d) n0'

    q : 𝔾
    q = qa + qb i  

    r : 𝔾
    r = ra + rb i  

    -- Inject natural number d to Gaussian integer.
    y = d +0i

    -- Proving x = r + q * y.
    eq : x ≡ r + q * y
    eq = begin
        x ≡⟨ refl ⟩ 
        a + b i ≡⟨ cong (λ x -> x + b i) ea ⟩ 
        (ra + qa * (+ d)) + b i ≡⟨ cong (λ x -> (ra + qa * (+ d)) + x i) eb ⟩ 
        (ra + qa * (+ d)) + (rb + qb * (+ d)) i ≡⟨ refl ⟩ 
        (ra + rb i) + ((qa * (+ d)) + (qb * (+ d)) i) ≡⟨ cong (λ x → (ra + rb i) + ((qa * (+ d)) + x i)) ((solve 3 (λ qa d qb → qb :* d := qa :* con 0ℤ :+ qb :* d) refl) qa (+ d) qb) ⟩
        (ra + rb i) + ((qa * (+ d)) + (qa * 0ℤ + qb * (+ d)) i) ≡⟨ cong (λ x → (ra + rb i) + (x + (qa * 0ℤ + qb * (+ d)) i)) ((solve 3 (λ qa d qb → qa :* d := qa :* d :- qb :* con 0ℤ) refl) qa (+ d) qb) ⟩ 
        (ra + rb i) + ((qa * (+ d) - qb * 0ℤ) + (qa * 0ℤ + qb * (+ d)) i) ≡⟨ refl ⟩ 
        (ra + rb i) + (qa + qb i) * y ≡⟨ refl ⟩ 
        r + q * y ∎
          where
            open IS.+-*-Solver
            open ≡-Reasoning


-- rank r < rank (inj d)
euc-rank' : ∀ (x : 𝔾) (d : ℕ) (n0 : ¬ d ≡ 0) ->
             let r = mod' x d n0 in let q = div' x d n0 in 
             rank r < rank (d +0i) 
euc-rank' n zero n0 with n0 refl
... | ()
euc-rank' x@(a + b i) d@(suc e) n0 = le
  where
    -- setting up q and r.
    n0' : ¬ + d ≡ 0#
    n0' p = n0 (IntP.+-injective p)
  
    r : 𝔾 
    r = mod' x d n0
    ra = Re r
    rb = Im r

    q : 𝔾 
    q = div' x d n0
    qa = Re q
    qb = Im q

    lea : ∣ ra ∣ ≤ d / 2
    lea = euc-rankℤ a (+ d) n0'

    leb : ∣ rb ∣ ≤ d / 2
    leb = euc-rankℤ b (+ d) n0'

    y = d +0i
    
    -- Proving rank r < rank y. 
    -- Some auxillary lemmas. 
    lem1 : ∀ {d : ℕ} -> d / 2 + d / 2 ≤ d
    lem1 {d} = begin
      d / 2 + d / 2  ≡⟨ solve 1 (λ x → x :+ x := x :* con 2) refl (d / 2) ⟩
      d / 2 * 2      ≤⟨ NatP.m≤n+m (d / 2 * 2) (d % 2) ⟩
      d % 2 + d / 2 * 2  ≡⟨ (sym $ NatESR.euc-eq d 2 (λ ())) ⟩
      d  ∎
        where
          open NatP.≤-Reasoning
          open NS.+-*-Solver

    lem2 : ∀ {d : Nat.ℕ} -> d / 2 ≤ d
    lem2 {d} = begin
      d / 2  ≤⟨ NatP.m≤n+m (d / 2) (d / 2) ⟩
      d / 2 + d / 2      ≤⟨ lem1 {d} ⟩
      d  ∎
        where
          open NatP.≤-Reasoning
          open NS.+-*-Solver

    lem2-strict : ∀ {d : Nat.ℕ} .{{_ : NonZero d}} -> (d / 2) < d
    lem2-strict {x@(suc d)} with x / 2 Nat.≟ 0
    ... | no ¬p = begin-strict
      x / 2  <⟨ NatP.m<n+m (x / 2) x/2>0 ⟩
      x / 2 + x / 2      ≤⟨ lem1 {x} ⟩
      x  ∎
      where
        open NatP.≤-Reasoning
        open NS.+-*-Solver
        open import Relation.Binary.Definitions
        open import Data.Empty

        x/2>0 : 0 < (x / 2)
        x/2>0 with NatP.<-cmp 0 (x / 2)
        ... | tri< a ¬b ¬c = a
        ... | tri≈ ¬a b ¬c = ⊥-elim (¬p (sym b))
    ... | yes p rewrite p = Nat.s≤s Nat.z≤n


    lem3 : rank y ≡ d * d
    lem3 = begin
      rank y ≡⟨ refl ⟩ 
      ∣ (+ d) * (+ d) + 0ℤ * 0ℤ ∣  ≡⟨ cong ∣_∣ (solve 1 (λ x → x :* x :+ con 0ℤ :* con 0ℤ := x :* x) refl (+ d)) ⟩ 
      ∣ (+ d) * (+ d) ∣     ≡⟨ IntP.abs-*-commute (+ d) (+ d) ⟩ 
      ∣ (+ d) ∣ * ∣ (+ d) ∣     ≡⟨ refl ⟩ 
      d * d  ∎
        where
          open IS.+-*-Solver
          open ≡-Reasoning

    -- The proof idea:
    -- rank r = ∣ ra * ra + rb * rb ∣ = ∣ ra ∣ * ∣ ra ∣ + ∣ rb ∣ * ∣ rb ∣
    -- ≤ d / 2 * d / 2 + d / 2 * d / 2 by the integer divmod property.
    -- ≤ d * d
    -- = rank y

    le : rank r < rank y
    le = begin-strict
      rank r                ≡⟨ refl ⟩
      let (sa , sae) = (a*a=+b ra) in let (sb , sbe) = a*a=+b rb in
      ∣ ra * ra + rb * rb ∣  ≡⟨ tri-eq' ra rb ⟩ 
      ∣ ra * ra ∣ + ∣ rb * rb ∣ ≡⟨ cong₂ _+_ (IntP.abs-*-commute ra ra) (IntP.abs-*-commute rb rb) ⟩
      ∣ ra ∣ * ∣ ra ∣ + ∣ rb ∣ * ∣ rb ∣  ≤⟨ NatP.+-mono-≤ (NatP.*-mono-≤ lea lea) (NatP.*-mono-≤ leb leb) ⟩
      (d / 2) * (d / 2) + (d / 2) * (d / 2) ≡⟨ solve 1 (λ x → (x :* x) :+ (x :* x) := x :* (x :+ x)) refl (d / 2) ⟩
      (d / 2) * ((d / 2) + (d / 2)) ≤⟨ NatP.*-monoʳ-≤ (d / 2) lem1 ⟩ 
      (d / 2) * d <⟨ NatP.*-monoˡ-< d (lem2-strict {d}) ⟩ 
      d * d                ≡⟨ sym lem3 ⟩
      rank y  ∎
        where
          open NatP.≤-Reasoning
          open NS.+-*-Solver
    

-- ----------------------------------------------------------------------
-- euc-eq and euc-rank property for div and mod

-- This is the case when the divisor y = c + d i is an arbitrary
-- non-zero Gaussian integer. Easy to see rank y ᶜ = rank y = y * y
-- ᶜ = ∣ c * c + d * d ∣ ≠ 0. Notice that by the previous spcial
-- case (when the divisor is a positive natural number) we have

-- eq' : x * y ᶜ = r' + q' * (y * y ᶜ), and 
-- le' : rank r' < rank (y * y ᶜ) = rank y * rank y ᶜ 
-- (eq') ⇒ r' = x * y ᶜ - q' * (y * y ᶜ) = (x - q' * y) * y ᶜ 
-- ⇒ eqr: rank r' = rank (x - q' * y) * rank y ᶜ 
-- (le') & (eqr) ⇒ rank (x - q' * y) < rank y since rank y ᶜ ≠ 0.

-- So setting q = q', and r = x - q' * y as div and mod functions do,
-- then check the euc-rank property holds. 

-- Dividend = reminder + quotient * divisor.
euc-eq : ∀ (x y : 𝔾) (n0 : ¬ y ≡ 0𝔾) ->
             let r = mod x y n0 in let q = div x y n0 in 
             x ≡ r + q * y 
euc-eq x y n0 = claim
  where
    -- Setting up r and q.
    r : 𝔾 
    r = mod x y n0
    q : 𝔾 
    q = div x y n0

    claim : x ≡ (x - q * y) + q * y 
    claim = begin
      x ≡⟨ solve 2 (\ x qy -> x := (x :- qy) :+ qy) refl x (q * y) ⟩ 
      (x - q * y) + q * y  ∎
      where
        open GS.+-*-Solver
        open ≡-Reasoning

-- rank r < rank y.
euc-rank : ∀ (x y : 𝔾) (n0 : ¬ y ≡ 0#) ->
             let r = mod x y n0 in let q = div x y n0 in 
             rank r < rank y
euc-rank x y n0 = claim 
  where
    n0' : ¬ rank y ≡ 0#
    n0' = y≠0#⇒rank≠0 n0
    
    r : 𝔾 
    r = mod x y n0 
    q : 𝔾 
    q = div x y n0

    eq : x ≡ r + q * y
    eq = euc-eq x y n0

    r' : 𝔾 
    r' = mod' (x * y ᶜ) (rank y) n0'
    q' : 𝔾 
    q' = div' (x * y ᶜ) (rank y) n0'

    eq' : x * y ᶜ ≡ r' + q' * (rank y +0i)
    eq' = euc-eq' (x * y ᶜ) (rank y) n0'

    le' : rank r' < rank (rank y +0i) 
    le' = euc-rank' (x * y ᶜ) (rank y) n0'

    q=q' : q ≡ q'
    q=q' = refl

    -- eqr : rank r' = rank (x - q' * y) * rank y ᶜ ---- (3)
    eqr : rank r' ≡ rank (x - q' * y) * rank (y ᶜ)
    eqr = begin
      rank r' ≡⟨ cong rank step ⟩
      rank ((x - q' * y) * y ᶜ) ≡⟨ rank-*-commute (x - q * y) (y ᶜ) ⟩
      rank (x - q' * y) * rank (y ᶜ) ∎
        where
          open ≡-Reasoning
          step : r' ≡ (x - q' * y) * y ᶜ
          step = begin
            r' ≡⟨ solve 2 (λ r x → r := r :+ x :- x) refl r' (q' * (rank y +0i)) ⟩
            r' + q' * (rank y +0i) - q' * (rank y +0i) ≡⟨ cong (_- q' * (rank y +0i)) (sym eq') ⟩
            x * y ᶜ - q' * (rank y +0i) ≡⟨ cong (λ z → x * y ᶜ - q' * z) (sym $ y*yᶜ=rank {y}) ⟩
            x * y ᶜ - q' * (y * y ᶜ) ≡⟨ solve 4 (\ x yc q y -> x :* yc :- q :* ( y :* yc) := (x :- q :* y) :* yc) refl x (y ᶜ) q' y ⟩
            (x - q' * y) * y ᶜ ∎
              where
                open GS.+-*-Solver
                open ≡-Reasoning

    -- (le') & (eqr) ⇒ rank (x - q' * y) < rank y since rank y ᶜ ≠ 0.
    claim : rank (x - q' * y) < rank y
    claim = NatP.*-cancelʳ-< {rank (y ᶜ)} (rank (x - q * y)) (rank y) eqr'
      where
        eqr' : rank (x - q' * y) * rank (y ᶜ) < rank y * rank (y ᶜ)
        eqr' = begin-strict
            rank (x - q' * y) * rank (y ᶜ) ≡⟨ sym eqr ⟩ 
            rank r' <⟨ le' ⟩
            rank (rank y +0i) ≡⟨ cong rank (sym $ y*yᶜ=rank {y}) ⟩ 
            rank (y * y ᶜ) ≡⟨ rank-*-commute y (y ᶜ) ⟩ 
            rank y * rank (y ᶜ) ∎
              where
                open GS.+-*-Solver
                open NatP.≤-Reasoning


-- ----------------------------------------------------------------------
-- 𝔾 is an Euclidean Domain.

import EuclideanDomain
open   EuclideanDomain.Structures (_≡_ {A = 𝔾}) using (IsEuclideanDomain)
open   EuclideanDomain.Bundles using (EuclideanDomainBundle)

+-*-isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0𝔾 1𝔾
+-*-isEuclideanDomain = record
                              { isCommutativeRing = +-*-isCommutativeRing 
                              ; *-alc = *-alc-𝔾 
                              ; div = div 
                              ; mod = mod 
                              ; rank = rank 
                              ; euc-eq = euc-eq 
                              ; euc-rank = euc-rank 
                              }


-- Bundle.
+-*-euclideanDomain : EuclideanDomainBundle _ _
+-*-euclideanDomain = record
  { isEuclideanDomain = +-*-isEuclideanDomain'
  }


-- ----------------------------------------------------------------------
-- Making 𝔾 an DivMod instance, overloading div and mod.

-- Translation between two nonzeros.
nz𝔾 : ∀ (x : 𝔾) -> .{{NonZero x}} -> ¬ x ≡ 0#
nz𝔾 (+_ zero + +[1+ n ] i) {{n0}} i0 with i0 
... | ()


instance
  g-divmod : DivMod 𝔾
  DivMod.NZT g-divmod = NZT𝔾
  (g-divmod DivMod./ n) d = div n d (nz𝔾 d)
  (g-divmod DivMod.% n) d = mod n d (nz𝔾 d)
