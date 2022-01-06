-- We show by allowing the reminder of integer division to be
-- negative, we can get more precise estimation of the rank of the
-- remainder: rank reminder ≤ (rank divisor) / 2.

{-# OPTIONS --without-K --safe #-}

module Integer.EucDomain2 where

-- ----------------------------------------------------------------------
-- ℕ is an "Euclidean SemiRing".
module NatESR where
  -- ℕ satisfy the euc-eq and euc-rank property with the usual div and
  -- mod function. Still we need to do the translation from non-equality
  -- to NonZero predicate.

  -- imports form stdlib.
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  
  open import Data.Nat as Nat using (ℕ ; zero ; suc)

  import Data.Nat.DivMod as NDM
  import Data.Nat.Properties as NatP

  -- imports from local.
  open import Instances
  
  -- We already make ℕ an instance of Rank. For convinence we restate it
  -- here.
  rank' : ℕ -> ℕ
  rank' x = x

  -- Division with the annoying translation from ¬ d ≡ 0 to NonZero
  -- predicate.
  div : ∀ (n d : ℕ) -> ¬ d ≡ 0 -> ℕ
  div n zero n0 with n0 refl
  ... | ()
  div n (suc d) n0 = NDM._/_ n (suc d)

  -- Reminder.
  mod : ∀ (n d : ℕ) -> ¬ d ≡ 0 -> ℕ
  mod n zero n0 with n0 refl
  ... | ()
  mod n (suc d) n0 = NDM._%_ n (suc d)

  -- Dividend = reminder + quotient * divisor.
  euc-eq : ∀ (n d : ℕ) (n0 : ¬ d ≡ 0) ->
               let r = mod n d n0 in let q = div n d n0 in 
               n ≡ r + q * d 
  euc-eq n zero n0 with n0 refl
  ... | () 
  euc-eq n (suc d) n0 = NDM.m≡m%n+[m/n]*n n (suc d)

  -- rank reminder < rank divisor.
  euc-rank : ∀ (n d : ℕ) (n0 : ¬ d ≡ 0) ->
               let r = mod n d n0 in let q = div n d n0 in 
               rank r < rank d
  euc-rank n zero n0 with n0 refl
  ... | () 
  euc-rank n (suc d) n0 = NDM.m%n<n n (suc d)


-- ----------------------------------------------------------------------
-- Allow Integer division to have negative reminder

-- Let n, d be integers and d nonzero, by the usual divison with
-- reminder we have q, r such that n = r + q * d and ∣ r ∣ < ∣ d ∣.
-- What we want is q' and r' such that n = r' + q' * d and ∣ r' ∣ ≤ ∣
-- d ∣ / 2. Asssume d > 0, an easy calculation shows if ∣ r ∣ ≤ ∣ d ∣
-- / 2, we let q' = q and r' = r, and if ∣ r ∣ > ∣ d ∣ / 2, we let q'
-- = q + 1 and r' = r - d. The case when d < 0 is similar. 

-- imports from stdlib.
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_ ; refl ; sym ; cong ; trans)

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool using (T ; not)
open import Data.Nat as Nat using (ℕ ; suc ; s≤s ; zero ; z≤n)
import Data.Nat.DivMod as NDM
import Data.Nat.Properties as NatP
open import Data.Integer as Int
  using (ℤ ; ∣_∣ ; +_ ; +[1+_] ; -[1+_] ; 1ℤ ; _◃_ ; +<+ ; -<- ; -≤- ; -<+ ; -≤+ ; +≤+ ; 0ℤ)
import Data.Integer.Properties as IntP
open import Data.Integer.DivMod
  using (_div_ ; _mod_ ; a≡a%n+[a/n]*n ; n%d<d)
open import Data.Integer.Solver


-- imports from local.
open import Instances

-- Aother integer division allowing negative reminder. 
div' : ∀ (n d : ℤ) -> ¬ d ≡ 0ℤ -> ℤ
div' n (+_ zero) n0 with n0 refl
... | ()
div' n d@(+[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = n div d
... | no np =  1ℤ + n div d
div' n d@(-[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = n div d
... | no np =  - 1ℤ + n div d

-- Another integer mod allowing negative reminder. 
mod' : ∀ (n d : ℤ) -> ¬ d ≡ 0ℤ -> ℤ
mod' n (+_ zero) n0 with n0 refl
... | ()
mod' n d@(+[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = + (n mod d)
... | no np =  + (n mod d) - d
mod' n d@(-[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = + (n mod d)
... | no np =  + (n mod d) + d

-- Dividend = reminder + quotient * divisor.
euc-eq' : ∀ (n d : ℤ) (n0 : ¬ d ≡ 0ℤ) ->
             let r = mod' n d n0 in let q = div' n d n0 in 
             n ≡ r + q * d 
euc-eq' n (+_ zero) n0 with n0 refl
... | ()
euc-eq' n d@(+[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = a≡a%n+[a/n]*n n d 
... | no np =  claim
  where
    claim : n ≡ (+ (n mod d) - d) + (1ℤ + n div d) * d
    claim = begin
      n ≡⟨  a≡a%n+[a/n]*n n d  ⟩ 
      + (n mod d) + (n div d) * d ≡⟨ solve 3 (\ x y z -> x :+ y :* z := x :- z :+ (con 1ℤ :+ y) :* z) refl (+ (n mod d)) (n div d) d ⟩ 
      (+ (n mod d) - d) + (1ℤ + n div d) * d ∎
        where
          open +-*-Solver
          open PE.≡-Reasoning
euc-eq' n d@(-[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = a≡a%n+[a/n]*n n d 
... | no np = claim 
  where
    claim : n ≡ (+ (n mod d) + d) + (- 1ℤ + n div d) * d
    claim = begin
      n ≡⟨  a≡a%n+[a/n]*n n d  ⟩ 
      + (n mod d) + (n div d) * d ≡⟨ solve 3 (\ x y z -> x :+ y :* z := x :+ z :+ (con (- 1ℤ) :+ y) :* z) refl (+ (n mod d)) (n div d) d ⟩ 
      (+ (n mod d) + d) + (- 1ℤ + n div d) * d ∎
        where
          open +-*-Solver
          open PE.≡-Reasoning

-- rank reminder ≤ (rank divisor) / 2.
euc-rank' : ∀ (n d : ℤ) (n0 : ¬ d ≡ 0ℤ) ->
             let r = mod' n d n0 in let q = div' n d n0 in 
             ∣ r ∣ ≤ ∣ d ∣ / 2
euc-rank' n (+_ zero) n0 with n0 refl
... | ()
euc-rank' n d@(+[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2
... | yes pr = pr 
... | no ¬p =  claim 
  where
    r = + (n mod d) - d

    d≠0 : ¬ ∣ d ∣ ≡ 0
    d≠0 = λ () 
    
    -- We follow the steps to show ∣ r ∣ ≤ ∣ d ∣ / 2, in the current case, i.e. ∣
    -- n % d - d ∣ ≤ d / 2. We follows the steps below:
    -- 1) d / 2 < n % d
    -- 2) d / 2 - d < n % d - d
    -- 3) n % d - d < 0, hence d / 2 - d < n % d - d < 0
    -- 4) ∣ d / 2 - d ∣ > ∣ n % d - d ∣
    -- 5)  d / 2 - d ≡ - d / 2 or d / 2 - d  ≡ - (d / 2 + 1)
    -- 6) ∣ d / 2 - d ∣ ≡ d / 2 or ∣ d / 2 - d ∣ ≡ d / 2 + 1
    -- 7) d / 2 > ∣ n % d - d ∣ or d / 2 + 1 > ∣ n % d - d ∣
    -- 8) d / 2 ≥ ∣ n % d - d ∣

    -- By negate ¬p, we can show ∣ d ∣ / 2 < n mod d.
    -- By negation of ¬p (we are using the decidable order).
    open import Relation.Binary using (tri< ; tri≈ ; tri>)
    step1 : ∣ d ∣ / 2 < n mod d
    step1 with NatP.<-cmp (n mod d) (∣ d ∣ / 2)
    ... | tri< a ¬b ¬c = ⊥-elim (¬p (NatP.<⇒≤ a))  
    ... | tri≈ ¬a b ¬c = ⊥-elim (¬p (NatP.≤-reflexive b))  
    ... | tri> ¬a ¬b c = c
      where
        notle : ¬ (n mod d ≤ ∣ d ∣ / 2)
        notle = ¬p

    -- Step 2. ∣ d ∣ / 2 - ∣ d ∣ < n mod d - ∣ d ∣. Subtracting ∣ d ∣
    -- from both sides of step1 preserves the inequality.
    step2 : + (∣ d ∣ / 2) - + ∣ d ∣ < + (n mod d) - + ∣ d ∣
    step2 = IntP.+-monoʳ-< (- (+ ∣ d ∣)) (+<+ step1)

    -- Step 3. n mod d - ∣ d ∣ < 0

    -- Some auxillary. 
    n-n=0 : ∀ {n} -> n - n ≡ 0ℤ
    n-n=0 {n} = IntP.+-inverseʳ n

    step3 : + (n mod d) - (+ ∣ d ∣) < 0ℤ
    step3 rewrite (sym (n-n=0 {+ ∣ d ∣})) = r-d<d-d
      where
        -- n mod d < ∣ d ∣, by Euclidean property of integers.
        r<∣d∣ : + (n mod d) < + ∣ d ∣
        r<∣d∣ = +<+ (n%d<d n d)

        -- Substract ∣ d ∣ on both sides of n mod d < ∣ d ∣.
        r-d<d-d : + (n mod d) - (+ ∣ d ∣) < (+ ∣ d ∣) - (+ ∣ d ∣)
        r-d<d-d = IntP.+-monoʳ-< (- + ∣ d ∣) r<∣d∣

    -- Step 4. ∣ d / 2 - d ∣ > ∣ n % d - d ∣. By 2, we have
    --  d / 2 - d  <  n % d - d < 0. By taking absolute values, we show
    -- ∣ d / 2 - d ∣ > ∣ n % d - d ∣.

    -- Some lemmas about take absolute value of negative and nonpositive
    -- numbers.
    lemma-∣neg∣ : ∀ {a : ℤ} -> a < 0ℤ -> + ∣ a ∣ ≡ - a
    lemma-∣neg∣ -<+ = refl

    lemma-∣non-pos∣ : ∀ {a : ℤ} -> a ≤ 0ℤ -> + ∣ a ∣ ≡ - a
    lemma-∣non-pos∣ {.(-[1+ _ ])} -≤+ = refl
    lemma-∣non-pos∣ {.(+ zero)} (+≤+ z≤n) = refl

    -- The injection of natural numbers into integers reflect order.
    lemma-inj-reflect-ord : ∀ {a b} -> + a < + b -> a < b 
    lemma-inj-reflect-ord (+<+ m<n) = m<n

    lemma-inj-reflect-ord' : ∀ {a b} -> + a ≤ + b -> a ≤ b 
    lemma-inj-reflect-ord' (+≤+ m<n) = m<n

    -- Taking absolute value on both sides of a strict inequality of
    -- negative numbers (can relax this to non-positive numbers)
    -- reverses the order.
    lemma-∣neg<neg∣ : ∀ {a b} -> a < 0ℤ -> b < a -> ∣ a ∣ < ∣ b ∣
    lemma-∣neg<neg∣ {a} {b} a<0 b<a = lemma-inj-reflect-ord claim where
      0<b : b < 0ℤ
      0<b = IntP.<-trans b<a a<0
      claim : (+ ∣ a ∣) < (+ ∣ b ∣)
      claim = begin-strict
        + ∣ a ∣              ≡⟨ lemma-∣neg∣ {a} a<0  ⟩
        - a                 <⟨ IntP.neg-mono-< b<a  ⟩
        - b                 ≡⟨ sym (lemma-∣neg∣ 0<b)  ⟩
        + ∣ b ∣  ∎
          where open IntP.≤-Reasoning

    -- Goal step4 achieved.
    step4 : ∣ + (n mod d) - d ∣ < ∣ + (∣ d ∣ / 2) - d ∣ 
    step4 = lemma-∣neg<neg∣ step3 step2

    -- Step 5. d / 2 - d ≡ - d / 2 or d / 2 - d ≡ - (d / 2 + 1)

    -- Natural number version of Step 5.  
    step5-nat : ∣ d ∣ / 2 + ∣ d ∣ / 2 ≡ ∣ d ∣ ⊎ suc (∣ d ∣  / 2 + ∣ d ∣  / 2) ≡ ∣ d ∣
    step5-nat = lemma-div-by-2 ∣ d ∣ 
      where
        -- An easy and useful fact.
        *2+ : ∀ {a} -> a * 2 ≡ a + a
        *2+ {zero} = refl
        *2+ {suc a} rewrite *2+ {a} | NatP.+-comm a (suc a) = refl

        -- Either d / 2 + d / 2 ≡ d or d / 2 + d / 2 + 1 ≡ d. 
        lemma-div-by-2 : ∀ d -> let hd = d / 2 in
                hd + hd ≡ d ⊎ suc (hd + hd) ≡ d 
        lemma-div-by-2 d with d / 2 | d % 2 | NatESR.euc-eq d 2 (λ { ()}) | NatESR.euc-rank d 2 (λ { ()})
        ... | hd | zero | proj₁₁ | pr rewrite *2+ {hd} = inj₁ (sym proj₁₁)
        ... | hd | suc zero | proj₁₁ | pr  rewrite *2+ {hd} = inj₂ (sym proj₁₁)
        ... | hd | suc (suc r₁) | proj₁₁ | pr =  ⊥-elim ((c1 r₁) pr )
          where
            c1  : ∀ a -> ¬ (suc (suc (suc a)) ≤ 2)
            c1 a = λ { (s≤s (s≤s ()))} 

    -- Next we need inject naturals to integers. We do the two
    -- identities separately.

    -- Step 5a. If (d / 2) + (d / 2) ≡ d, we show d / 2 - d ≡ - d / 2.
    step5a : ∀ d -> (d / 2) + (d / 2) ≡ d -> let -_ = λ x -> - (+ x) in
               + (d / 2) - (+ d) ≡ - (d / 2)
    step5a d hyp = sym claim4
      where
        open PE.≡-Reasoning
        claim : + (d / 2 + d / 2)  ≡  + d
        claim = cong +_ hyp

        claim2 : + (d / 2)  +  + (d / 2) ≡  + d
        claim2 = begin
          + (d / 2)  +  + (d / 2) ≡⟨ IntP.pos-+-commute (d / 2) (d / 2) ⟩
          + (d / 2 + d / 2) ≡⟨ cong +_ hyp ⟩
          + d ∎

        claim3 :  + (d / 2)  ≡  + d - + (d / 2)
        claim3 = begin
          + (d / 2)   ≡⟨ (solve 1 (λ a -> a := a :+ a :- a) refl) (+ (d / 2))  ⟩
          + (d / 2) +  + (d / 2) - + (d / 2) ≡⟨ cong (_- + (d / 2)) claim2 ⟩
          + d - + (d / 2) ∎
            where open +-*-Solver

        claim4 : let -_ = λ x -> - (+ x) in
                 - (d / 2)  ≡  + (d / 2) - + d
        claim4 =  begin
          - (+ (d / 2))   ≡⟨ cong -_ claim3 ⟩ 
          - (+ d - + (d / 2)) ≡⟨ (solve 2 (λ a b -> :- (a :- b) := b :- a) refl) (+ d) (+ (d / 2)) ⟩
          + (d / 2) - + d ∎
            where open +-*-Solver

    -- Step 5b. If (d / 2) + (d / 2) + 1 ≡ d, we show d / 2 - d ≡ - (d
    -- / 2 + 1). (Note that we change the sign of the equality)
    step5b : ∀ d -> suc ((d / 2) + (d / 2)) ≡ d -> let -_ = λ x -> - (+ x) in
              (+ d) - + (d / 2) ≡ + (d / 2) + 1ℤ
    step5b d hyp = begin
          + d - + (d / 2)  ≡⟨ cong (λ x → + x - + (d / 2)) (sym hyp) ⟩ 
          + (suc (d / 2 + d / 2))  - + (d / 2) ≡⟨ refl ⟩
          + (1 + (d / 2 + d / 2))  - + (d / 2) ≡⟨ cong (_- + (d / 2)) (IntP.pos-+-commute 1 (d / 2 + d / 2)) ⟩
          + 1 + + (d / 2 + d / 2) - + (d / 2) ≡⟨ cong (λ x → + 1 + x - + (d / 2)) (IntP.pos-+-commute (d / 2) (d / 2)) ⟩
          + 1 +  + (d / 2) + + (d / 2) - + (d / 2) ≡⟨ solve 1 (λ x → (con 1ℤ) :+ (x :+ x) :- x := x :+ con 1ℤ) refl (+ (d / 2)) ⟩
          + (d / 2) + 1ℤ ∎
            where
              open +-*-Solver
              open PE.≡-Reasoning

    -- Goal 5. 
    step5 : let -_ = λ x -> - (+ x) in
        + (∣ d ∣ / 2) - d ≡ - (∣ d ∣ / 2) ⊎ d - + (∣ d ∣ / 2) ≡ + (∣ d ∣ / 2) + 1ℤ
    step5 with step5-nat
    ... | inj₁ x = inj₁ (step5a ∣ d ∣ x)
    ... | inj₂ y = inj₂ (step5b ∣ d ∣ y)


    -- Step 6. ∣ d / 2 - d ∣ ≡ d / 2 or ∣ d / 2 - d ∣ ≡ d / 2 + 1
    step6 : let -_ = λ x -> - (+ x) in
       ∣ + (∣ d ∣ / 2) - d ∣ ≡ ∣ d ∣ / 2 ⊎ ∣ d - + (∣ d ∣ / 2) ∣ ≡ ∣ d ∣ / 2 + 1
    step6 with step5
    ... | inj₁ x rewrite x = inj₁ (trans ∣-d/2∣≡∣d/2∣ ∣d/2∣≡d/2)
      where
        ∣-d/2∣≡∣d/2∣ : ∣ - (+ (∣ d ∣ / 2)) ∣ ≡ ∣ + (∣ d ∣ / 2) ∣
        ∣-d/2∣≡∣d/2∣ = IntP.∣-i∣≡∣i∣ (+ (∣ d ∣ / 2))
        ∣d/2∣≡d/2 : ∣ + (∣ d ∣ / 2) ∣ ≡ (∣ d ∣ / 2)
        ∣d/2∣≡d/2 = refl
    ... | inj₂ y rewrite y = inj₂ claim
      where
        claim : ∣ + (∣ d ∣ / 2) + 1ℤ ∣ ≡ ∣ d ∣ / 2 + 1
        claim = begin
          ∣ + (∣ d ∣ / 2) + 1ℤ ∣ ≡⟨ refl ⟩ 
          ∣ + ((∣ d ∣ / 2) + 1) ∣ ≡⟨ refl ⟩ 
          ∣ d ∣ / 2  + 1 ∎
            where
              open PE.≡-Reasoning

    -- Step 7. d / 2 > ∣ n % d - d ∣ or d / 2 + 1 > ∣ n % d - d ∣
    step7 : ∣ + (n mod d) - d ∣ < ∣ d ∣ / 2 ⊎ ∣ + (n mod d) - d ∣ < ∣ d ∣ / 2 + 1
    step7 with step6
    ... | inj₁ x = inj₁ claim
      where
        claim : ∣ + (n mod d) - d ∣ < ∣ d ∣ / 2
        claim = begin-strict
          ∣ + (n mod d) - d ∣ <⟨ step4 ⟩ 
          ∣ + (∣ d ∣ / 2) - d ∣ ≡⟨ x ⟩ 
          ∣ d ∣ / 2 ∎
            where
              open NatP.≤-Reasoning
    ... | inj₂ y = inj₂ claim
      where
        claim : ∣ + (n mod d) - d ∣ < ∣ d ∣ / 2 + 1
        claim = begin-strict
          ∣ + (n mod d) - d ∣ <⟨ step4 ⟩ 
          ∣ + (∣ d ∣ / 2) - d ∣ ≡⟨ IntP.∣i-j∣≡∣j-i∣ (+ (∣ d ∣ / 2)) d ⟩ 
          ∣ d - + (∣ d ∣ / 2) ∣ ≡⟨ y ⟩ 
          ∣ d ∣ / 2 + 1 ∎
            where
              open NatP.≤-Reasoning

    -- Step 8. d / 2 ≥ ∣ n % d - d ∣
    step8 : ∣ + (n mod d) - d ∣ ≤ ∣ d ∣ / 2
    step8 with step7
    ... | inj₁ x = NatP.<⇒≤ x
    ... | inj₂ y = m<sucn⇒m≤n claim
      where
        m<sucn⇒m≤n : ∀ {m n : ℕ} → m < suc n → m ≤ n
        m<sucn⇒m≤n (s≤s le) = le

        lemma-+1 : ∀ {a : ℕ} -> a + 1 ≡ suc a 
        lemma-+1 {zero} = refl
        lemma-+1 {suc a} = cong suc (lemma-+1 {a})

        claim : ∣ + (n mod d) - d ∣ < suc (∣ d ∣ / 2)
        claim = begin-strict
          ∣ + (n mod d) - d ∣ <⟨ y ⟩ 
          ∣ d ∣ / 2 + 1 ≡⟨ lemma-+1 ⟩ 
          suc (∣ d ∣ / 2) ∎
            where
              open NatP.≤-Reasoning
    
    claim : ∣ r ∣ ≤ ∣ d ∣ / 2
    claim = step8

-- This case is solved by recursive call with argument n and - d. 
euc-rank' n d@(-[1+ e ]) n0 with n mod d ≤? ∣ d ∣ / 2 | euc-rank' n (+[1+ e ]) (λ {()}) 
... | yes pr | hyp  = pr 
... | no ¬p | hyp = hyp


-- We can relax the estimation.
euc-rank'' : ∀ (n d : ℤ) (n0 : ¬ d ≡ 0ℤ) ->
               let r = mod' n d n0 in let q = div' n d n0 in 
               ∣ r ∣ < ∣ d ∣
euc-rank'' n d n0 = let r = mod' n d n0 in let q = div' n d n0 in
             begin-strict
               ∣ r ∣ ≤⟨ euc-rank' n d n0 ⟩ 
               ∣ d ∣ / 2 <⟨ aux ∣ d ∣ ∣d∣≠0 ⟩ 
               ∣ d ∣ ∎
                 where
                   open NatP.≤-Reasoning
                   aux : ∀ n -> ¬ n ≡ 0 -> n / 2 < n
                   aux zero n0 with n0 refl
                   ... | ()
                   aux (suc n) n0 = NDM.m/n<m (suc n) 2 (s≤s (s≤s z≤n))
                   ∣d∣≠0 : ¬ ∣ d ∣ ≡ 0
                   ∣d∣≠0 x = n0 (IntP.∣i∣≡0⇒i≡0 x)  
    

-- ----------------------------------------------------------------------
-- Alternative Euclidean Structure

-- The newly defined div' and mod' together with euc-eq' and
-- euc-rank'' make ℤ an Euclidean Domain with more precise estimate on
-- the rank of the reminder.

open import Integer.EucDomain
  using (+-*-isEuclideanDomain ; +-*-euclideanDomain)
import EuclideanDomain
open   EuclideanDomain.Bundles

-- We update the old Euclidean structure in EucDomain.
+-*-isEuclideanDomain' = record +-*-isEuclideanDomain
                         { div = div'
                         ; mod = mod'
                         ; euc-eq = euc-eq'
                         ; euc-rank = euc-rank''
                         }

-- Bundle.
+-*-euclideanDomain' : EuclideanDomainBundle _ _
+-*-euclideanDomain' = record
  { isEuclideanDomain = +-*-isEuclideanDomain'
  }


-- ----------------------------------------------------------------------
-- Make a new instance for DivMod ℤ

-- We use the newly defined div and mod function.
instance
  new-DMℤ : DivMod ℤ
  new-DMℤ .NZT = NZTℤ
  new-DMℤ ._/_ n d@(+[1+ n₁ ]) = div' n d λ {()} 
  new-DMℤ ._/_ n d@(-[1+ n₁ ]) = div' n d λ {()} 
  new-DMℤ ._%_ n d@(+[1+ n₁ ]) = mod' n d λ {()} 
  new-DMℤ ._%_ n d@(-[1+ n₁ ]) = mod' n d λ {()} 

