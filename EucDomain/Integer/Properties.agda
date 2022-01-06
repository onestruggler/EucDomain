-- Some extra properties of integers.

{-# OPTIONS --without-K --safe #-}

module Integer.Properties where

-- imports from stdlib.
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_ ; refl ; sym ; cong ; trans ; cong₂)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product as P using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Nat as Nat using (ℕ ; suc ; zero ; z≤n)
import Data.Nat.Solver as NS
open import Data.Integer as Int
  using (ℤ ; ∣_∣ ; +_ ; +[1+_] ; -[1+_] ; 1ℤ ; +<+ ; -<- ; -≤- ; -<+ ; -≤+ ; +≤+ ; 0ℤ ; NonNegative ; +0)
import Data.Integer.Properties as IntP
open import Function

-- imports from local.
open import Instances

-- Triangle equality.
tri-eq : ∀ (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative b}} -> ∣ a + b ∣ ≡ ∣ a ∣ + ∣ b ∣
tri-eq (+_ a) (+_ b) = begin
  ∣ + a + + b ∣ ≡⟨ refl ⟩ 
  ∣ + (a + b) ∣ ≡⟨ refl ⟩
  a + b        ≡⟨ refl ⟩
  ∣ + a ∣ + ∣ + b ∣ ∎
    where
      open PE.≡-Reasoning

-- For all a, a * a is always non-negative.
a*a=+b : ∀ a -> ∃ λ b → a * a ≡ + b
a*a=+b (+_ a) = (a * a) , IntP.pos-distrib-* a a
a*a=+b (-[1+_] a) = suc a * suc a , refl

0≤a*a : ∀ {a} → 0ℤ ≤ a * a 
0≤a*a {a} rewrite proj₂ $ a*a=+b a = +≤+ Nat.z≤n 


-- For non-zero natrual number a, a * a is always positive.
a*a-pos : ∀ (a : ℕ) .{{_ : Nat.NonZero a}} -> ∃ λ n → a * a ≡ suc n
a*a-pos (suc b) = b * b + 2 * b , claim
  where
    claim : suc b * suc b ≡ suc (b * b + 2 * b)
    claim = 
      begin
          suc b * suc b   ≡⟨ refl ⟩ 
      (1 + b) * (1 + b)   ≡⟨ solve 1 (λ b → (con 1 :+ b) :* (con 1 :+ b) := con 1 :+ (b :* b :+ con 2 :* b)) refl b ⟩ 
      1 + (b * b + 2 * b)  ≡⟨ refl ⟩ 
      suc (b * b + 2 * b) ∎
        where
          open NS.+-*-Solver
          open PE.≡-Reasoning

a*a-pos' : ∀ (a : ℤ) .{{_ : NonZero a}} -> ∃ λ n → a * a ≡ + (suc n)
a*a-pos' +[1+ n ] rewrite proj₂ $ a*a-pos (suc n) = (proj₁ $ a*a-pos (suc n)) , refl
a*a-pos' -[1+ n ] rewrite proj₂ $ a*a-pos (suc n) = (proj₁ $ a*a-pos (suc n)) , refl

-- For an non-zero integer a, ∣ a * a ∣ is always positive.
∣a*a∣-pos : ∀ (a : ℤ) .{{_ : NonZero a}} -> ∃ λ n → ∣ a * a ∣ ≡ suc n
∣a*a∣-pos (+ (suc b)) = b * b + 2 * b , claim
  where
    claim : suc b * suc b ≡ suc (b * b + 2 * b)
    claim = proj₂ $ a*a-pos (suc b)
∣a*a∣-pos (-[1+_] b) = b * b + 2 * b , claim
  where
    claim : suc b * suc b ≡ suc (b * b + 2 * b)
    claim = proj₂ $ a*a-pos (suc b)

+∣a*a∣=a*a : ∀ (a : ℤ) -> + ∣ a * a ∣ ≡ a * a 
+∣a*a∣=a*a a = IntP.0≤i⇒+∣i∣≡i (0≤a*a {a}) 

pos : ∀ {a : ℤ} -> ¬ a ≡ 0ℤ -> 0ℤ < a * a 
pos {+_ zero} n0 with n0 refl
... | ()
pos {a@(+[1+ n ])} n0 rewrite proj₂ $ a*a-pos' a = +<+ (Nat.s≤s Nat.z≤n)
pos {a@(-[1+ n ])} n0 rewrite proj₂ $ a*a-pos' a = +<+ (Nat.s≤s Nat.z≤n)

pos' : ∀ {a} -> 0ℤ < a -> Nat.NonZero ∣ a ∣
pos' {(+_ zero)} (+<+ ())
pos' {+[1+ n ]} l = record { nonZero = _ }


-- ∣ a * a + b * b ∣ is not zero if one of a and b is.
∣aa+bb∣-nonzero : ∀ a b -> ¬ a ≡ 0ℤ ⊎ ¬ b ≡ 0ℤ -> Nat.NonZero ∣ a * a + b * b ∣
∣aa+bb∣-nonzero a b (inj₁ x) = pos' (IntP.+-mono-<-≤ (pos x) (0≤a*a {b}))
∣aa+bb∣-nonzero a b (inj₂ y) = pos' (IntP.+-mono-≤-< (0≤a*a {a}) (pos y))


-- ----------------------------------------------------------------------
-- Properties of aa + bb

-- A special case of tri-eq. 
tri-eq' : ∀ a b -> ∣ a * a + b * b ∣ ≡ ∣ a * a ∣ + ∣ b * b ∣
tri-eq' a b = begin
      let (sa , sae) = (a*a=+b a) in let (sb , sbe) = a*a=+b b in
       ∣ a * a + b * b ∣  ≡⟨ cong (λ x → ∣ x ∣) (cong₂ _+_ sae sbe) ⟩
       ∣ + sa + + sb ∣  ≡⟨ (tri-eq (+ sa) (+ sb)) ⟩
       ∣ + sa ∣ + ∣ + sb ∣  ≡⟨ cong₂ _+_ (cong ∣_∣ (sym sae)) (cong ∣_∣ (sym sbe)) ⟩
       ∣ a * a ∣ + ∣ b * b ∣ ∎
        where
          open PE.≡-Reasoning


-- A property of a pair of integers.
a=0×b=0⇒aa+bb=0 : ∀ {a b : ℤ} -> a ≡ 0ℤ × b ≡ 0ℤ -> a * a + b * b ≡ 0ℤ
a=0×b=0⇒aa+bb=0 {.0ℤ} {.0ℤ} (refl , refl) = refl

aa+bb=0⇒a=0×b=0 : ∀ {a b : ℤ} -> a * a + b * b ≡ 0ℤ -> a ≡ 0ℤ × b ≡ 0ℤ
aa+bb=0⇒a=0×b=0 {a} {b} eq = P.map x^2=0⇒x=0 x^2=0⇒x=0 $ z+z (0≤a*a {a}) (0≤a*a {b}) eq 
  where
    z+z : ∀ {x y} -> 0ℤ ≤ x -> 0ℤ ≤ y -> x + y ≡ 0ℤ -> x ≡ 0ℤ × y ≡ 0ℤ
    z+z {.+0} {.(+ _)} (+≤+ {n = zero} z≤n) (+≤+ z≤n) x+y=0 = (refl , x+y=0)
    z+z {.(+[1+ n ])} {.+0} (+≤+ {n = ℕ.suc n} z≤n) (+≤+ {n = zero} m≤n) ()
    z+z {.(+[1+ n ])} {.(+[1+ n₁ ])} (+≤+ {n = ℕ.suc n} z≤n) (+≤+ {n = ℕ.suc n₁} m≤n) ()

    x^2=0⇒x=0 : ∀ {x} -> x * x ≡ 0ℤ -> x ≡ 0ℤ
    x^2=0⇒x=0 {+_ zero} eq = refl
