-- This file gives the definition of Gaussian Integers, the addition
-- and multiplication on them, and shows that they form a commutative
-- ring, and other properties. All the proofs are straightforward.

{-# OPTIONS --without-K --safe  #-}

module GauInt.Properties where

-- imports from local.
open import GauInt.Instances
open import Instances
open import GauInt.Base using (𝔾 ; _+_i ; _ᶜ ; Re ; Im ; _+0i ; _+0i')
open import Integer.Properties

-- imports from stdlib and Agda.
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (DecidableEquality ; Setoid ; DecSetoid)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Nat as Nat using (ℕ; suc; zero)
import Data.Nat.Properties as NatP
open import Data.Integer.Properties as IntP
  using (+-assoc ; +-identityˡ ; +-identityʳ ; *-identityˡ ; +-inverseˡ ; +-inverseʳ ; +-comm ; 0≤i⇒+∣i∣≡i ; +-mono-≤ ; +-mono-<-≤ ; +-mono-≤-<)
open import Data.Integer as Int
  using (ℤ ; +_ ; NonNegative ; -[1+_] ; +[1+_] ; +≤+ ; +<+ ; ∣_∣ ; 0ℤ)
import Data.Integer.Solver as IS
open IS.+-*-Solver


open import Algebra.Bundles as B
import Algebra.Morphism as Morphism
open import Algebra.Structures {A = 𝔾} _≡_
open import Function.Base using (_$_)

module 𝔾toℕ = Morphism.Definitions 𝔾 ℕ _≡_
module ℕto𝔾 = Morphism.Definitions ℕ 𝔾 _≡_

-- ----------------------------------------------------------------------
-- Equality

-- Injections are injective.
+0i'-injective : ∀ {a b} -> a +0i' ≡ b +0i' → a ≡ b
+0i'-injective refl = refl

+0i-injective : ∀ {m n} -> m +0i ≡ n +0i → m ≡ n
+0i-injective refl = refl

-- Decidable equality on 𝔾.
infix 4 _≟_
_≟_ : DecidableEquality 𝔾
_≟_ x@(a + b i) y@(c + d i) with  a Int.≟ c | b Int.≟ d
... | yes p  | yes q = yes (cong₂ _+_i p q)
... | yes p  | no ¬q = no (λ { refl → ¬q refl})
... | no ¬p  | hyp = no (λ { refl → ¬p refl})


≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid 𝔾

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_


-- ----------------------------------------------------------------------
-- Properties of _+_

-- Associativity of addition. 
assoc-+ : ∀ (x y z : 𝔾) -> ((x + y) + z) ≡ (x + (y + z))
assoc-+ x@(a + b i) y@(c + d i) z@(e + f i) = begin
  (((a + b i) + (c + d i)) + (e + f i)) ≡⟨ refl ⟩
  ((a + c + e) + (b + d + f) i) ≡⟨ cong₂ _+_i (+-assoc a c e) (+-assoc b d f) ⟩
  ((a + (c + e)) + (b + (d + f)) i) ≡⟨ refl ⟩
  (x + (y + z)) ∎

-- Left additive identity.
leftId-+ : ∀ (x : 𝔾) -> 0# + x ≡ x
leftId-+ x@(a + b i) = begin
  (0# + 0# i) + (a + b i) ≡⟨ refl ⟩
  -- cannot parse if remove the outer layer parenthese.
  ((0# + a) + (0# + b) i) ≡⟨ cong₂  _+_i (+-identityˡ a) (+-identityˡ b) ⟩
  (a + b i) ∎   

-- Right additive identity.
rightId-+ : ∀ (x : 𝔾) -> (x + 0#) ≡ x
rightId-+ x@(a + b i) = begin
  (a + b i) + (0# + 0# i)  ≡⟨ refl ⟩
  ((a + 0#) + (b + 0#) i) ≡⟨ cong₂  _+_i (+-identityʳ a) (+-identityʳ b) ⟩
  (a + b i) ∎   

-- Left additive inverse. 
leftInv-+ : ∀ (x : 𝔾) -> (- x) + x ≡ 0#
leftInv-+ x@(a + b i) = cong₂ _+_i (+-inverseˡ a) (+-inverseˡ b) 

-- Right additive inverse. 
rightInv-+ : ∀ (x : 𝔾) -> x + (- x) ≡ 0#
rightInv-+ x@(a + b i) = cong₂ _+_i (+-inverseʳ a) (+-inverseʳ b)

-- Addition is commutative. 
comm-+ : (x y : 𝔾) → (x + y) ≡ (y + x)
comm-+ x@(a + b i) y@(c + d i) = cong₂ _+_i (+-comm a c) (+-comm b d) 

-- ----------------------------------------------------------------------
-- Structures for addition 

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = assoc-+
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm        = comm-+
  }

+-0-isMonoid : IsMonoid _+_ 0#
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = leftId-+ , rightId-+ 
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0#
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = comm-+
  }

+-0-isGroup : IsGroup _+_ 0# (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = leftInv-+ , rightInv-+ 
  ; ⁻¹-cong  = cong (-_)
  }

+-isAbelianGroup : IsAbelianGroup _+_ 0# (-_)
+-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = comm-+
  }

-- ----------------------------------------------------------------------
-- Bundles for addition 

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-isAbelianGroup
  }


-- ----------------------------------------------------------------------
-- Properties of multiplication 

-- Associativity of multiplication.
assoc-* : ∀ (x y z : 𝔾) -> ((x * y) * z) ≡ (x * (y * z))
assoc-* x@(a + b i) y@(c + d i) z@(e + f i) = begin
  (((a + b i) * (c + d i)) * (e + f i)) ≡⟨ refl ⟩
  ((a * c - b * d) + (a * d + b * c) i)  * (e + f i) ≡⟨ refl ⟩
  ((a * c - b * d) * e - (a * d + b * c) * f) + ((a * c - b * d) * f + (a * d + b * c) * e) i ≡⟨ cong₂ _+_i (let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 6 (\ a b c d e f -> (((a * c) - (b * d)) * e) - (((a * d) + (b * c)) * f) := (a * ((c * e) - (d * f))) - (b * ((c * f) + (d * e)))) refl a b c d e f)) ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in
   (solve 6 (\ a b c d e f -> (((a * c) - (b * d)) * f) + (((a * d) + (b * c)) * e) := (a * ((c * f) + (d * e))) + (b * ((c * e) - (d * f)))) refl a b c d e f))) ⟩
  ((a * (c * e - d * f) - b * (c * f + d * e) ) + (a * (c * f + d * e) + b * (c * e - d * f)) i ) ≡⟨ refl ⟩
  ((a + b i) * ((c * e - d * f) + (c * f + d * e) i) ) ≡⟨ refl ⟩
  (x * (y * z)) ∎ 

-- Left multiplicative identity.
leftId-* : ∀ (x : 𝔾) -> (1# * x) ≡ x
leftId-* x@(a + b i) = begin
  (1# + 0# i) * (a + b i) ≡⟨ refl ⟩
  ((1# * a - 0# * b) + (1# * b + 0# * a) i) ≡⟨ cong₂ _+_i (let _*_ = _:*_ in let _-_ = _:-_ in (solve 2 (\ a b -> (con 1# * a) - (con 0# * b) := con 1# * a) refl a b)) ( (let _*_ = _:*_ in let _+_ = _:+_ in (solve 2 (\ a b -> (con 1# * b) + (con 0# * a) := con 1# * b) refl a b)))  ⟩
  ((1# * a) + (1# * b) i) ≡⟨ cong₂ _+_i (*-identityˡ a) (*-identityˡ b)  ⟩
  (a + b i) ∎  

-- Right multiplicative identity.
rightId-* : ∀ (x : 𝔾) -> (x * 1#) ≡ x
rightId-* x@(a + b i) = begin
  (a + b i) * (1# + 0# i)  ≡⟨ refl ⟩
  (( a * 1# - b * 0#) + ( a * 0#  + b * 1# ) i) ≡⟨ cong₂ _+_i ((let _*_ = _:*_ in let _-_ = _:-_ in (solve 2 (\ a b -> (a * con 1# ) - (b * con 0# ) := con 1# * a) refl a b))) ((let _*_ = _:*_ in let _+_ = _:+_ in (solve 2 (\ a b -> (a * con 0#) + (b * con 1# )   := con 1# * b) refl a b)))   ⟩
  ((1# * a) + (1# * b) i) ≡⟨ cong₂ _+_i (*-identityˡ a) (*-identityˡ b)  ⟩
  (a + b i) ∎   

-- Zero leftly times any number is zero. 
leftZero : ∀ x -> (0# + 0# i) * x ≡ (0# + 0# i)
leftZero x@(a + b i)  = begin
  (0# + 0# i) * (a + b i) ≡⟨ refl ⟩
  (0#  * a - 0#  * b) +   (0#  * a - 0#  * b) i  ≡⟨ refl ⟩
  0# + 0# i ∎   

-- Zero rightly times any number is zero. 
rightZero : ∀ x -> x * (0# + 0# i) ≡ (0# + 0# i)
rightZero x@(a + b i)  = begin
  (a + b i) * (0# + 0# i)  ≡⟨ refl  ⟩
  (a * 0#  - b * 0# ) + (a * 0#  + b *  0# ) i  ≡⟨ cong₂ _+_i ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in  (solve 2 (\ a b -> (a * con 0#) - (b * con 0# ) := con 0#) refl a b))) ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in  (solve 2 (\ a b -> (a * con 0#) + (b * con 0# ) := con 0#) refl a b)))   ⟩
  0# + 0# i ∎   

-- Left multiplication is distributive over addition. 
*-DistributesOver-+ˡ : ∀ (x y z : 𝔾) -> (x * (y + z)) ≡ ((x * y) + (x * z))
*-DistributesOver-+ˡ x@(a + b i) y@(c + d i) z@(e + f i) = begin
  x * (y + z) ≡⟨ refl ⟩
  (a * (c + e) - b * (d + f) + (a * (d + f) + b * (c + e)) i) ≡⟨ cong₂ _+_i ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 6 (\ a b c d e f -> (a * (c + e)) - (b * (d + f) ) := ((a * c) - (b * d)) + ((a * e) - (b * f)) ) refl a b c d e f))) ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 6 (\ a b c d e f -> (a * (d + f)) + (b * (c + e) ) := ((a * d) + (b * c)) + ((a * f) + (b * e)) ) refl a b c d e f))) ⟩
  ((a * c - b * d)  + (a * e - b * f)) + ((a * d + b * c) + (a * f + b * e)) i ≡⟨ refl ⟩ 
  ((x * y) + (x * z)) ∎  

-- Right multiplication is distributive over addition. 
*-DistributesOver-+ʳ : ∀ (x y z : 𝔾) -> ((y + z) * x) ≡ (y * x) + (z * x)
*-DistributesOver-+ʳ x@(a + b i) y@(c + d i) z@(e + f i) = begin
  (y + z) * x ≡⟨ refl ⟩
  ((c + e) * a - (d + f) * b + ( (c + e) * b + (d + f) * a ) i) ≡⟨ cong₂ _+_i ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 6 (\ a b c d e f -> ((c + e) * a) - ((d + f) * b ) := ((c * a ) - (d * b)) + ((e * a) - (f * b )) ) refl a b c d e f))) ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 6 (\ a b c d e f -> ((c + e) * b) + ((d + f) * a ) := ((c * b ) + (d * a)) + ((e * b) + (f * a )) ) refl a b c d e f)))  ⟩
  ((c * a - d * b)  + (e * a - f * b)) + ((c * b + d * a ) + (e * b + f * a )) i ≡⟨ refl ⟩ 
  ((y * x) + (z * x)) ∎  


-- Multiplicaton is commutative. 
comm-* : ∀ (x y : 𝔾) -> x * y ≡ y * x
comm-* x@(a + b i) y@(c + d i) = begin
  x * y ≡⟨ refl ⟩
  (a * c - b * d) + (a * d + b * c) i ≡⟨ cong₂ _+_i ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in (solve 4 (\ a b c d -> (a * c) - (b * d) := (c * a ) - (d * b)) refl a b c d))) ((let _*_ = _:*_ in let _+_ = _:+_ in let _-_ = _:-_ in  (solve 4 (\ a b c d -> (a * d) + (b * c) := (c * b) + (d * a)) refl a b c d)))  ⟩
  (c * a - d * b) + (c * b + d * a) i ≡⟨ refl ⟩ 
  (y * x) ∎  


-- ----------------------------------------------------------------------
-- Structures for multiplication

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = assoc-*
  }

*-isCommutativeSemigroup : IsCommutativeSemigroup _*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm        = comm-*
  }

*-1-isMonoid : IsMonoid _*_ 1#
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = leftId-* , rightId-* 
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = comm-*
  }

-- ----------------------------------------------------------------------
-- Structures for multiplication and addition

+-*-isSemiring : IsSemiring _+_ _*_ 0# 1#
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-isMonoid = *-1-isMonoid
    ; distrib = *-DistributesOver-+ˡ , *-DistributesOver-+ʳ 
    }
  ; zero = leftZero , rightZero 
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0# 1#
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = comm-*
  }

+-*-isRing : IsRing _+_ _*_ -_ 0# 1#
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = *-DistributesOver-+ˡ , *-DistributesOver-+ʳ
  ; zero             = leftZero , rightZero
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = comm-*
  }

------------------------------------------------------------------------
-- Bundles for multiplication 

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- Bundles for multiplication and addition

+-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

+-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-ring : B.Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }


-- ----------------------------------------------------------------------
-- Properties of Re and Im

-- Re x + Im x i = x
Re+Im*i : ∀ {x} -> Re x + Im x i ≡ x
Re+Im*i {x + x₁ i} = refl

-- Re (y * y ᶜ) ≡ + rank y 
Re[yyᶜ]=rank : ∀ {y : 𝔾} -> Re (y * y ᶜ) ≡ + rank y 
Re[yyᶜ]=rank {y@(a + b i)} = sym $ begin
  + (rank y) ≡⟨ refl ⟩
  + (rank (a + b i)) ≡⟨ refl ⟩
  + ∣ a * a + b * b ∣ ≡⟨ cong +_ (tri-eq' a b) ⟩
  + (∣ a * a ∣ + ∣ b * b ∣) ≡⟨ refl ⟩
  + ∣ a * a ∣ + + ∣ b * b ∣ ≡⟨ cong₂ _+_ (+∣a*a∣=a*a a) (+∣a*a∣=a*a b) ⟩
  a * a + b * b ≡⟨ solve 2 (\ a b -> a :* a :+ b :* b := a :* a :- b :* (:- b)) refl a b ⟩
  a * a - b * (- b) ≡⟨ refl ⟩
  Re ((a * a - b * (- b)) + 0ℤ i) ≡⟨ refl ⟩
  Re ((a * a - b * (- b)) + (a * (- b) + b * a) i) ≡⟨ refl ⟩
  Re (y * y ᶜ) ∎

-- Im y * y ᶜ = 0
Im[yyᶜ]=0 : ∀ {y : 𝔾} -> Im (y * y ᶜ) ≡ 0#
Im[yyᶜ]=0 {y@(a + b i)} = begin
  Im (y * y ᶜ) ≡⟨ refl ⟩
  Im ((a * a - b * (- b)) + (a * (- b) + b * a) i) ≡⟨ refl ⟩
  a * (- b) + b * a ≡⟨ solve 2 (\ a b -> a :* (:- b) :+ b :* a := con 0#) refl a b ⟩
  0# ∎


-- ----------------------------------------------------------------------
-- Properties of conjugation

-- Conjugation is injective.
ᶜ-injective : ∀ {x} -> x ᶜ ≡ 0# -> x ≡ 0#
ᶜ-injective {+ 0 + + 0 i} eq = refl

-- y * y ᶜ = rank y
y*yᶜ=rank : ∀ {y : 𝔾} -> y * y ᶜ ≡ rank y +0i
y*yᶜ=rank {y@(a + b i)} = begin
  y * y ᶜ ≡⟨ sym $ Re+Im*i ⟩
  Re (y * y ᶜ) + Im (y * y ᶜ) i  ≡⟨ cong₂ _+_i (Re[yyᶜ]=rank {y}) (Im[yyᶜ]=0 {y})  ⟩
  + rank y + 0# i ∎


-- ----------------------------------------------------------------------
-- Properties of rank

-- rank on 𝔾 is homomorphic in multiplication.
rank-*-commute : 𝔾toℕ.Homomorphic₂ rank _*_ Nat._*_
rank-*-commute x@(a + b i) y@(c + d i) = claim
  where
    claim : rank (x * y) ≡ rank x * rank y
    claim = begin
      rank (x * y)  ≡⟨ refl ⟩ 
      rank ((a * c - b * d) + (a * d + b * c) i) ≡⟨ refl ⟩
      ∣ (a * c - b * d)^2 + (a * d + b * c)^2 ∣ ≡⟨ cong ∣_∣ (solve 4 (λ a b c d → (a :* c :- b :* d) :* (a :* c :- b :* d) :+ (a :* d :+ b :* c) :* (a :* d :+ b :* c) := (a :* a :+ b :* b) :* (c :* c :+ d :* d)) refl a b c d) ⟩
      ∣ (a ^2 + b ^2) * (c ^2 + d ^2) ∣ ≡⟨ IntP.abs-*-commute ((a ^2 + b ^2)) ((c ^2 + d ^2)) ⟩
      ∣ a ^2 + b ^2 ∣ * ∣ c ^2 + d ^2 ∣ ≡⟨ refl ⟩
      rank x * rank y ∎

rank=∣Re[y*yᶜ]∣ : ∀ (x : 𝔾) -> rank x ≡ ∣ Re (x * x ᶜ) ∣
rank=∣Re[y*yᶜ]∣ x@(a + b i) = begin
  rank (a + b i) ≡⟨ refl ⟩
  ∣ a * a + b * b ∣ ≡⟨ cong ∣_∣ (solve 2 (λ a b → a :* a :+ b :* b := a :* a :- b :* (:- b)) refl a b) ⟩
  ∣ a * a - b * (- b) ∣ ≡⟨ refl ⟩
  ∣ Re ((a * a - b * (- b)) + 0ℤ i) ∣ ≡⟨ refl ⟩
  ∣ Re ((a * a - b * (- b)) + (a * (- b) + b * a) i) ∣ ≡⟨ refl ⟩
  ∣ Re (x * x ᶜ) ∣  ∎

-- rank y + 0 i = y * y ᶜ
rank+0i=y*yᶜ : ∀ {y : 𝔾} -> (rank y) +0i ≡ y * y ᶜ 
rank+0i=y*yᶜ {y} = sym $ begin
  y * y ᶜ ≡⟨ sym $ Re+Im*i ⟩
  Re (y * y ᶜ) + Im (y * y ᶜ) i  ≡⟨ cong₂ _+_i (Re[yyᶜ]=rank {y}) (Im[yyᶜ]=0 {y})  ⟩
  + rank y + 0# i ∎

-- ----------------------------------------------------------------------
-- Injection preserves SemiRing Structure

+0i-+-commute : ℕto𝔾.Homomorphic₂ _+0i Nat._+_ _+_
+0i-+-commute a b = refl 

+0i-*-commute : ℕto𝔾.Homomorphic₂ _+0i Nat._*_ _*_
+0i-*-commute a b rewrite NatP.*-zeroˡ a | NatP.*-zeroˡ b | NatP.*-zeroʳ a | NatP.*-zeroʳ b | sym (IntP.pos-distrib-* a b) | IntP.+-identityʳ (+ a * + b) = refl

0+0i=0 : 0 +0i ≡ 0#
0+0i=0 = refl 

1+0i=1 : 1 +0i ≡ 1#
1+0i=1 = refl 


-- ----------------------------------------------------------------------
-- Properties of NonZero




