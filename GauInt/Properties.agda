-- This file gives the definition of Gaussian Integers, the addition
-- and multiplication on them, and shows that they form a commutative
-- ring, and other properties. All the proofs are straightforward.

{-# OPTIONS --without-K --safe  #-}

module GauInt.Properties where

-- imports from local.
open import GauInt.Instances
open import Instances hiding (i ; _≟_)
open import GauInt.Base using (𝔾 ; _+_i ; _ᶜ ; Re ; Im ; _+0i ; _+0i' ; 0𝔾)
open import Integer.Properties

-- imports from stdlib and Agda.
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (DecidableEquality ; Setoid ; DecSetoid ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Product using (proj₁; proj₂; _,_ ; _×_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂) renaming ([_,_]′ to ⊎-elim)
open import Data.Nat as Nat using (ℕ; suc; zero)
import Data.Nat.Properties as NatP
open import Data.Integer.Properties as IntP
  using (+-assoc ; +-identityˡ ; +-identityʳ ; *-identityˡ ; +-inverseˡ ; +-inverseʳ ; +-comm ; 0≤i⇒+∣i∣≡i ; +-mono-≤ ; +-mono-<-≤ ; +-mono-≤-<)
open import Data.Integer as Int
  using (ℤ ; +_ ; NonNegative ; -[1+_] ; +[1+_] ; +≤+ ; +<+ ; ∣_∣ ; 0ℤ ; +0)
import Data.Integer.Solver as IS
open IS.+-*-Solver

open import Algebra.Bundles as B
import Algebra.Morphism as Morphism
open import Algebra.Structures {A = 𝔾} _≡_
open import Function.Base using (_$_)
module 𝔾toℕ = Morphism.Definitions 𝔾 ℕ _≡_
module ℕto𝔾 = Morphism.Definitions ℕ 𝔾 _≡_


open import Algebra.Definitions (_≡_ {A = 𝔾}) using (AlmostLeftCancellative)


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
leftZero : ∀ (x : 𝔾) -> (0# + 0# i) * x ≡ (0# + 0# i)
leftZero x@(a + b i)  = begin
  (0# + 0# i) * (a + b i) ≡⟨ refl ⟩
  (0#  * a - 0#  * b) +   (0#  * a - 0#  * b) i  ≡⟨ refl ⟩
  0# + 0# i ∎   

-- Zero rightly times any number is zero. 
rightZero : ∀ (x : 𝔾) -> x * (0# + 0# i) ≡ (0# + 0# i)
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
    ; *-cong = cong₂ _*_
    ; *-assoc = assoc-*
    ; *-identity = leftId-* , rightId-* 
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
  ; *-cong = cong₂ _*_
  ; *-assoc =  assoc-*
  ; *-identity = leftId-* , rightId-* 
  ; distrib          = *-DistributesOver-+ˡ , *-DistributesOver-+ʳ
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
      ∣ (a ^2 + b ^2) * (c ^2 + d ^2) ∣ ≡⟨ IntP.abs-* ((a ^2 + b ^2)) ((c ^2 + d ^2)) ⟩
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
+0i-*-commute a b rewrite NatP.*-zeroˡ a | NatP.*-zeroˡ b | NatP.*-zeroʳ a | (IntP.pos-* a b) | IntP.+-identityʳ (+ a * + b) = refl

0+0i=0 : 0 +0i ≡ 0#
0+0i=0 = refl 

1+0i=1 : 1 +0i ≡ 1#
1+0i=1 = refl 



-- ----------------------------------------------------------------------
-- Domain Structrue on 𝔾 

-- Some auxillaries.

-- Zero is unique. 
unique0 : ∀ {a b} -> (a + b i) ≡ 0# -> a ≡ 0ℤ × b ≡ 0ℤ
unique0 {.+0} {.+0} refl = refl , refl

-- Conversely, if a + bi ≠ 0 then at least one of a and b is not zero.
unique0' : ∀ {a b} -> ¬ (a + b i) ≡ 0# -> ¬ a ≡ 0ℤ ⊎ ¬ b ≡ 0ℤ
unique0' {a@(+_ zero)} {b@(+_ zero)} neq with neq refl
... | ()
unique0' {+_ zero} {+[1+ n ]} neq = inj₂ (λ ())
unique0' {+_ zero} { -[1+_] n} neq = inj₂ (λ ())
unique0' {+[1+ n ]} {b} neq = inj₁ (λ ())
unique0' { -[1+_] n} {b} neq = inj₁ (λ ())


-- Make an equation onesided.
oneside : ∀ {a b : 𝔾} -> a ≡ b -> a - b ≡ 0#
oneside {a} {b} eq rewrite eq = rightInv-+ b 

-- Make an equation twosided.  
twoside : ∀ {a b : 𝔾} -> a - b ≡ 0# -> a ≡ b
twoside {a} {b} eq = sym $ -‿injective $ +-inverseʳ-unique a (- b) eq
  where
    open import Algebra.Properties.Ring +-*-ring

-- Make an equation twosided, ℤ version.
twosideℤ : ∀ {a b : ℤ} -> a - b ≡ 0# -> a ≡ b
twosideℤ {a} {b} eq = sym (PRI.-‿injective (PRI.+-inverseʳ-unique a (- b) eq ))
  where
    import Algebra.Properties.Ring IntP.+-*-ring as PRI


-- We show zero divisor is necessary zero (equivalent to left or right
-- cancellation in a commutative ring), which makes 𝔾 an integral
-- domain.
zero-divisor-is-zero :  ∀ {x y : 𝔾} -> x * y ≡ 0# -> ¬ x ≡ 0# -> y ≡ 0#
zero-divisor-is-zero {x@(a + b i)} {y@(c + d i)} eq neq = cong₂ _+_i (proj₁ step6) (proj₂ step6)
  where
    open ≡-Reasoning
    open IS.+-*-Solver
    -- 0 = x * y = (a * c - b * d) + (a * d + b * c) i, together with
    -- c + d i ≠ 0, we can derive a = 0 and b = 0, contradicting x ≠
    -- 0. The proof idea is:
    --
    -- step0 : a * c - b * d = 0 and a * d + b * c = 0
    -- step1 : a * c * c - b * d * c = 0
    -- step2 : a * d * d + b * c * d = 0
    -- s1,s2 ⇒ step1&2 : a * (c * c + d * d) = 0
    -- step3 : a * c * d - b * d * d = 0
    -- step4 : a * d * c + b * c * c = 0
    -- s3,s4 ⇒ step3&4 : b * (c * c + d * d) = 0
    -- one of a b nonzero ⇒ step5 : (c * c + d * d) = 0
    -- step5 ⇒ step6 : c = 0 and d = 0

    -- step0 : a * c - b * d = 0 and a * d + b * c = 0
    step0 : a * c - b * d ≡ 0# × a * d + b * c ≡ 0#
    step0 = unique0 eq
    
    -- step1 : a * c * c - b * d * c = 0
    step1 : a * c * c - b * d * c ≡ 0#
    step1 = begin
        a * c * c - b * d * c ≡⟨ solve 4 (\ a b c d -> a :* c :* c :- b :* d :* c := (a :* c :- b :* d) :* c) refl a b c d ⟩
        (a * c - b * d) * c ≡⟨ cong (_* c) (proj₁ step0) ⟩
        0ℤ * c ≡⟨ refl ⟩
        0ℤ ∎

    -- step2 : a * d * d + b * c * d = 0
    step2 : a * d * d + b * c * d ≡ 0#
    step2 = begin
        a * d * d + b * c * d ≡⟨ solve 4 (\ a b c d -> a :* d :* d :+ b :* c :* d := (a :* d :+ b :* c) :* d) refl a b c d ⟩
        (a * d + (b * c)) * d ≡⟨ cong (_* d) (proj₂ step0) ⟩
        0ℤ * d ≡⟨ refl ⟩
        0ℤ ∎ 

    -- c1,c2 ⇒ step1&2 : a * (c * c + d * d) = 0
    step1&2 : a * (c * c + d * d) ≡ 0#
    step1&2 = begin
      a * (c * c + d * d) ≡⟨ solve 4 (\ a b c d -> a :* (c :* c :+ d :* d) := (a :* c :* c :- b :* d :* c) :+ (a :* d :* d :+ b :* c :* d) ) refl a b c d ⟩
      (a * c * c - b * d * c) + (a * d * d + b * c * d) ≡⟨ cong₂ _+_ step1 step2 ⟩
      0# ∎ 

    -- step3 : a * c * d - b * d * d = 0
    step3 : a * c * d - b * d * d ≡ 0#
    step3 = begin
        a * c * d - b * d * d ≡⟨ solve 4 (\ a b c d -> a :* c :* d :- b :* d :* d := (a :* c :- b :* d) :* d) refl a b c d ⟩
        (a * c - b * d) * d ≡⟨ cong (_* d) (proj₁ step0) ⟩
        0ℤ * d ≡⟨ refl ⟩
        0ℤ ∎

    -- step4 : a * d * c + b * c * c = 0
    step4 : a * d * c + b * c * c ≡ 0#
    step4 = begin
        a * d * c + b * c * c ≡⟨ solve 4 (\ a b c d -> a :* d :* c :+ b :* c :* c := (a :* d :+ b :* c) :* c) refl a b c d ⟩
        (a * d + (b * c)) * c ≡⟨ cong (_* c) (proj₂ step0) ⟩
        0ℤ * c ≡⟨ refl ⟩
        0ℤ ∎ 

    -- s3,s4 ⇒ step3&4 : b * (c * c + d * d) = 0
    step3&4 : b * (c * c + d * d) ≡ 0#
    step3&4 = begin
      b * (c * c + d * d) ≡⟨ solve 4 (\ a b c d -> b :* (c :* c :+ d :* d) := :- (a :* c :* d :- b :* d :* d) :+ (a :* d :* c :+ b :* c :* c) ) refl a b c d ⟩
      - (a * c * d - b * d * d) + (a * d * c + b * c * c) ≡⟨ cong₂ (\x y -> (- x) + y) step3 step4 ⟩
      0# ∎

    -- one of a b nonzero ⇒ step5 : (c * c + d * d) = 0
    -- some auxillary lemma.
    aux : ∀ {a : ℤ} -> a * 0# ≡ 0#
    aux {a} rewrite IntP.*-comm a 0# = refl

    step1&2' : a * (c * c + d * d) ≡ a * 0#
    step1&2' rewrite aux {a} = step1&2
    
    step3&4' : b * (c * c + d * d) ≡ b * 0#
    step3&4' rewrite aux {b} = step3&4


    step5 : c * c + d * d ≡ 0#
    step5 = ⊎-elim (λ x₁ → IntP.*-cancelˡ-≡ a (c * c + d * d) 0# {{myins2 {a} {x₁}}} step1&2') (λ x₁ → IntP.*-cancelˡ-≡ b (c * c + d * d) 0# {{myins2 {b} {x₁}}} step3&4') (unique0' neq)
      where
        -- We need a translation from non-equality to NonZero predicate.
        open import Agda.Builtin.Unit
        myins2 : ∀ {x : ℤ} -> {n0 : ¬ x ≡ 0ℤ} -> NonZero x
        myins2 {+_ zero} {n0} with n0 refl
        ... | ()
        myins2 {+[1+ n ]} {n0} = record { nonZero = tt }
        myins2 { -[1+_] n} {n0} = record { nonZero = tt }

    -- step5 ⇒ step6 : c = 0 and d = 0
    step6 : c ≡ 0# × d ≡ 0#
    step6 = aa+bb=0⇒a=0×b=0 step5 


-- Almost left cancellative.
*-alc-𝔾 : AlmostLeftCancellative 0𝔾 _*_
*-alc-𝔾 x@(a + b i) y@(c + d i) z@(e + f i)  neq eq = y=z
  where
    onesided-eq : x * (y + (- z)) ≡ 0#
    onesided-eq = begin
      x * (y + (- z)) ≡⟨ *-DistributesOver-+ˡ x y (- z)  ⟩
      x * y + x * (- z) ≡⟨ refl ⟩ 
      x * y + (a + b i) * (- e + - f i) ≡⟨ cong (λ t → x * y + t) refl ⟩
      x * y + ((a * - e - b * - f ) + (a * - f + b * - e) i)  ≡⟨ cong (λ t → x * y + t) (cong₂ _+_i (solve 4 (\a e b f -> a :* :- e :- b :* :- f := :- (a :* e :- b :* f)) refl a e b f) (solve 4 (\a e b f -> a :* :- f :+ b :* :- e := :- (a :* f :+ b :* e)) refl a e b f)) ⟩
      x * y + (- (a * e - b * f) + - (a * f + b * e) i)  ≡⟨ cong (λ t → x * y + t) refl ⟩
      x * y + (- (x * z)) ≡⟨ oneside eq  ⟩
      0# ∎
        where
          open ≡-Reasoning
          open IS.+-*-Solver

    y-z=0 : (y + (- z)) ≡ 0#
    y-z=0 = zero-divisor-is-zero onesided-eq neq

    y=z : y ≡ z
    y=z = twoside y-z=0


-- Multiplication commutativity plus left cancellative implies 𝔾 is an
-- commutative Domain. Knowing this, we can show e.g.
y≠0⇒y*yᶜ≠0 : ∀ {y} -> ¬ y ≡ 0# -> ¬ y * y ᶜ ≡ 0#
y≠0⇒y*yᶜ≠0 {y} n0 eq  = ⊥-elim (n0' e0)
      where
        open import Data.Empty
        n0' : ¬ y ᶜ ≡ 0#
        n0' x with n0 (ᶜ-injective {y} x)
        ... | ()

        eq' : y * y ᶜ ≡ y * 0#
        eq' = begin 
          y * y ᶜ ≡⟨ eq ⟩
          0# ≡⟨ sym $ rightZero y ⟩
          y * 0# ∎
            where
              open IS.+-*-Solver
              open ≡-Reasoning

        e0 : y ᶜ ≡ 0#
        e0 = *-alc-𝔾 y (y ᶜ) 0# n0 eq'


y≠0#⇒rank≠0 : ∀ {y : 𝔾} -> ¬ y ≡ 0# -> ¬ rank y ≡ 0#
y≠0#⇒rank≠0 {y} n0 = rank≠0
  where
    open import Data.Empty
    y*yᶜ≠0 : ¬ y * y ᶜ ≡ 0#
    y*yᶜ≠0 = y≠0⇒y*yᶜ≠0 n0
    rank≠0 : ¬ rank y ≡ 0#
    rank≠0 e = ⊥-elim (y*yᶜ≠0 y*yᶜ=0) 
      where
        y*yᶜ=0 : y * y ᶜ ≡ 0#
        y*yᶜ=0 = begin 
          y * y ᶜ ≡⟨ sym $ Re+Im*i ⟩
          Re (y * y ᶜ) + Im (y * y ᶜ) i ≡⟨ cong₂ _+_i (Re[yyᶜ]=rank {y}) refl ⟩
          + rank y  + Im (y * y ᶜ) i ≡⟨ cong₂ _+_i (cong +_ e) (Im[yyᶜ]=0 {y}) ⟩
          0# ∎
            where
              open IS.+-*-Solver
              open ≡-Reasoning


rank=0⇒y=0 : ∀ {y : 𝔾} -> rank y ≡ 0# -> y ≡ 0# 
rank=0⇒y=0 {y@(a + b i)} eq0 = y=0
  where
    eq0' : a * a + b * b ≡ 0#
    eq0' = IntP.∣i∣≡0⇒i≡0 eq0
    s1 : a ≡ 0ℤ × b ≡ 0ℤ
    s1 = aa+bb=0⇒a=0×b=0 eq0'
    y=0 : y ≡ 0#
    y=0 with s1
    ... | fst , snd rewrite fst | snd = refl


rank≥1 : ∀ {y : 𝔾} -> ¬ y ≡ 0# -> 1# ≤ rank y
rank≥1 {y} n0 = aux (rank y) (y≠0#⇒rank≠0 {y} n0)
  where
    aux : ∀ (n : ℕ) -> ¬ n ≡ 0 -> 1 ≤ n
    aux zero n0' with n0' refl
    ... | ()
    aux (suc n) n0' = Nat.s≤s Nat.z≤n


ranky<1⇒y=0 : ∀ (y : 𝔾) -> rank y < 1# -> y ≡ 0#
ranky<1⇒y=0 y r = rank=0⇒y=0 {y} ranky=0
  where
    aux : ∀ (n : ℕ) -> n < 1 -> n ≡ 0
    aux .zero (Nat.s≤s Nat.z≤n) = refl

    ranky=0 : rank y ≡ 0
    ranky=0 = aux (rank y) r

   
-- ----------------------------------------------------------------------
-- Properties of NonZero




