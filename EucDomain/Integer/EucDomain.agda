-- Example, ℤ is an Euclidean Domain. Here all the properties needed
-- are already proved in Data.Integer.Properties. However, we will
-- prove there is another divmod pair such that the rank estimation
-- is more precise, see EucDomain2.agda.

{-# OPTIONS --without-K --safe #-}

module Integer.EucDomain where

  -- imports from stdlib.
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (refl ; _≡_)

  open import Data.Nat using (_<_)
  open import Data.Integer
    using (_+_ ; _*_ ; -_ ; ℤ ; 0ℤ ; 1ℤ ; ∣_∣ ; +[1+_] ; -[1+_] ; +_)
  open import Data.Integer.DivMod
    renaming (_div_ to _divℤ_; _mod_ to _modℤ_ ; n%d<d to euc-rankℤ; a≡a%n+[a/n]*n to euc-eqℤ)
  open import Data.Integer.Properties
    using (+-*-isCommutativeRing ; *-cancelˡ-≡)

  open import Algebra.Definitions (_≡_ {A = ℤ}) using (AlmostLeftCancellative)

  -- imports from local.
  import EuclideanDomain
  open EuclideanDomain.Structures (_≡_ {A = ℤ})
  open EuclideanDomain.Bundles


  -- You will notice the recurring pattern that I have to split on
  -- the divisor d, and use ¬ d ≡ 0ℤ to exclude the zero divisor
  -- case. And addtionally, I have to repeat similary codes
  -- twice. This is the price of the translation from ¬ a ≡ 0ℤ to
  -- NonZero a. I don't have a good way to avoid this. This become
  -- even more awkward when dealing with Gaussian integers since we
  -- have more constructor there (meaning more cases and more
  -- repeatitions).

  -- On the other hand, a translation from NonZero predicate to
  -- non-equaity ¬ d ≡ 0ℤ is quite easy. We will use this to define
  -- div and mod with instance predicate argument for 𝔾.

  -- I could use NonZero predicate in the definition of Euclidean
  -- Domain, but that will make the definition more complicated. Also
  -- the file "Algebra.Definition" using the same method as here to
  -- exclude zero, for example the definition of
  -- "AlmostLeftCancellative", so we also comply this convention.

  -- div with irrelevant instance argument replaced by non-equality
  -- argument.
  div : ∀ (n d : ℤ) -> ¬ d ≡ 0ℤ -> ℤ
  div n (+ 0) n0 with n0 refl
  ... | ()
  div n d@(+[1+ n₁ ]) n0 = n divℤ d 
  div n d@(-[1+_] n₁) n0 = n divℤ d

  -- mod with irrelevant instance argument replaced by non-equality
  -- argument. 
  mod : ∀ (n d : ℤ) -> ¬ d ≡ 0ℤ -> ℤ
  mod n (+ 0) n0 with n0 refl
  ... | ()
  mod n d@(+[1+ n₁ ]) n0 = + (n modℤ d)
  mod n d@(-[1+_] n₁) n0 = + (n modℤ d)

  -- Divident = reminder + quotient * divisor.
  euc-eq : ∀ (n d : ℤ) (n0 : ¬ d ≡ 0ℤ) ->
               let r = mod n d n0 in let q = div n d n0 in 
               n ≡ r + q * d 
  euc-eq n (+ 0) n0 with n0 refl
  ... | ()
  euc-eq n d@(+[1+ n₁ ]) n0 = euc-eqℤ n d 
  euc-eq n d@(-[1+_] n₁) n0 = euc-eqℤ n d 


  -- The rank of the reminder is strictly smaller than the rank of the
  -- divisor.
  euc-rank : ∀ (n d : ℤ) (n0 : ¬ d ≡ 0ℤ) ->
               let r = mod n d n0 in let q = div n d n0 in 
               ∣ r ∣ < ∣ d ∣ 
  euc-rank n (+ 0) n0 with n0 refl
  ... | ()
  euc-rank n d@(+[1+ n₁ ]) n0 = euc-rankℤ n d
  euc-rank n d@(-[1+_] n₁) n0 = euc-rankℤ n d


  -- Multiplication is left cancellative. 
  *-alc-ℤ : AlmostLeftCancellative 0ℤ _*_
  *-alc-ℤ {+ 0} j k n0 with n0 refl
  ... | ()
  *-alc-ℤ {i@(+[1+ n ])} j k n0 = *-cancelˡ-≡ i j k
  *-alc-ℤ { i@(-[1+ n ])} j k n0 = *-cancelˡ-≡ i j k

  -- ℤ is an Euclidean Domain. 
  +-*-isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0ℤ 1ℤ
  +-*-isEuclideanDomain = record
                            { isCommutativeRing = +-*-isCommutativeRing 
                            ; *-alc = *-alc-ℤ
                            ; div = div 
                            ; mod = mod 
                            ; rank = ∣_∣
                            ; euc-eq = euc-eq 
                            ; euc-rank = euc-rank 
                            }

  -- Bundle.
  +-*-euclideanDomain : EuclideanDomainBundle _ _
  +-*-euclideanDomain = record
    { isEuclideanDomain = +-*-isEuclideanDomain
    }

