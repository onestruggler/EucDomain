-- Tests for the least denominator exponents DenomExp[ δ ] with the
-- bases √2, 2, 1 + i and 1 + ω (Quantum.Synthesis.Ring), checked by
-- evaluation.

{-# OPTIONS --without-K --safe #-}

module Test.DenomExp where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤ ; tt)
open import Function.Base using (_∋_)
open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; T)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix hiding (Plus ; Times)
open import Quantum.Synthesis.LaTeX

-- ----------------------------------------------------------------------
-- The newsynth functions (base √2) are unchanged.

_ : denomexp (DRootTwo ∋ √½) ≡ 1
_ = refl
_ : denomexp (DOmega ∋ √½ ^ 5) ≡ 5
_ = refl
_ : denomexp-decompose {List DOmega} {List ZOmega} (√½ ∷ ½ ∷ []) ≡ (Omega -1 0 1 0 ∷ Omega 0 0 0 1 ∷ [] , 2)
_ = refl
_ : denomexp (U2 DOmega ∋ matrix2x2 (√½ , √½) (√½ , - √½)) ≡ 1
_ = refl

-- Nested in other output (showsPrec at precedence > 7).
_ : showsPrec 11 (DOmega ∋ √½ * ω) ≡ "(roothalf * Omega 0 0 1 0)"
_ = refl
_ : showsPrec 7 (DOmega ∋ √½ ^ 3 * (1 + ω)) ≡ "roothalf^3 * Omega 0 0 1 1"
_ = refl
_ : showsPrec 11 (DRComplex ∋ ω) ≡ "(roothalf * (1 + i))"
_ = refl
_ : showsPrec 11 (DOmega ∋ 1 + ω) ≡ "(Omega 0 0 1 1)"
_ = refl
_ : showlatex-p 8 (DOmega ∋ roothalf) ≡ "(\\frac{1}{\\sqrt{2}}(1))"
_ = refl

-- DenomExp can still be used in constraints and as the type of an
-- instance, which is defined by the fields denomexp-of and
-- denomexp-factor-of.
denomexp' : {A : Set} {{_ : DenomExp A}} -> A -> ℕ
denomexp' = denomexp

_ : denomexp' (DOmega ∋ √½ ^ 3) ≡ 3
_ = refl

record Wrap : Set where
  constructor wrap
  field unwrap : DOmega

instance
  DenomExpWrap : DenomExp Wrap
  DenomExpWrap .denomexp-of (wrap a) = denomexp a
  DenomExpWrap .denomexp-factor-of (wrap a) k = wrap (denomexp-factor a k)

_ : denomexp (wrap (√½ ^ 3)) ≡ 3
_ = refl
_ : denomexp-factor (wrap √½) 1 ≡ wrap 1
_ = refl

-- ----------------------------------------------------------------------
-- 𝔻 with base 2.

_ : denomexp[ 2 ] (Dyadic ∋ 3 * ½ ^ 4) ≡ 4
_ = refl
_ : denomexp[ 2 ] (Dyadic ∋ 5) ≡ 0
_ = refl
_ : denomexp-decompose[ 2 ] {Dyadic} {ℤ} (3 * ½ ^ 4) ≡ (3 , 4)
_ = refl
_ : showsPrec-DenomExp[ 2 ] {Dyadic} {ℤ} 0 (3 * ½ ^ 4) ≡ "half^4 * 3"
_ = refl
_ : showsPrec-DenomExp[ 2 ] {Dyadic} {ℤ} 0 5 ≡ "5"
_ = refl

-- Multiplication by 2ᵏ.
_ : dyadic-shift (3 * ½ ^ 4) 2 ≡ 3 * ½ ^ 2
_ = refl
_ : dyadic-shift (3 * ½ ^ 4) 6 ≡ 12
_ = refl
_ : dyadic-shift (-3 * ½) 1 ≡ -3
_ = refl
_ : dyadic-shift -5 3 ≡ -40
_ = refl
_ : dyadic-shift 0 3 ≡ 0
_ = refl

-- 𝔻[√2] with bases √2 and 2.
_ : denomexp[ 2 ] (DRootTwo ∋ √½) ≡ 1
_ = refl
_ : denomexp[ √2 ] (DRootTwo ∋ ½ ^ 3 + √2) ≡ 6
_ = refl
_ : denomexp[ 2 ] (DRootTwo ∋ ½ ^ 3 + √2) ≡ 3
_ = refl
_ : denomexp-decompose[ 2 ] (DRootTwo ∋ √½ ^ 3) ≡ (RootTwo 0 1 , 2)
_ = refl

-- 𝔻[i] with bases 1 + i and 2.
_ : denomexp[ 1 + i ] (DComplex ∋ ½) ≡ 2
_ = refl
_ : denomexp[ 1 + i ] (DComplex ∋ (1 + i) * ½) ≡ 1
_ = refl
_ : denomexp[ 1 + i ] (DComplex ∋ (1 + i) * ½ ^ 2) ≡ 3
_ = refl
_ : denomexp[ 1 + i ] (DComplex ∋ (3 + 5 * i) * ½ ^ 3) ≡ 5
_ = refl
_ : denomexp[ 1 + i ] (DComplex ∋ 3 - i) ≡ 0
_ = refl
_ : denomexp-decompose[ 1 + i ] (DComplex ∋ ½) ≡ (i , 2)
_ = refl
_ : denomexp[ 2 ] (DComplex ∋ (1 + i) * ½ ^ 3) ≡ 3
_ = refl
_ : showsPrec-DenomExp[ 1 + i ] {DComplex} {ZComplex} 0 ½ ≡ "recip (1 + i)^2 * i"
_ = refl
_ : showsPrec-DenomExp[ 2 ] {DComplex} {ZComplex} 0 ((1 + i) * ½ ^ 3) ≡ "half^3 * (1 + i)"
_ = refl

-- 𝔻[√2,i] with bases √2, 2 (componentwise) and 1 + i (by search).
-- Note that ω is not in ℤ[√2][i].
_ : denomexp[ √2 ] (DRComplex ∋ ω) ≡ 1
_ = refl
_ : denomexp[ 2 ] (DRComplex ∋ ω) ≡ 1
_ = refl
_ : denomexp[ 1 + i ] (DRComplex ∋ ω) ≡ 1
_ = refl
_ : denomexp[ 1 + i ] (DRComplex ∋ √½) ≡ 2
_ = refl
_ : denomexp[ 1 + i ] (DRComplex ∋ ½ ^ 3) ≡ 6
_ = refl
_ : show (DRComplex ∋ ω) ≡ "roothalf * (1 + i)"
_ = refl

-- 𝔻[ω] with bases √2, 1 + i, 1 + ω and 2.
_ : denomexp[ 1 + ω ] (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexp[ 1 + ω ] (DOmega ∋ √½) ≡ 2
_ = refl
_ : denomexp[ 1 + ω ] (DOmega ∋ (1 + ω) * ½) ≡ 3
_ = refl
_ : denomexp[ 1 + ω ] (DOmega ∋ (1 + ω) ^ 3 * ½) ≡ 1
_ = refl
_ : denomexp[ 1 + ω ] (DOmega ∋ ω ^ 3 - i) ≡ 0
_ = refl
-- (1 + ω)⁻¹ = (ω - i)/√2.
_ : denomexp-decompose[ 1 + ω ] (DOmega ∋ √½ * (ω - i)) ≡ (1 , 1)
_ = refl
_ : denomexp-decompose[ 1 + ω ] (DOmega ∋ ½) ≡ (Omega 2 3 2 0 , 4)
_ = refl
_ : denomexp[ 2 ] (DOmega ∋ √½ ^ 5) ≡ 3
_ = refl
_ : denomexp[ 1 + i ] (DOmega ∋ √½ ^ 5) ≡ 5
_ = refl
_ : denomexp-decompose[ 1 + i ] (DOmega ∋ √½ ^ 5) ≡ (Omega 0 0 -1 0 , 5)
_ = refl
_ : showsPrec-DenomExp[ 1 + ω ] {DOmega} {ZOmega} 0 ½ ≡ "recip (1 + omega)^4 * Omega 2 3 2 0"
_ = refl
_ : showsPrec-DenomExp[ 2 ] {DOmega} {ZOmega} 0 (√½ ^ 3 * (1 + ω)) ≡ "half^2 * Omega (-1) 1 1 1"
_ = refl
_ : showsPrec-DenomExp[ √2 ] {DOmega} {ZOmega} 0 (√½ ^ 3 * (1 + ω)) ≡ "roothalf^3 * Omega 0 0 1 1"
_ = refl
_ : show (DOmega ∋ √½ ^ 3 * (1 + ω)) ≡ "roothalf^3 * Omega 0 0 1 1"
_ = refl
_ : show-recip-base (Omega 0 0 1 2) ≡ "recip (Omega 0 0 1 2)"
_ = refl

-- Precedence.
_ : showsPrec-DenomExp[ 2 ] {DOmega} {ZOmega} 11 (1 + ω) ≡ "(Omega 0 0 1 1)"
_ = refl
_ : showsPrec-DenomExp[ 1 + ω ] {DOmega} {ZOmega} 7 (√½ * (ω - i)) ≡ "recip (1 + omega) * Omega 0 0 0 1"
_ = refl
_ : showsPrec-DenomExp[ 1 + ω ] {DOmega} {ZOmega} 8 (√½ * (ω - i)) ≡ "(recip (1 + omega) * Omega 0 0 0 1)"
_ = refl
_ : showsPrec-DenomExp[ 2 ] {DOmega} {ZOmega} 7 (√½ ^ 3 * (1 + ω)) ≡ "half^2 * Omega (-1) 1 1 1"
_ = refl
_ : showsPrec-DenomExp[ 2 ] {DOmega} {ZOmega} 8 (√½ ^ 3 * (1 + ω)) ≡ "(half^2 * Omega (-1) 1 1 1)"
_ = refl

-- ----------------------------------------------------------------------
-- The base is matched up to evaluation.

_ : denomexp[ ω + 1 ] (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexp[ Omega 0 0 1 1 ] (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexp[ 1 + omega ] (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexp[ fromZRootTwo (RootTwo 0 1) ] (DOmega ∋ √½) ≡ 1
_ = refl
_ : denomexp[ ω - ω ^ 3 ] (DOmega ∋ √½) ≡ 1
_ = refl
_ : denomexp[ roottwo ] (DOmega ∋ √½) ≡ 1
_ = refl
_ : denomexp[ 1 + 1 ] (DOmega ∋ ½) ≡ 1
_ = refl
_ : denomexp[ √2 * √2 ] (DOmega ∋ ½) ≡ 1
_ = refl
_ : denomexp[ -i * (1 + i) ^ 2 ] (DOmega ∋ ½) ≡ 1
_ = refl
_ : denomexp[ ω ^ 2 + 1 ] (DComplex ∋ ½) ≡ 2
_ = refl
_ : denomexp[ i + 1 ] (DComplex ∋ ½) ≡ 2
_ = refl

-- ----------------------------------------------------------------------
-- Containers, for every base.

_ : denomexp[ 1 + ω ] (List DOmega ∋ ½ ∷ √½ ∷ []) ≡ 4
_ = refl
_ : denomexp[ 1 + ω ] (DOmega × DOmega ∋ (√½ , 1)) ≡ 2
_ = refl
_ : denomexp[ 2 ] (DRootTwo × DOmega ∋ (√½ , ½ ^ 3)) ≡ 3
_ = refl
_ : denomexp[ 1 + ω ] (U2 DOmega ∋ matrix2x2 (√½ , √½) (√½ , - √½)) ≡ 2
_ = refl
_ : denomexp[ 2 ] (U2 DOmega ∋ matrix2x2 (√½ , √½) (√½ , - √½)) ≡ 1
_ = refl
_ : denomexp[ 1 + i ] (U2 DComplex ∋ matrix2x2 (½ , ½) (½ , - ½)) ≡ 2
_ = refl
_ : denomexp-decompose[ 1 + ω ] {List DOmega} {List ZOmega} (√½ ∷ []) ≡ (Omega 0 1 1 1 ∷ [] , 2)
_ = refl
_ : denomexp[ 2 ] (List DOmega ∋ []) ≡ 0
_ = refl
_ : denomexp-decompose[ 2 ] {DOmega × DOmega} {ZOmega × ZOmega} (½ , ½ ^ 2) ≡ ((Omega 0 0 0 2 , Omega 0 0 0 1) , 2)
_ = refl
_ : denomexp[ 2 ] (U2 DOmega ∋ matrix2x2 (1 , ½) (0 , 1)) ≡ 1
_ = refl
_ : denomexp[ 2 ] (U2 DOmega ∋ matrix2x2 (1 , 0) (0 , ½)) ≡ 1
_ = refl
_ : denomexp[ 1 + ω ] (DOmega × ⊤ ∋ (1 , tt)) ≡ 0
_ = refl
_ : denomexp[ 2 ] (⊤ ∋ tt) ≡ 0
_ = refl
_ : denomexp (DOmega × ⊤ ∋ (√½ , tt)) ≡ 1
_ = refl
_ : denomexp-decompose[ 1 + ω ] {DOmega × ⊤} {ZOmega × ⊤} (1 , tt) ≡ ((1 , tt) , 0)
_ = refl

-- ----------------------------------------------------------------------
-- LaTeX.

_ : showlatex (DOmega ∋ omega ^ 3 * roothalf ^ 3) ≡ "\\frac{1}{\\sqrt{2}^{3}}(\\omega^3)"
_ = refl
_ : showlatex-denomexp-p[ √2 ] {DOmega} {ZOmega} 0 roothalf ≡ "\\frac{1}{\\sqrt{2}}(1)"
_ = refl
_ : showlatex-denomexp-p[ 1 + ω ] {DOmega} {ZOmega} 0 ½ ≡ "\\frac{1}{(1+\\omega)^{4}}(2\\omega^3+3\\omega^2+2\\omega)"
_ = refl
_ : showlatex-denomexp-p[ 1 + ω ] {DOmega} {ZOmega} 0 (√½ * (ω - i)) ≡ "\\frac{1}{1+\\omega}(1)"
_ = refl
_ : showlatex-denomexp-p[ 2 ] {DOmega} {ZOmega} 0 (omega ^ 3 * roothalf ^ 3) ≡ "\\frac{1}{2^{2}}(\\omega^2-1)"
_ = refl
_ : showlatex-denomexp-p[ 1 + i ] {DComplex} {ZComplex} 0 ½ ≡ "\\frac{1}{(1+i)^{2}}i"
_ = refl
_ : showlatex-denomexp-p[ 1 + i ] {DComplex} {ZComplex} 0 ((1 + i) * ½) ≡ "\\frac{1}{1+i}i"
_ = refl
_ : showlatex-denomexp-p[ 1 + i ] {U2 DComplex} {U2 ZComplex} 0 (matrix2x2 (½ , ½) (½ , - ½)) ≡ "\\frac{1}{(1+i)^{2}}\\begin{pmatrix}i & i\\\\i & -i\\\\\\end{pmatrix}"
_ = refl
_ : showlatex-base 8 (Omega 0 0 1 2) ≡ "(\\omega+2)"
_ = refl

-- Precedence.
_ : showlatex-denomexp-p[ 2 ] {DOmega} {ZOmega} 0 (1 + ω) ≡ "\\omega+1"
_ = refl
_ : showlatex-denomexp-p[ 2 ] {DOmega} {ZOmega} 7 (1 + ω) ≡ "(\\omega+1)"
_ = refl
_ : showlatex-denomexp-p[ 1 + ω ] {DOmega} {ZOmega} 7 (√½ * (ω - i)) ≡ "\\frac{1}{1+\\omega}(1)"
_ = refl
_ : showlatex-denomexp-p[ 1 + ω ] {DOmega} {ZOmega} 8 (√½ * (ω - i)) ≡ "(\\frac{1}{1+\\omega}(1))"
_ = refl
_ : showlatex-denomexp-p[ 2 ] {DOmega} {ZOmega} 7 (omega ^ 3 * roothalf ^ 3) ≡ "\\frac{1}{2^{2}}(\\omega^2-1)"
_ = refl
_ : showlatex-denomexp-p[ 2 ] {DOmega} {ZOmega} 8 (omega ^ 3 * roothalf ^ 3) ≡ "(\\frac{1}{2^{2}}(\\omega^2-1))"
_ = refl

-- ----------------------------------------------------------------------
-- A new base, defined by the user: 1 - i for 𝔻[i], by search
-- ((1 - i)² = -2i). It is preferred to the generic componentwise
-- instance for 𝔻[i], which is OVERLAPPABLE.

instance
  DenomExpDComplex-1-i : DenomExp[ 1 - i ] DComplex
  DenomExpDComplex-1-i = denomexp-by-search 2 (1 - i)

_ : denomexp[ 1 - i ] (DComplex ∋ (3 + 5 * i) * ½ ^ 3) ≡ 5
_ = refl
_ : showsPrec-DenomExp-named (1 - i) "recip (1 - i)" {DComplex} {ZComplex} 0 ½ ≡ "recip (1 - i)^2 * (-i)"
_ = refl

-- The base 1 + ω for 𝔻[ω] by search ((1 + ω)⁴ = 2u for a unit u),
-- which exercises more than one step of the search. (Not an instance,
-- since there is one already.) It is compared with the instance on
-- the samples below.
search-1+ω : DenomExp[ 1 + ω ] DOmega
search-1+ω = denomexp-by-search 4 (1 + ω)

_ : denomexp[ 1 + ω ] {{search-1+ω}} ((1 + ω) * ½) ≡ 3
_ = refl

-- The value δA passed to denomexp-by-search is checked (by instance
-- arguments) to be equal to the base, and to be integral.
_ : (e : ℕ) (δA : DComplex) -> .{{_ : T (toQOmega δA == toQOmega (ZOmega ∋ 1 + i))}}
  -> .{{_ : T (from-whole {DComplex} {ZComplex} (to-whole δA) == δA)}} -> DenomExp[ 1 + i ] DComplex
_ = denomexp-by-search

-- ----------------------------------------------------------------------
-- Checks on samples of elements: for k = denomexp[ δ ] a, aδᵏ is
-- integral and aδᵏ⁻¹ is not (if k > 0); the exponents for different
-- bases are related as expected; and multiplication by 2ᵏ is right.

module _ {A B : Set} {{_ : Ring A}} {{_ : DecEq A}} {{_ : WholePart A B}} where
  open LiteralsFor A

  integral : A -> Bool
  integral x = from-whole {A} {B} (to-whole x) == x

  least-ok : (δ : ZOmega) {{_ : DenomExp[ δ ] A}} -> A -> Bool
  least-ok δ a with denomexp[ δ ] a
  ... | zero = integral (denomexp-factor[ δ ] a 0)
  ... | suc k = integral (denomexp-factor[ δ ] a (suc k)) ∧ not (integral (denomexp-factor[ δ ] a k))

  all-ok : (δ : ZOmega) {{_ : DenomExp[ δ ] A}} -> List A -> Bool
  all-ok δ = List.foldr (λ a b -> least-ok δ a ∧ b) true

  -- denomexp-factor[ 2 ] a k = a2ᵏ for k ≤ 5.
  shift-ok : {{_ : DenomExp[ 2 ] A}} -> List A -> Bool
  shift-ok = List.foldr (λ a b -> List.foldr (λ k c -> (denomexp-factor[ 2 ] a k == a * 2 ^ k) ∧ c) b ks) true
    where
      ks : List ℕ
      ks = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

ceil-half : ℕ -> ℕ
ceil-half n = (n Nat.+ 1) Nat./ 2

-- All checks for an element of 𝔻[ω], for all four bases: the least
-- exponents are right; k√2 = k₁₊ᵢ = ⌈k₁₊ω / 2⌉ and k₂ = ⌈k√2 / 2⌉; and
-- the formula for 1 + ω agrees with the search.
omega-ok : DOmega -> Bool
omega-ok a = least-ok (1 + ω) a ∧ least-ok √2 a ∧ least-ok (1 + i) a ∧ least-ok 2 a
  ∧ (denomexp[ √2 ] a == ceil-half (denomexp[ 1 + ω ] a))
  ∧ (denomexp[ 1 + i ] a == denomexp[ √2 ] a)
  ∧ (denomexp[ 2 ] a == ceil-half (denomexp[ √2 ] a))
  ∧ (denomexp[ 1 + ω ] {{search-1+ω}} a == denomexp[ 1 + ω ] a)

coeffs : List ℤ
coeffs = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

sample-omega : List DOmega
sample-omega = List.concatMap (λ s -> List.concatMap (λ a -> List.concatMap (λ b -> List.concatMap (λ c -> List.map (λ d ->
  s * fromZOmega (Omega a b c d)) coeffs) coeffs) coeffs) coeffs) (1 ∷ ½ ∷ √½ * ½ ∷ [])

sample-complex : List DComplex
sample-complex = List.concatMap (λ s -> List.concatMap (λ a -> List.map (λ b ->
  s * Cplx (fromℤ a) (fromℤ b)) (coeffs List.++ (4 ∷ 5 ∷ 6 ∷ 7 ∷ []))) (coeffs List.++ (4 ∷ 5 ∷ 6 ∷ 7 ∷ []))) (1 ∷ ½ ∷ ½ ^ 2 ∷ [])

sample-rcomplex : List DRComplex
sample-rcomplex = List.concatMap (λ s -> List.concatMap (λ a -> List.map (λ b ->
  s * Cplx (fromℤ[√2] a b) (fromℤ[√2] b a)) coeffs) coeffs) (1 ∷ √½ ∷ ½ ∷ √½ ^ 3 ∷ [])

-- Elements with negative and odd or even coefficients, for dyadic-shift.
signed : List ℤ
signed = -3 ∷ -2 ∷ 0 ∷ 1 ∷ 4 ∷ []

sample-signed : List DOmega
sample-signed = List.concatMap (λ s -> List.concatMap (λ a -> List.map (λ b ->
  s * Omega (fromℤ a) 0 (fromℤ b) (fromℤ (a - b))) signed) signed) (1 ∷ ½ ∷ ½ ^ 3 ∷ [])

_ : List.foldr (λ a b -> omega-ok a ∧ b) true sample-omega ≡ true
_ = refl
_ : all-ok (1 + i) sample-complex ≡ true
_ = refl
_ : all-ok 2 sample-complex ≡ true
_ = refl
_ : all-ok (1 - i) sample-complex ≡ true
_ = refl
_ : all-ok (1 + i) sample-rcomplex ≡ true
_ = refl
_ : all-ok √2 sample-rcomplex ≡ true
_ = refl
_ : all-ok 2 sample-rcomplex ≡ true
_ = refl
_ : shift-ok sample-signed ≡ true
_ = refl
_ : shift-ok (List.map (λ { (Omega a b c d) -> RootTwo d c }) sample-signed) ≡ true
_ = refl
_ : shift-ok (List.map (λ { (Omega a b c d) -> Cplx d a }) sample-signed) ≡ true
_ = refl
