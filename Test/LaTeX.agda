-- refl-based tests for Quantum.Synthesis.LaTeX. The expected strings
-- are the outputs of the Haskell reference implementation (newsynth
-- 0.4.1.0); see also Test/LaTeXRun.agda for more (compiled) tests.
module Test.LaTeX where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix hiding (Plus ; Times)
open import Quantum.Synthesis.MultiQubitSynthesis
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.LaTeX

_ : showlatex (TL-X 0 1 ∷ TL-T -1 2 3 ∷ TL-omega 1 0 ∷ TL-T 8 0 1 ∷ []) ≡ "X\\level{1,2} T^7\\level{3,4} \\omega\\level{1} "
_ = refl

_ : showlatex (ZOmega ∋ Omega -1 1 -1 1) ≡ "-\\omega^3+\\omega^2-\\omega+1"
_ = refl

_ : showlatex (ZRootTwo ∋ RootTwo -2 -3) ≡ "-2 - 3 \\sqrt{2}"
_ = refl

_ : showlatex (DRootTwo ∋ 1 + roothalf) ≡ "\\frac{1}{1} + \\frac{1}{2} \\sqrt{2}"
_ = refl

_ : showlatex (ZRootTwo [i] ∋ Cplx (RootTwo 0 2) (RootTwo -1 1)) ≡ "2 \\sqrt{2}+(-1 + \\sqrt{2})\\,i"
_ = refl

_ : showlatex (DOmega ∋ omega ^ 3 * roothalf ^ 3) ≡ "\\frac{1}{\\sqrt{2}^{3}}(\\omega^3)"
_ = refl

_ : showlatex (U2 DOmega ∋ from-gates (H ∷ [])) ≡ "\\frac{1}{\\sqrt{2}}\\begin{pmatrix}1 & 1\\\\1 & -1\\\\\\end{pmatrix}"
_ = refl

_ : showlatex (W ∷ H ∷ W ∷ T ∷ []) ≡ "{\\omega}H{\\omega}T"
_ = refl

_ : showlatex (Negate (Negate (Const -3))) ≡ "-(--3)"
_ = refl

_ : showlatex (Float ∋ 0.125) ≡ "0.1250000000"
_ = refl

_ : showlatex (Float ∋ 1.0 Float.÷ 3.0) ≡ "0.3333333333"
_ = refl

_ : show-ffloat 1 0.25 ≡ "0.2"
_ = refl

_ : show-ffloat 1 0.35 ≡ "0.4"
_ = refl
