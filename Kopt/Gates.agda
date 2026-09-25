-- Section I of
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026):
--
-- the gate set 𝒢, circuits, and the semantics ⟦_⟧ : 𝒞ℐℛ → 𝒞𝒞𝒮.
--
-- The generators are
--
--   K = (1/γ)·[[1,1],[1,-1]]  (γ = 1+i),   S = diag(1,i),   Z = S²,
--   X = KZK·i,   CZ = diag(1,1,1,-1),   CS = diag(1,1,1,i),
--   CX = CX₀₁,   XC = CX₁₀,   Ex = swap,
--
-- with G₀ = G⊗I and G₁ = I⊗G. We also keep the authors' scalar gate
-- Ii = i·(I⊗I) (Haskell: II), which makes the semantics exact rather
-- than up-to-global-phase, and the controlled-K gates CK = I ⊕ K and
-- KC = Ex·CK·Ex, which Equation (1) expands into the gates of 𝒢.
--
-- The semantics is the one of the paper (Definition I.1),
-- ⟦A ++ B⟧ = ⟦A⟧ · ⟦B⟧, i.e. matrix-multiplication order, which is
-- the reverse of the usual quantum circuit order. It agrees with the
-- authors' Haskell u4of.

{-# OPTIONS --without-K --safe #-}

module Kopt.Gates where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_ ; length)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base

-- ----------------------------------------------------------------------
-- * The gate set (Definition I.1)

-- The gate set 𝒢 = {Xⱼ, Zₖ, Sₗ, Kₘ, CZ, CS, CX, XC, Ex} of the paper,
-- together with the scalar gate Ii = i·(I⊗I) and the controlled-K
-- gates CK, KC. The subscript 0 refers to the first (most
-- significant) qubit, the subscript 1 to the second one.
data Gate : Set where
  X₀ X₁ Z₀ Z₁ S₀ S₁ K₀ K₁ CZ CS CX XC Ex Ii CK KC : Gate

-- A circuit is a finite sequence of gates.
Circuit : Set
Circuit = List Gate

-- ----------------------------------------------------------------------
-- * The gate matrices

-- The one-qubit gates, as 2×2-matrices over 𝔻[i].

id-matrix : Matrix 2 2 DComplex
id-matrix = 1

x-matrix : Matrix 2 2 DComplex
x-matrix = matrix2x2 (0 , 1) (1 , 0)

z-matrix : Matrix 2 2 DComplex
z-matrix = matrix2x2 (1 , 0) (0 , - 1)

s-matrix : Matrix 2 2 DComplex
s-matrix = matrix2x2 (1 , 0) (0 , i)

-- K = ω⁷H = (1/(1+i))·[[1,1],[1,-1]].
k-matrix : Matrix 2 2 DComplex
k-matrix = matrix2x2 (κ , κ) (κ , - κ)
  where
    κ : DComplex
    κ = 1/γ

-- The Kronecker product of two one-qubit gates, G⊗H.
_⊗_ : Matrix 2 2 DComplex -> Matrix 2 2 DComplex -> Matrix 4 4 DComplex
a ⊗ b = tensor a b

-- The semantics of a single gate.
⟦_⟧g : Gate -> Matrix 4 4 DComplex
⟦ X₀ ⟧g = x-matrix ⊗ id-matrix
⟦ X₁ ⟧g = id-matrix ⊗ x-matrix
⟦ Z₀ ⟧g = z-matrix ⊗ id-matrix
⟦ Z₁ ⟧g = id-matrix ⊗ z-matrix
⟦ S₀ ⟧g = s-matrix ⊗ id-matrix
⟦ S₁ ⟧g = id-matrix ⊗ s-matrix
⟦ K₀ ⟧g = k-matrix ⊗ id-matrix
⟦ K₁ ⟧g = id-matrix ⊗ k-matrix
⟦ CZ ⟧g = matrix4x4 (1 , 0 , 0 , 0)
                    (0 , 1 , 0 , 0)
                    (0 , 0 , 1 , 0)
                    (0 , 0 , 0 , - 1)
⟦ CS ⟧g = matrix4x4 (1 , 0 , 0 , 0)
                    (0 , 1 , 0 , 0)
                    (0 , 0 , 1 , 0)
                    (0 , 0 , 0 , i)
⟦ CX ⟧g = cnot
⟦ XC ⟧g = matrix4x4 (1 , 0 , 0 , 0)
                    (0 , 0 , 0 , 1)
                    (0 , 0 , 1 , 0)
                    (0 , 1 , 0 , 0)
⟦ Ex ⟧g = swap
⟦ Ii ⟧g = i scalarmult 1
⟦ CK ⟧g = oplus id-matrix k-matrix
⟦ KC ⟧g = matrix4x4 (1 , 0 , 0 , 0)
                    (0 , κ , 0 , κ)
                    (0 , 0 , 1 , 0)
                    (0 , κ , 0 , - κ)
  where
    κ : DComplex
    κ = 1/γ

-- The semantics of a circuit (Definition I.1): ⟦A ++ B⟧ = ⟦A⟧ · ⟦B⟧.
⟦_⟧ : Circuit -> Matrix 4 4 DComplex
⟦ [] ⟧ = 1
⟦ g ∷ c ⟧ = ⟦ g ⟧g * ⟦ c ⟧

-- ----------------------------------------------------------------------
-- * Inverses

-- The inverse of a gate, as a circuit (Haskell: inv_gate).
inv-gate : Gate -> Circuit
inv-gate X₀ = X₀ ∷ []
inv-gate X₁ = X₁ ∷ []
inv-gate Z₀ = Z₀ ∷ []
inv-gate Z₁ = Z₁ ∷ []
inv-gate S₀ = Z₀ ∷ S₀ ∷ []
inv-gate S₁ = Z₁ ∷ S₁ ∷ []
inv-gate K₀ = K₀ ∷ Ii ∷ []
inv-gate K₁ = K₁ ∷ Ii ∷ []
inv-gate CZ = CZ ∷ []
inv-gate CS = CZ ∷ CS ∷ []
inv-gate CX = CX ∷ []
inv-gate XC = XC ∷ []
inv-gate Ex = Ex ∷ []
inv-gate Ii = Ii ∷ Ii ∷ Ii ∷ []
inv-gate CK = CK ∷ S₀ ∷ []
inv-gate KC = KC ∷ S₁ ∷ []

-- The inverse of a circuit (Haskell: inv_cir).
inv-circuit : Circuit -> Circuit
inv-circuit c = List.concatMap inv-gate (List.reverse c)

-- ----------------------------------------------------------------------
-- * Equation (1): the controlled-K gates in terms of 𝒢

-- CK = CZ·Z₀S₀Z₁S₁K₁CSK₁S₁·i  (Equation (1) of the paper; the
-- authors' decompose_ck).
ck-expansion : Circuit
ck-expansion = CZ ∷ Z₀ ∷ S₀ ∷ Z₁ ∷ S₁ ∷ K₁ ∷ CS ∷ K₁ ∷ S₁ ∷ Ii ∷ []

-- The mirror image, KC = Ex·CK·Ex.
kc-expansion : Circuit
kc-expansion = CZ ∷ Z₁ ∷ S₁ ∷ Z₀ ∷ S₀ ∷ K₀ ∷ CS ∷ K₀ ∷ S₀ ∷ Ii ∷ []

-- Replace a controlled-K gate by its expansion (Haskell:
-- decompose_ck; that function only expands CK, we also expand KC).
decompose-ck : Gate -> Circuit
decompose-ck CK = ck-expansion
decompose-ck KC = kc-expansion
decompose-ck g = g ∷ []

-- Rewrite a circuit over the extended gate set into one over 𝒢 ∪ {i}
-- (Haskell: desugar_ck).
desugar-ck : Circuit -> Circuit
desugar-ck = List.concatMap decompose-ck

-- ----------------------------------------------------------------------
-- * Gate counts (Definition V.1)

-- Is the gate a K gate? (Used to split a circuit at its K gates,
-- which are the only gates that change the lde; Remark II.10.)
is-k-gate : Gate -> Bool
is-k-gate K₀ = true
is-k-gate K₁ = true
is-k-gate _ = false

-- The raw K-count: the number of K gates in the circuit.
kc : Circuit -> ℕ
kc [] = 0
kc (K₀ ∷ c) = suc (kc c)
kc (K₁ ∷ c) = suc (kc c)
kc (_ ∷ c) = kc c

-- The raw CS-count: the number of CS gates in the circuit.
csc : Circuit -> ℕ
csc [] = 0
csc (CS ∷ c) = suc (csc c)
csc (_ ∷ c) = csc c

-- The raw length: the total number of gates.
rlen : Circuit -> ℕ
rlen = length

-- ----------------------------------------------------------------------
-- * Decidable equality

private
  gate-code : Gate -> ℕ
  gate-code X₀ = 0
  gate-code X₁ = 1
  gate-code Z₀ = 2
  gate-code Z₁ = 3
  gate-code S₀ = 4
  gate-code S₁ = 5
  gate-code K₀ = 6
  gate-code K₁ = 7
  gate-code CZ = 8
  gate-code CS = 9
  gate-code CX = 10
  gate-code XC = 11
  gate-code Ex = 12
  gate-code Ii = 13
  gate-code CK = 14
  gate-code KC = 15

  gate-decode : ℕ -> Gate
  gate-decode 0 = X₀
  gate-decode 1 = X₁
  gate-decode 2 = Z₀
  gate-decode 3 = Z₁
  gate-decode 4 = S₀
  gate-decode 5 = S₁
  gate-decode 6 = K₀
  gate-decode 7 = K₁
  gate-decode 8 = CZ
  gate-decode 9 = CS
  gate-decode 10 = CX
  gate-decode 11 = XC
  gate-decode 12 = Ex
  gate-decode 13 = Ii
  gate-decode 14 = CK
  gate-decode _ = KC

  gate-decode-code : (g : Gate) -> gate-decode (gate-code g) ≡ g
  gate-decode-code X₀ = refl
  gate-decode-code X₁ = refl
  gate-decode-code Z₀ = refl
  gate-decode-code Z₁ = refl
  gate-decode-code S₀ = refl
  gate-decode-code S₁ = refl
  gate-decode-code K₀ = refl
  gate-decode-code K₁ = refl
  gate-decode-code CZ = refl
  gate-decode-code CS = refl
  gate-decode-code CX = refl
  gate-decode-code XC = refl
  gate-decode-code Ex = refl
  gate-decode-code Ii = refl
  gate-decode-code CK = refl
  gate-decode-code KC = refl

gate-≟ : DecidableEquality Gate
gate-≟ g h with gate-code g ≟ gate-code h
... | yes p = yes (trans (sym (gate-decode-code g)) (trans (cong gate-decode p) (gate-decode-code h)))
... | no ¬p = no λ { refl -> ¬p refl }

-- ----------------------------------------------------------------------
-- * Printing

-- Gates are printed like in the paper and in the authors' Haskell
-- code; the scalar gate Ii is printed "II", as in Haskell.
show-gate : Gate -> String
show-gate X₀ = "X0"
show-gate X₁ = "X1"
show-gate Z₀ = "Z0"
show-gate Z₁ = "Z1"
show-gate S₀ = "S0"
show-gate S₁ = "S1"
show-gate K₀ = "K0"
show-gate K₁ = "K1"
show-gate CZ = "CZ"
show-gate CS = "CS"
show-gate CX = "CX"
show-gate XC = "XC"
show-gate Ex = "Ex"
show-gate Ii = "II"
show-gate CK = "CK"
show-gate KC = "KC"

-- Circuits are printed like Haskell's show for lists, e.g. "[K1,CS,K1]".
show-circuit : Circuit -> String
show-circuit = showList (λ _ -> show-gate)

instance
  DecEqGate : DecEq Gate
  DecEqGate ._≟_ = gate-≟

  ShowGate : Show Gate
  ShowGate .showsPrec _ = show-gate

  ShowCircuit : Show Circuit
  ShowCircuit .showsPrec _ = show-circuit
