-- Every gate, every circuit and every generalized permutation is
-- unitary, and therefore so is every matrix a descent reaches.
--
-- This discharges the hypothesis Kopt.OptSteps.StepsUnitary: the
-- induction of Kopt.OptInduction needs to know that each operator
-- along a descent is still unitary, and a descent multiplies by
-- generalized permutations and K₁ gates only.
--
-- The unitarity of the sixteen gates is a closed computation, so it is
-- done the way the paper's finite verifications are done here: one
-- boolean check over the list of all gates, with the membership of the
-- gate in question turning it into a proof (Kopt.Descent.all-of-∈).
-- Equalities of concrete 4×4 matrices are stated as boolean tests and
-- converted with ==⇒≡, because deciding them as propositional
-- equalities is what the top-level README warns about.

{-# OPTIONS --without-K --safe #-}

module Kopt.GateUnitary where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Descent
  using (Op ; all-of ; all-of-∈ ; ∧-true ; _∈ˡ_ ; here ; there
        ; GP ; gp-mat ; Step ; gp-left ; gp-right ; K-left ; K-right ; step-of ; run)
open import Kopt.Unitary using (IsUnitary ; is-unitary)
open import Kopt.MatAdj using (unitary-*)
open import Kopt.GPData using (==⇒≡)
open import Kopt.Optimality using (gp-circuit ; gp-circuit-ok)
open import Kopt.OptSteps using (StepsUnitary)

-- ----------------------------------------------------------------------
-- * The gates

-- The gate set, in the order of Definition I.1, plus the scalar gate
-- and the two controlled-K gates (the same list as Test.KoptGates).
all-gates : List Gate
all-gates = X₀ ∷ X₁ ∷ Z₀ ∷ Z₁ ∷ S₀ ∷ S₁ ∷ K₀ ∷ K₁ ∷ CZ ∷ CS ∷ CX ∷ XC ∷ Ex ∷ Ii ∷ CK ∷ KC ∷ []

unitary? : Gate -> Bool
unitary? g = ((adjoint ⟦ g ⟧g * ⟦ g ⟧g) == 1#) ∧ ((⟦ g ⟧g * adjoint ⟦ g ⟧g) == 1#)

gates-unitary : all-of unitary? all-gates ≡ true
gates-unitary = refl

∈-all-gates : (g : Gate) -> g ∈ˡ all-gates
∈-all-gates X₀ = here
∈-all-gates X₁ = there here
∈-all-gates Z₀ = there (there here)
∈-all-gates Z₁ = there (there (there here))
∈-all-gates S₀ = there (there (there (there here)))
∈-all-gates S₁ = there (there (there (there (there here))))
∈-all-gates K₀ = there (there (there (there (there (there here)))))
∈-all-gates K₁ = there (there (there (there (there (there (there here))))))
∈-all-gates CZ = there (there (there (there (there (there (there (there here)))))))
∈-all-gates CS = there (there (there (there (there (there (there (there (there here))))))))
∈-all-gates CX = there (there (there (there (there (there (there (there (there (there here)))))))))
∈-all-gates XC =
  there (there (there (there (there (there (there (there (there (there (there here))))))))))
∈-all-gates Ex =
  there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))
∈-all-gates Ii =
  there (there (there (there (there (there (there (there (there (there (there (there
    (there here))))))))))))
∈-all-gates CK =
  there (there (there (there (there (there (there (there (there (there (there (there
    (there (there here)))))))))))))
∈-all-gates KC =
  there (there (there (there (there (there (there (there (there (there (there (there
    (there (there (there here))))))))))))))

gate-unitary : (g : Gate) -> IsUnitary ⟦ g ⟧g
gate-unitary g = is-unitary (==⇒≡ (proj₁ parts)) (==⇒≡ (proj₂ parts))
  where
    parts : ((adjoint ⟦ g ⟧g * ⟦ g ⟧g) == 1#) ≡ true × ((⟦ g ⟧g * adjoint ⟦ g ⟧g) == 1#) ≡ true
    parts = ∧-true (all-of-∈ unitary? all-gates gates-unitary (∈-all-gates g))

-- ----------------------------------------------------------------------
-- * Circuits

unitary-nil : IsUnitary ⟦ [] ⟧
unitary-nil = is-unitary (==⇒≡ refl) (==⇒≡ refl)

circuit-unitary : (c : Circuit) -> IsUnitary ⟦ c ⟧
circuit-unitary [] = unitary-nil
circuit-unitary (g ∷ c) = unitary-* (gate-unitary g) (circuit-unitary c)

-- ----------------------------------------------------------------------
-- * Generalized permutations
--
-- Via the exhaustive check of Section III C: gp-circuit G is a circuit
-- implementing G exactly (Kopt.Optimality.gp-circuit-ok).

gp-unitary : (G : GP) -> IsUnitary (gp-mat G)
gp-unitary G = subst IsUnitary (proj₁ (gp-circuit-ok G)) (circuit-unitary (gp-circuit G))

-- ----------------------------------------------------------------------
-- * Descents

step-unitary : (s : Step) (A : Op) -> IsUnitary A -> IsUnitary (step-of s A)
step-unitary (gp-left G) A hA = unitary-* (gp-unitary G) hA
step-unitary (gp-right G) A hA = unitary-* hA (gp-unitary G)
step-unitary K-left A hA = unitary-* (gate-unitary K₁) hA
step-unitary K-right A hA = unitary-* hA (gate-unitary K₁)

run-unitary : (ss : List Step) (A : Op) -> IsUnitary A -> IsUnitary (run ss A)
run-unitary [] A hA = hA
run-unitary (s ∷ ss) A hA = run-unitary ss (step-of s A) (step-unitary s A hA)

-- The hypothesis of Kopt.OptSteps, for every unitary operator.
steps-unitary-of : (A : Op) -> IsUnitary A -> StepsUnitary A
steps-unitary-of A hA ss = run-unitary ss A hA
