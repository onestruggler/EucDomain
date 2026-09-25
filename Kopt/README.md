# Kopt: a formalization of K-optimal two-qubit Clifford+CS synthesis

An Agda formalization of

> X. Bian and Y. Feng, *K-Optimal and CS-Near-Optimal Exact Synthesis of Two-Qubit Clifford+CS
> Operators* (2026),

built on the ring framework of this repository (`Typeclasses`, `Instances`,
`Quantum.Synthesis.Ring`, `Quantum.Synthesis.Matrix`). The paper's rings are the framework's:
ℤ[i] = `ZComplex` (the Gaussian integers of `GauInt`), 𝔻[i] = `DComplex`, ℤ₂ = `Z2`, and a
two-qubit operator is a `Matrix 4 4 DComplex`.

## Modules

| module | paper | contents |
|---|---|---|
| `Kopt.Base` | II | γ = 1+i, parity in ℤ[i] (Def. II.4), the least denominator exponent `lde` (Def. II.1) as a type class, residues ρₙ : ℤ[i] → ℤ[i]/(γⁿ) as binary strings, (n,l)-residues (Def. II.3), shifts |
| `Kopt.Gates` | I | the gate set 𝒢, circuits, the semantics ⟦_⟧ with ⟦A++B⟧ = ⟦A⟧·⟦B⟧, inverses, the counts rkc/rcs/rlen, Equation (1) |
| `Kopt.Permutations` | III | the 24 permutation matrices and their Table I circuits, the 256 diagonal unitaries, generalized permutations (`gperm-of`, computed, not tabulated) |
| `Kopt.Patterns` | IV A–B | the six residue patterns, `lemma-six`, the refinements `refine-ii` … `refine-vi` and their ρ₂ normal forms |
| `Kopt.Synth` | IV B–C | `decrease1-lde`, `synth`, `optimize-gp`, `prkc` (Table II), Cor. IV.8 |
| `Kopt.Properties.*` | II | the proofs of Section II (see below); `Kopt.Properties.Algebra` re-exports them |
| `Kopt.Descent`, `Kopt.Optimality` | V | descents, the optimality statements and their proofs/checks |

Tests are in `Test/Kopt*.agda`; the `*Run` modules are compiled programs (`agda --compile`).

## What is proved, and what is checked

Proofs (Agda, `--safe`, no postulates) — Section II:
ρₙ is well defined, sound and injective, and stable under increasing n; the residue arithmetic mod γ²
and mod γ³ (including ρ₂(x†) = ρ₂(x) and ρ₃(x†) = ab(c⊕b)); Lemma II.5 (odd ⟺ odd norm), Lemma II.6
(cancelling γ), Lemma II.7, Lemma II.8 (subadditivity of lde), Lemma II.9 (shifts) and the four
K-action cases of Section II C; and that the `lde` used by the algorithm is the least denominator
exponent (existence and minimality).

Executable and exhaustively checked: the 24 Table I circuits, the 256 diagonal unitaries, and all
6144 generalized permutations (each synthesized exactly, with ≤ 9 gates, ≤ 1 CS and no K gate).

End-to-end validation against the authors' dataset (`experiment_data.dat`, 12,000 records, lde up to
152): for every record, `lde U` is the recorded lde, `⟦synth U⟧ = U` exactly, and the K- and CS-counts
equal the recorded ones; the descent invariants of Lemmas IV.1/IV.4 and Table II hold at all
1,193,146 steps.

## Two corrections to the paper

1. **Corollary V.10.** From cs(A) ≥ kc(A)/2 − 1 one gets (k+1)/cs(A) ≤ 2(k+1)/(k−2) = 2 + **6**/(k−2);
   the paper prints 2 + 4/(k−2), which is strictly smaller and fails whenever the lower bound of
   Theorem V.9 is tight (21 of the 12,000 dataset records). The asymptotic claim — CS-count at most
   twice optimal — is unaffected.
2. **The ρ₂ normal form of case (iv)ᵀ.** Since γ† = −iγ, we have ρˡ₂(A†) = ρ₂(iˡ)·ρˡ₂(A)ᵀ, so the
   normal form reached by refining the adjoint carries an extra factor ρ₂(i) = 11 when l is odd. The
   authors' Haskell comment (and the constant `case_ivt_2`) omit it; `test_refine_ivt` prints its
   result instead of asserting it, which is why this was invisible. The synthesis algorithm itself is
   unaffected.

## Reference material

The authors' Haskell implementation and dataset (github.com/onestruggler/Kopt) were used as the
reference: `Kopt.hs` (the algorithm), `U4Di.hs` (lde, residues, gate matrices) and
`experiment_data.dat`. The Haskell is written against the `newsynth` library, whose Agda port is in
`Quantum/Synthesis/` in this repository, so the correspondence is close to line by line.
