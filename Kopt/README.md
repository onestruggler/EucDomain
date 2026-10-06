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
| `Kopt.GammaPow` | II | γˡ in ℤ[i], computed with ⌊l/2⌋ multiplications by γ² = 2i (a fast power that can be reasoned about, unlike the framework's `_^_`) |
| `Kopt.Unitary` | IV A | unitarity of a `Matrix 4 4 DComplex` as an explicit hypothesis, and **Lemmas IV.2 and IV.3** at the residue level: the parity counts of the columns and rows of ρˡ₁ |
| `Kopt.Unitary3` | IV A | **Lemmas IV.2 and IV.3 at ρ₂**: the same counting facts one residue digit up, which is the form the refinements of Section IV B are solved against (at positive lde all four ρ₂ inner products vanish) |
| `Kopt.PatternFacts` | IV A | **Lemma IV.1**: every unitary over 𝔻[i] has one of the six patterns, and it has pattern (i) if and only if its lde is 0 |
| `Kopt.MatAdj` | -- | (X·Y)† = Y†·X† and (X†)† = X for 4×4 matrices, which the library does not prove, and therefore that unitarity is closed under products and adjoints |
| `Kopt.CircuitSem` | III C | the 24 Table I permutation circuits and the 256 diagonal circuits implement the matrices they are meant to, keyed on membership in `all-perms` -- which is all the residue search tells its caller about a permutation |
| `Kopt.ResPerm` | IV A | ρₙ commutes with a reindexing of the rows and columns (both are applied entrywise) |
| `Kopt.PermAdj` | III C | G† = G⁻¹ for a generalized permutation, by uniqueness of inverses, and hence left multiplication read as right multiplication by the inverse |
| `Kopt.PermIndex` | -- | the dictionary between the two indexings of a permutation: `Pos`, a datatype, where selection reduces for a variable permutation, and `Tuple4 = ℕ×ℕ×ℕ×ℕ`, where nothing reduces until the permutation is known |
| `Kopt.PermScatter` | III C | multiplying on the left by a permutation matrix permutes the rows (the case `lcomb-unit` does not cover), with the permutation still a variable |
| `Kopt.PermMul` | III C, IV A | P_x·A·P_y is the reindexing `permute-matrix x y A` that the level data records |
| `Kopt.SearchMem` | IV A | the permutations the search returns lie in `all-perms` |
| `Kopt.LevelSound` | IV A–B | **what the level data says about the operator**: for `B = L·A·R`, that B is that reindexing of A, that ρˡ₂(B) and ρˡ₁(B) are the recorded residue matrix and pattern, that B has the lde of A, and that B is unitary. Each of the six cases of Section IV B starts here |
| `Kopt.GateUnitary` | I, III C | every gate, every circuit and every generalized permutation is unitary, hence so is every matrix a descent reaches (`steps-unitary-of`) |
| `Kopt.Synth` | IV B–C | `decrease1-lde`, `synth`, `optimize-gp`, `prkc` (Table II), Cor. IV.8 |
| `Kopt.Properties.*` | II | the proofs of Section II (see below); `Kopt.Properties.Algebra` re-exports them |
| `Kopt.GPData` | III C | the generalized permutations as symbolic permutation/phase data, and the exhaustive check over all 24·256 of them that `gperm-of` returns a circuit implementing each one with ≤ 9 gates, no K gate and ≤ 1 CS gate (used by `Kopt.Optimality` and `Kopt.SynthProperties`) |
| `Kopt.Descent`, `Kopt.Optimality` | V | descents (Def. V.1–V.2), Equation (3), Thm V.9, Cor. V.8/V.10, Remark V.11 |
| `Kopt.NormalForms` | V | the residue enumerations behind Lemmas V.3, V.4 and V.6 |
| `Kopt.OptSteps`, `Kopt.OptPotential`, `Kopt.OptInduction` | V | single descent steps (Remark II.10 for a K gate, invertibility), the Table II potential, and the induction proving Lemma V.7 |
| `Kopt.SynthProperties` | IV | properties of the synthesis algorithm itself |

Tests are in `Test/Kopt*.agda`; the `*Run` modules are compiled programs (`agda --compile`).

## What is proved, and what is checked

Proofs (Agda, `--safe`, no postulates) — Section II:
ρₙ is well defined, sound and injective, and stable under increasing n; the residue arithmetic mod γ²
and mod γ³ (including ρ₂(x†) = ρ₂(x) and ρ₃(x†) = ab(c⊕b)); Lemma II.5 (odd ⟺ odd norm), Lemma II.6
(cancelling γ), Lemma II.7, Lemma II.8 (subadditivity of lde), Lemma II.9 (shifts) and the four
K-action cases of Section II C; and that the `lde` used by the algorithm is the least denominator
exponent (existence and minimality).

Section IV: **Lemma IV.2 and Lemma IV.3** at the residue level (`Kopt.Unitary`) — for a unitary U over
𝔻[i] and a denominator exponent l > 0, every column and every row of ρˡ₁(U) has an even number of odd
entries, and two distinct columns (or rows) are both odd at an even number of positions; at l = 0 the
counts are odd instead. These are the counting facts the paper's proofs rest on (Σ‖wⱼ‖² = ‖w‖² ≡ 0
mod γ together with Lemma II.5). And **Lemma IV.1** (`Kopt.PatternFacts`): every unitary over 𝔻[i]
has one of the six patterns, and it has pattern (i) if and only if its lde is 0. Unitarity is an
explicit hypothesis throughout, because the type `Matrix 4 4 DComplex` contains every matrix and
Lemma IV.1 is false without it (γ⁻¹·1 has lde 1 and pattern (i)).

Section V: Equation (3) (every circuit is an alternating sequence of generalized permutations and K₁
gates with the same K-count), every K-free circuit is a generalized permutation, Remark II.10 (in
particular that a K gate changes the lde by at most one, and that nothing else changes it), Theorem
V.9's upper bound, the Corollary V.8 count bounds, Lemma V.5, Remark V.11, Corollary V.10 with the
corrected constant, and **Lemma V.7** (the complete path descent is K-optimal), proved by induction on
the Table II potential 2·lde(A) − rank(pat A), given Lemmas V.4 and V.6 and unitarity. Lemma IV.1 was
a hypothesis of that induction and is now discharged (`Kopt.OptInduction.lemma-V-7′`,
`cor-V-8-K-optimal″`), and so is unitarity along the descent, so that the two statements
`lemma-V-7″` and `cor-V-8-K-optimal‴` assume only Lemma V.4, Lemma V.6 and `IsUnitary A` —
the paper's hypothesis A ∈ 𝒞𝒞𝒮 — together with the three algorithmic facts about `synth`.

Exhaustively checked by the type checker (these checks are proofs): the 24 Table I circuits, the 256
diagonal unitaries, all 6144 generalized permutations (each synthesized exactly, with ≤ 9 gates, ≤ 1 CS
and no K gate), the residue enumerations behind Lemma V.3 (the achievable ρ₂ normal forms against
all generalized permutations), Lemma V.4 (8064 one-K-gate 1-ascents) and Lemma V.6 (1536 residue steps),
and the combinatorial half of Lemma IV.1 (`Kopt.PatternFacts.pos-check`, `zero-check`): the search of
`lemma-six` is run on every 4×4 matrix over ℤ₂ that the residues of a unitary can be — those with
MᵀM = MMᵀ = 0 that are nonzero, out of the 4096 with even columns, at lde > 0, and the 24 permutation
matrices at lde 0.
Those two checks also establish that the search is *sound*: the two permutations it returns carry the
matrix to the pattern, and the matrix is that pattern permuted back (`level-sound-pos`,
`level-sound-zero`). That is where a proof about the operator the algorithm builds from the level data
has to start, since the level data is all that is known about the permutations. `Kopt.LevelSound` carries
that through to the operator: the two permutations lie in `all-perms`, so Table I applies to them, and
the operator B = L·A·R that the algorithm passes on is the reindexing the level data names, with the
recorded ρˡ₂ and the recorded pattern as its residue matrices, the lde of A, and unitarity.

Checked by execution only: Theorem V.9's lower bound rests on "every two-qubit Clifford needs ≤ 2 K
gates", verified by a BFS producing exactly 46080 elements — the whole Clifford group with phases —
closed under all generators. Corollary V.8's K-optimality is therefore conditional on that and on the
algorithmic facts about `synth`.

Named hypotheses that remain: Lemma V.4 and Lemma V.6 (the two residue-level statements of Section V,
enumerated in `Kopt.NormalForms` but not yet connected to the operators), Lemma IV.4 with Table II
(that each round of `decrease1-lde` lowers the lde — the `Descends`/`Terminates` hypothesis of
`Kopt.SynthProperties`, which is decidable and discharged by evaluation for any concrete operator),
and Section III C (that an operator of lde 0 is a generalized permutation). The hypothesis
`Kopt.OptSteps.StepsUnitary A` — that every matrix reachable from A by a descent step is unitary — is
no longer among them: it is proved in `Kopt.GateUnitary` for every unitary A, from the unitarity of
the gates and of the generalized permutations together with the anti-multiplicativity of `adjoint`
(`Kopt.MatAdj`).

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
