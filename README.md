# EucDomain

Gaussian integers as a Euclidean domain in Agda, and an Agda port of
the Haskell library [newsynth](https://hackage.haskell.org/package/newsynth)
(N. J. Ross and P. Selinger: exact and approximate synthesis of
Clifford+T quantum circuits), built on a common ring framework that
overloads operators and constants with instance arguments.

Requires Agda 2.8.0 and the Agda standard library 2.4 (see
`EucDomain.agda-lib`). `agda Everything.agda` type checks everything.

## Contents

**Euclidean domains** (the original content of this repository)

1. `EuclideanDomain` gives the definition of Euclidean Domain (ED).
2. `GauInt.EucDomain` shows Gaussian Integers form an ED.
3. `Integer.EucDomain2` defines the integer division that allows
   negative reminder. It gives a more precise estimation of the
   reminder.

**The ring framework** (following newsynth's `Quantum.Synthesis.Ring`)

- `Typeclasses`: the type classes, as records used with instance
  arguments: `SemiRing`, `Ring` (`+ * - ^`), `DecEq` (`≟ ==`),
  `DecOrd` (`≤ <`), `NonZeroTypeclass`, `DivMod` (`/ %`),
  `Fractional` (`⁻¹`), `Rank`, `HalfRing` (`½`), `RootTwoRing` (`√2`),
  `RootHalfRing` (`√½`), `ComplexRing` (`i`, `+i`, `-i`), `OmegaRing`
  (`ω`), `Adjoint` (`adj`, `†`), `Adjoint2` (`adj2`, `•`),
  `NormedRing`, `Floor`, `Floating`, `ToRational`, `Show`.
- `Instances`: instances for ℕ, ℤ, ℚ and Float.
- `Literals`: overloaded numeric literals (see below).
- `Quantum.Synthesis.Ring`: the rings of newsynth: ℤ₂, the dyadic
  fractions 𝔻 = ℤ[½], and the type formers `A [√2]`, `A [i]`, `A [ω]`
  with all their instances, e.g. `ℤ [√2]`, `𝔻 [√2] [i]`, `ℚ [ω]`
  (aliases `ZRootTwo`, `DRComplex`, `QOmega`, `ℤ[√2]`, `𝔻[ω]`, ...).
- `Quantum.Synthesis.Ring.Properties`: proofs that all these rings
  are commutative rings (stdlib `IsCommutativeRing`), generically for
  `A [√2]`, `A [i]`, `A [ω]` over any commutative ring A, and for
  ℤ₂ and 𝔻; that `adj` and `adj2` are involutive ring automorphisms;
  and that the norms of ℤ[√2], ℤ[i], and ℤ[ω] are multiplicative.

The Gaussian integers are `𝔾 = ℤ [i]` of the framework, with
`a + b i` a pattern synonym for `Cplx a b`, so the ring operations,
constants and conjugation of 𝔾 are the generic ones, and the proven
division of `GauInt.EucDomain` is the `DivMod` instance used by
newsynth's Euclidean algorithms for ℤ[i].

**The newsynth port** (`Quantum.Synthesis.*`, one Agda module per
Haskell module, Haskell `snake_case` names become `kebab-case`)

| Agda module | contents |
|---|---|
| `Random` | exact port of `System.Random` from random-1.1 (the version newsynth uses) |
| `EuclideanDomain` | Euclidean algorithms for ℤ, ℤ[i], ℤ[√2], ℤ[ω] |
| `StepComp` | step-counting (coinductive) computations |
| `Diophantine` | solving t†t = ξ in ℤ[ω] (factoring, square roots mod p) |
| `Matrix` | vectors and matrices indexed by their dimensions |
| `Clifford`, `CliffordT` | Clifford group, Matsumoto–Amano normal forms, exact single-qubit synthesis |
| `MultiQubitSynthesis` | exact multi-qubit synthesis (Giles–Selinger) |
| `ArcTan2`, `ToReal`, `SymReal`, `QuadraticEquation` | real number support; symbolic reals and their parser |
| `GridProblems` | one- and two-dimensional grid problems |
| `GridSynth`, `Newsynth` | approximate synthesis of z-rotations (Ross–Selinger) |
| `EulerAngles`, `RotationDecomposition`, `LaTeX` | utilities |

`Data.Number.FixedPrec` ports the Haskell package fixedprec
(arbitrary precision real numbers `FixedPrec e`, with e decimal
digits; the precision is a term, so newsynth's `dynamic_fixedprec`
trick is not needed). `Programs.Gridsynth` is the `gridsynth` command
line program.

All modules are `--safe` except `Programs.CommandLine` and
`Programs.Gridsynth` (FFI for stderr and the clock). Recursion that
is not structural in Haskell uses explicit fuel (always more than
enough) or coinduction; functions that call `error` in Haskell return
a `Maybe` or a documented default. Deviations from Haskell are listed
at the top of each module.

## Denominator bases

`Typeclasses.Properties` proves successor, addition, product and inverse
laws for the fast-power evaluator under explicit commutative-monoid laws,
and preservation of powers by multiplicative maps. The evaluator retains
its original branch order for inexact carriers.
`Quantum.Synthesis.Ring.Properties.Dyadic` also proves denominator rescaling,
the smart constructor's exponent bound, and exact recovery of a dyadic value
from its integer numerator at any sufficient denominator bound.

`Quantum.Synthesis.Ring.DenomExp Base A` computes a least denominator
exponent and multiplies by a power of the selected base. The tag `Base`
allows several denominator conventions on the same carrier:

```agda
denomexpBy SqrtTwoBase (DRootTwo ∋ ½)  -- 2
denomexpBy TwoBase     (DRootTwo ∋ ½)  -- 1
denomexp-factorBy TwoBase (Dyadic ∋ ½) 3  -- 4
denomexp-decomposeBy {Dyadic} {ℤ} TwoBase (dyadic 1 3)  -- (1 , 3)
```

The existing `denomexp`, `denomexp-factor`, `denomexp-decompose` and
default printing retain the √2 convention. Explicit class constraints
now take a base parameter, e.g. `DenomExp SqrtTwoBase DOmega`.
Base-2 instances are supplied for `Dyadic`, `DRootTwo` and `DOmega`.
`OnePlusIBase` selects 1+i on `DComplex`, `DRComplex` and `DOmega`;
`OnePlusOmegaBase` selects 1+ω on `DOmega`. For example:

```agda
denomexpBy OnePlusIBase     (DComplex ∋ ½)  -- 2
denomexpBy OnePlusOmegaBase (DOmega   ∋ ½)  -- 4
```

These instances multiply by the actual complex base, including its phase.
For 1+i on dyadic Gaussian numbers, clearing powers of 2 followed by a
Gaussian parity check gives the least exponent. `DRComplex` applies that
calculation separately to the coefficients of 1 and √2. On `DOmega`,
1+i = ω√2 has the same exponent as √2 because ω is an integral unit.
For δ = 1+ω, δ² = √2·ω(1+√2), and ω(1+√2) is an integral unit.
If the least √2 exponent is k, the δ exponent is 2k or 2k−1: the latter
applies when the cleared numerator's coefficient sum is even. Integral
inputs have exponent zero.

The distinguished whole ring matters: `DRComplex` uses ℤ[√2,i], whereas
`DOmega` uses ℤ[ω]. Thus ω has 1+i exponent 1 in the former and 0 in the
latter. The 1+ω instance is supplied on `DOmega`, whose whole ring contains
that base. `Test.Ring` checks the unit identities and compares the new
exponents against independent multiplication and integrality checks,
including every smaller exponent on finite coefficient samples.

Pairs, lists, vectors and matrices preserve the selected base, take the
maximum entry exponent (zero when empty), and scale every entry.
The complex lift applies a coefficient-ring base to both coordinates;
the 1+i instances above instead mix coordinates explicitly.
To avoid overlapping instance search, `DenomExpCplx` is a reusable builder,
with automatic instances registered for `SqrtTwoBase` and `TwoBase`.
Clients adding another coefficient-ring base can register that builder
as an instance for their specific tag.

To add a base, declare a tag type and an instance defining the two
`DenomExp` fields. No central enumeration needs changing. `Test.Ring`
defines a base-4 instance and `Test.Matrix` checks that it lifts through
vectors and matrices. As before, this operational interface has no law
fields: instance authors must justify minimality and denominator clearing
relative to the chosen `WholePart` instance.

For explicit-base rendering, `showsPrec-DenomExpBy` takes an inverse-base
expression (e.g. `"half"`), and `showlatex-denomexpBy-p` takes a base
expression (e.g. `"2"`). Parenthesize compound expressions as needed.

## Overloading

Operators are overloaded with instance arguments, e.g. `_+_ : {{SemiRing A}} → A → A → A`.
Constants are overloaded in the same way, e.g. `i`, `ω`, `√2`, `½`.
After `open import Literals`, numeric literals are overloaded too:

```agda
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Instances
open import Literals
open import Quantum.Synthesis.Ring

_ : (ZOmega ∋ ω ^ 8) ≡ 1
_ = refl
_ : (ZComplex ∋ -i * +i) ≡ 1
_ = refl
_ : (DRComplex ∋ ω ^ 2) ≡ i
_ = refl
_ : (QRootTwo ∋ 1 / (1 + √2)) ≡ -1 + √2
_ = refl
```

Some design points (see the comments in `Typeclasses` and `Literals`):

- Each ring type has its own `Number`/`Negative` instances instead of
  one generic `{{Ring A}} → Number A`, because Agda does not discard an
  overlapping candidate whose own instance arguments cannot be found.
  Code over an abstract ring `A` writes `open LiteralsFor A`.
- Literal overloading is opt-in: in a module that has it, every ℕ
  literal is elaborated through instance search, which breaks ring
  solver calls like `solve 1 ...` (the arity is needed too early).
  The proof modules therefore don't open `Literals`.
- The only superclass chains are `SemiRing ← Ring` and
  `NonZeroTypeclass ← DivMod ← Fractional`, to avoid ambiguous
  instance search. A field is a Euclidean domain with remainder 0, so
  `/` means the same thing everywhere.
- The name `i` clashes with the notation `a + b i`; modules using that
  notation hide `i`.

## Algebraic maps

`Quantum.Synthesis.Ring.Properties.Hom` provides instance-based
`IsRingHom` (addition, multiplication, zero, one, negation) and
`IsMultiplicativeHom` (multiplication and one). Ring homomorphisms also
preserve subtraction; `MultiplicativeLaws.f-^` proves preservation of the
operational fast power. `compose-ring` and `compose-multiplicative` compose
maps between different carriers. `toRingHomomorphism` and
`toMonoidHomomorphism` expose standard-library morphism structures.

The existing `adj-*` and `adj2-*` proofs give involutive scalar ring
automorphisms. `Hom.Laws.isRingHom` converts their endomorphism component
to a full ring homomorphism. Ready-made `adj-isRingHom-ZComplex`,
`adj-isRingHom-DComplex`, `adj-isRingHom-ZOmega`, and
`adj-isRingHom-DOmega` live in `Quantum.Synthesis.Ring.Properties`.
Matrix adjoints reverse multiplication order and are not covered by these
scalar ring-homomorphism statements.

The extension property modules prove `lift-Cplx-isRingHom`,
`lift-RootTwo-isRingHom`, and `lift-Omega-isRingHom` for constant-coefficient
embeddings over any commutative base ring. `mapCoefficients-Cplx-isRingHom`
lifts any coefficient ring homomorphism to the complex extensions.
`norm-isMultiplicativeHom-ZComplex`, `-ZRootTwo`, and `-ZOmega` package the
integer-valued number-theoretic norms. These are multiplicative maps;
no additivity of norms is asserted. `Test.RingProperties` checks composition,
standard-library interoperability, and norm preservation of powers.

## Scalar arithmetic modules

The reusable scalar theory used by Kopt lives here and has no dependency on
Kopt matrices, circuits, synthesis, or its source tree:

| Modules | Content |
| --- | --- |
| `GauInt.Algebra` | Gaussian ring laws, sparse solver, embeddings, adjoint and norm homomorphisms, units |
| `GauInt.Gamma`, `GauInt.Gamma.Division`, `GauInt.Gamma.Integer` | Powers and divisibility by `1+i`, exact quotient, embedded-integer divisibility |
| `GauInt.Gamma.Congruence`, `NormCongruence`, `ImagCongruence` | Decidable congruence modulo gamma powers and its norm/imaginary consequences |
| `GauInt.Gamma.Residue` | Canonical eight-element encoding modulo gamma cubed, with arithmetic correctness |
| `GauInt.Parity`, `GauInt.NormParity`, `GauInt.Units` | Gaussian parity, norm parity, and classification of the four units |
| `Integer.Sum`, `Integer.Congruence`, `Integer.Residues`, `Integer.Parity`, `Integer.Squares` | Finite sums, congruences, residue bounds, Boolean parity, and square bounds |
| `Natural.Sum` | Finite natural sums and permutation/ordering laws |
| `Quantum.Synthesis.Ring.Properties.DyadicComplex` | Integer and Gaussian embeddings into dyadics, inverse-gamma scaling, denominator clearing |
| `Finite.Check` | Generic finite proof-producing decision helpers used by residue certificates |

`GauInt.Units.phaseToZI` is the scalar enumeration `1, i, -1, -i`.
It is independent of circuit syntax. Integer parity and square bounds also
have no Gaussian or matrix dependency. Matrix factorization and circuit
optimality remain in the application. `Everything.agda` checks every module
listed here against this library and the standard library alone.

## Certified gamma denominator extraction

`Quantum.Synthesis.Ring.Properties.GammaDenominator` proves that the existing
`OnePlusIBase` exponent on `DComplex` clears denominators for every scalar.
`denominator-factor-whole-at` certifies exact integer extraction at that
exponent or any larger one; `denominator-reconstruct` proves the round trip.
The proof covers common-denominator alignment, parity cancellation and
zero exponents. `align-dyadic` exposes the existing alignment calculation
without changing its algorithm. `Typeclasses.Properties.Powers.cancel-step`
provides the generic invertible-base cancellation used by the proof.

`denominator-minimal` proves that the operational exponent is least among
all powers that clear the scalar to Gaussian integers. The proof uses the
canonical dyadic numerator to rule out two further gamma factors after
alignment, and the parity test to determine whether one factor cancels.
`Test.GammaDenominator` exercises integral, negative, mixed-denominator and
redundantly scaled inputs, and proves that selected smaller exponents cannot
clear any integer numerator; `Everything.agda` includes both modules.

`Typeclasses.Properties.MappedActions` factors the clearing-transport proof
through abstract source and target carriers. This avoids repeatedly unfolding
dyadic coordinate arithmetic during proof inference. On the development
machine with cached dependencies and a 4 GB Agda heap, checking
`GammaDenominator.agda` took 51.3 s after this refactor versus 161.7 s before.
This is a module typechecking measurement, not a synthesizer runtime benchmark.

## Native matrix laws

`Quantum.Synthesis.Matrix.Properties` supplies entries, tabulation,
extensionality, finite sums, and generic laws for the native column-major
matrix type. `Linear` takes the coefficient ring laws and proves product
associativity, identities and scalar-product rules for rectangular matrices,
including empty and singleton inner dimensions. `Linear.Conjugate` proves
adjoint entry formulas, involution and reversal of matrix products from the
coefficient adjoint automorphism. `Map` lifts a coefficient ring homomorphism
to preservation of native matrix products, identities and scalar multiplication.
When the coefficient map preserves conjugation, it also preserves adjoints and
row Gram matrices. `Linear.Conjugate.gram-scale` proves the norm factor in a
scaled Gram matrix. `Linear.Evaluation` proves agreement of a native left fold
with any semantics satisfying the corresponding identity and product equations.
`Linear.·-cancel` cancels scaling by a unit; `Map.Conjugate.gram-unitary`
transfers a cleared Gram equation through an embedding when its scale is a unit.

The generic matrix theory is adapted from the independently developed
`Kopt.Algebra.Linear` at Kopt revision `a0b62a0`; it has no Kopt dependency.
`Test.Matrix` includes an empty-product embedding check and a noncommuting
example that distinguishes the matrix adjoint law from scalar multiplicativity.

## Testing

`Test/*.agda` contain checks by evaluation (`refl`); `Test/*Run.agda`
are compiled programs whose output was compared with the Haskell
implementation. `Test/gridsynth-compare.sh` runs the Agda and the
Haskell `gridsynth` programs on 85 argument sets (all options, error
cases, precisions up to 200 digits) and compares stdout, stderr and
exit codes byte for byte; all 85 are identical. Since the random
number generator is an exact port, the same seed (`-r`) gives the
same circuit.

Building the program: `agda --compile Programs/Gridsynth.agda`, then e.g.

```
$ ./Gridsynth pi/8 -d 20 -r 1 -s
```

The compiled Agda program is about 3× slower than the Haskell one
(e.g. 0.4 s vs 0.1 s for `pi/128 -d 50`, 1.8 s vs 0.7 s for
`pi/128 -d 200`); the remaining gap is mostly per-operation overhead
of stdlib's ℤ and ℚ arithmetic.
