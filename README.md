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
  and that the norms of ℤ[√2] and ℤ[i] are multiplicative.

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

## Denominator exponents

newsynth's class `DenomExp` factors out the least power of 1/√2 from
an element of 𝔻[√2], 𝔻[ω], ... (e.g. `denomexp`, `denomexp-decompose`).
Here the class is generalized to other bases: `DenomExp[ δ ] A` for a
base δ ∈ ℤ[ω], written as an ordinary expression, and `DenomExp` is
`DenomExp[ √2 ]`, so the newsynth class name and functions (`denomexp`,
`denomexp-factor`, `denomexp-decompose`, `showsPrec-DenomExp`) are
unchanged. There are instances for the divisors of 2:

| ring | bases |
|---|---|
| 𝔻 | 2 |
| 𝔻[√2] | √2, 2 |
| 𝔻[i] | 1 + i, 2 |
| 𝔻[√2,i] | √2, 2, 1 + i |
| 𝔻[ω] | √2, 1 + i, 1 + ω, 2 |

and for pairs, lists, vectors and matrices of these, for every base.

```agda
open import Data.Product.Base using (_,_)

_ : denomexp[ 1 + ω ] (DOmega ∋ ½) ≡ 4
_ = refl
_ : denomexp-decompose[ 1 + i ] (DComplex ∋ ½) ≡ (i , 2)
_ = refl
_ : showsPrec-DenomExp[ 2 ] {DOmega} {ZOmega} 0 (√½ ^ 3 * (1 + ω)) ≡ "half^2 * Omega (-1) 1 1 1"
_ = refl
```

Instances for further bases can be written by hand, or built with
`denomexp-by-search` (see `Test/DenomExp.agda` for a base 1 - i).
Unlike in newsynth, the fields of the class are named `denomexp-of`
and `denomexp-factor-of`, so an instance is defined as
`X .denomexp-of a = ...` (its type can still be written `DenomExp X`).
Asking for a base that has no instance is a type error; for 𝔻, which
has a single instance, it reads like `0 !=< 1 of type ℕ`.

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
