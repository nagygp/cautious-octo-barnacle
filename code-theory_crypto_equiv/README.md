# `CodeTheoryCryptoEquiv` — coding theory ↔ cryptography equivalence library

This folder is a **self-contained, runnable Lean library**. It is wired into the
repository's root `lakefile.toml` as the library target

```
CodeTheoryCryptoEquiv   (srcDir = "code-theory_crypto_equiv")
```

so it builds with

```bash
lake build CodeTheoryCryptoEquiv
```

Every module lives under `CodeTheoryCryptoEquiv/` and imports only `Mathlib`
together with other `CodeTheoryCryptoEquiv.*` modules — there are no intra-repo
dependencies on the sibling libraries, so this tree can be read or built on its
own.

## What the library is about

The library assembles the **equivalence web** that links three classically
separate subjects:

* **Symmetric-crypto Boolean functions** — APN / AB / differential uniformity of
  power maps over `GF(2ⁿ)`, with the **Kasami** map `x ↦ x^{d(k)}`,
  `d(k) = 2^{2k} − 2^k + 1`, as the worked example;
* **Coding theory** — linear codes, the **MacWilliams identity**, the
  **Delsarte LP bound**, MDS / Reed–Solomon, Plotkin, Gilbert–Varshamov and
  sphere packing;
* **CCZ / EA-equivalence** — the affine equivalence under which differential
  uniformity, APN-ness and AB-ness are invariants (Flystel / Anemoi).

plus two short "variety" bridges: **finite geometry** (MDS codes ↔ arcs) and
**statistical physics** (a weight enumerator = a partition function, MacWilliams
= a high/low-temperature duality), and a **difference-sets** Fourier bridge.

## Entry point

`CodeTheoryCryptoEquiv/Headlines.lean` is the single discoverable entry point for
the cryptographic spine. It re-exports:

| Name (`Kasami.Headlines`)   | Meaning                                                        |
| --------------------------- | ------------------------------------------------------------- |
| `kasami_is_apn`             | Kasami map is APN (every nonzero derivative is ≤ 2-to-1)      |
| `kasami_is_apn_diffUnif`    | same, as differential uniformity exactly 2                   |
| `kasami_is_ab`              | Kasami map is AB (Walsh squares in `{0, 2^{n+1}}`), input-mask form |
| `kasami_is_ab_outputMask`   | AB in the literature-standard output-mask form               |

Standing hypotheses: `1 ≤ k < n`, `gcd(k, n) = 1`, `n` odd.

The coding-theory, geometry, physics and difference-set developments are reached
directly through their own modules (see the maps below); they are not aliased in
`Headlines`.

## Module DAG (low level → high level)

Arrows point from a module to the modules it imports (intra-library only). Two
largely independent strands meet at a few cross-links.

### 1. Cryptographic Kasami spine

```
APN.Defs
  ├─► APN.CharTwoBasics
  └─► Walsh.Transform ─► Walsh.Moments ─┬─► Walsh.WalshAB ─► Walsh.WalshDivisibility
                                        └─► Walsh.ChabaudVaudenay

FiniteField.AutBase ─► FiniteField.FrobAlg ─┬─► FiniteField.TraceNorm
                                            ├─► FiniteField.ExpArith
                                            └─► (… FrobAlg used widely)
FiniteField.Lemma31, FiniteField.BareLemma31Skeleton ─► FiniteField.AdjointBij ─► FiniteField.Thm32

Walsh.WalshDivisibility, APN.Defs ─► Support.AutocorrQuadratic

Core.KasamiAPN ─► Core.KasamiEvenK
Core.KasamiAPN, Core.CrossFormAnalysis, Core.KasamiEvenK ─► Core.KasamiMCM ─► Core.KasamiWalshDiv
Walsh.WalshAB, Core.{KasamiEvenK,CrossFormAnalysis,KasamiWalshDiv} ─► Core.KasamiAB

Core.KasamiAB, DiffUniformity.DifferentialUniformity ─► DiffUniformity.KasamiDiffUniformity
Core.KasamiAB, DiffUniformity.KasamiDiffUniformity ─► Headlines
```

| Directory       | Role |
| --------------- | ---- |
| `APN/`          | APN / derivative vocabulary in characteristic two (`Defs`, `CharTwoBasics`). |
| `FiniteField/`  | finite-field tower: `AutBase`, `FrobAlg`, `TraceNorm`, `ExpArith`, exponent arithmetic, `Lemma31`/`BareLemma31Skeleton`, the adjoint bijection `AdjointBij` and the Dempwolff–Müller permutation `Thm32`. |
| `Walsh/`        | Walsh/Fourier transform (`Transform`), moment method (`Moments`, `WalshAB`, `WalshDivisibility`) and the Chabaud–Vaudenay AB bound (`ChabaudVaudenay`). |
| `Support/`      | `AutocorrQuadratic`, the quadratic-autocorrelation helper for the divisibility step. |
| `Core/`         | the Kasami collision analysis and AB/APN assembly (`KasamiAPN`, `KasamiEvenK`, `CrossFormAnalysis`, `KasamiMCM`, `KasamiWalshDiv`, `KasamiAB`). |
| `Headlines.lean`| single entry point (aliases above). |

### 2. Differential uniformity & CCZ / EA-equivalence

```
DiffUniformity.DifferentialUniformity            (standalone abstract foundation)
DiffUniformity.DifferentialUniformityUpstream    (upstream-candidate foundation)
DiffUniformity.DifferentialUniformityUpstreamSkeleton   (sorry-ed skeleton template)

DifferentialUniformityUpstream ─► CCZEquivalence ─► Flystel ─┐
                                  CCZEquivalence, Flystel ─► CCZEquiv ─┘─► FlystelField
```

| Module | Role |
| ------ | ---- |
| `DifferentialUniformity` | characteristic-free differential-uniformity foundation. |
| `DifferentialUniformityUpstream` | upstream-ready restatement used by the CCZ track. |
| `DifferentialUniformityUpstreamSkeleton` | clean `sorry`-only skeleton/template (placeholder, not proved). |
| `CCZEquivalence` | EA-equivalence invariants — the affine core of CCZ-equivalence. |
| `Flystel`, `CCZEquiv`, `FlystelField` | the open Flystel / Anemoi round as a concrete CCZ instantiation. |

### 3. Coding theory

```
CodingTheory.LinearCode ─┬─► Dual ─► GeneratorParityCheck ─► MDS ─► ReedSolomon
                         ├─► WeightEnumerator ─► (with Dual) MacWilliams ─┐
                         ├─► Krawtchouk ─► KrawtchoukOrthogonality        │
                         ├─► SpherePacking ─► GilbertVarshamov            │
                         └─► Plotkin                                      │
   MacWilliams, Krawtchouk ─► MacWilliamsDistribution ─► DelsarteLP ─► DelsarteBound
```

| Module | Role |
| ------ | ---- |
| `LinearCode` | linear codes, Hamming distance, basic parameters. |
| `Dual`, `GeneratorParityCheck` | dual code and generator/parity-check duality. |
| `WeightEnumerator`, `Krawtchouk`, `KrawtchoukOrthogonality` | weight enumerators and Krawtchouk polynomials. |
| `MacWilliams`, `MacWilliamsDistribution` | the MacWilliams identity and the dual weight distribution. |
| `DelsarteLP`, `DelsarteBound` | Delsarte linear-programming constraints and the LP bound. |
| `MDS`, `ReedSolomon` | Singleton bound, MDS codes, Reed–Solomon codes. |
| `Plotkin`, `SpherePacking`, `GilbertVarshamov` | classical existence/packing bounds. |

### 4. Upstream coding-theory mirror

`Upstream/` is a parallel, dependency-minimal copy of the coding-theory core
(`LinearCode`, `Dual`, `GeneratorParityCheck`, `Krawtchouk`, `WeightEnumerator`,
`SpherePacking`, `MDS`, `ReedSolomon`, `GilbertVarshamov`) intended as a
self-contained candidate for upstreaming to Mathlib. Its own notes are in
`CodeTheoryCryptoEquiv/Upstream/README.md`. It has the same internal shape as
`CodingTheory/` and does not depend on the rest of the library.

### 5. Cross-discipline bridges

```
Walsh.Transform        ─► DifferenceSets.Basic
CodingTheory.MDS       ─► Geometry.Arcs
CodingTheory.{MacWilliams,WeightEnumerator} ─► Physics.PartitionFunction
```

| Module | Role |
| ------ | ---- |
| `DifferenceSets.Basic` | difference sets in `(GF(2ⁿ), +)` and the Fourier/Walsh bridge (Dillon–Dobbertin, Prop. 2). |
| `Geometry.Arcs` | the classical equivalence MDS codes ↔ arcs in projective space. |
| `Physics.PartitionFunction` | weight enumerator as a partition function; MacWilliams as a Kramers–Wannier-type duality. |

## Status

`lake build CodeTheoryCryptoEquiv` succeeds. The crypto spine and the
coding-theory / equivalence results are proved; the only `sorry`s are the
explicit placeholder template `DiffUniformity/DifferentialUniformityUpstreamSkeleton.lean`
(advertised as a `sorry` skeleton in its own header) and one or two clearly
marked stubs. Everything else is complete.
