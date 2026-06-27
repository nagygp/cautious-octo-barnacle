# `ConjecturesMTupleTripleCount` — the m-tuple / triple-count conjecture library

This folder is a **self-contained, runnable Lean library**. It is wired into the
repository's root `lakefile.toml` as the library target

```
ConjecturesMTupleTripleCount   (srcDir = "conjectures-mtuple-triple_count")
```

so it builds with

```bash
lake build ConjecturesMTupleTripleCount
```

Every module lives under `ConjecturesMTupleTripleCount/` and imports only
`Mathlib` together with other `ConjecturesMTupleTripleCount.*` modules. The build
is **`sorry`-free**.

## What the library is about

The library investigates the **m-tuple / triple count** of APN (and specifically
**Kasami**) derivatives over `GF(2ⁿ)`. For `f : F → F`, a nonzero shift `a` and a
coefficient tuple `c : Fin m → F`, the derivative is `Δf_a(x) = f(x+a) + f(x)`,
and one studies how many ways `m` derivative values combine to zero (`preCount`),
together with the induced image count (`imgCount`).

It establishes two complementary things:

1. **A disproof.** The *unconditional* conjecture "for nonzero coefficients
   `imgCount m f a c = 2^{(m−1)n − m}`" is **false**; it only holds behind a
   `FlatSpectrum` hypothesis that is unsatisfiable for odd `n`. `MTuple/Disproof.lean`
   gives two machine-checked refutations (`disproof_m2`, `m_tuple_count_two_false`,
   `triple_count_cube_false`).
2. **A conditional, honest account + a roadmap.** `MTuple/Count.lean` rebuilds the
   count theory `sorry`-free behind the satisfiable `Vanish` hypothesis
   (`imgCount_of_vanish`, and its `m = 3` specialization `triple_count_of_vanish`),
   and `Foundations/` develops the layered **"Kasami is Vanish"** program that aims
   to *discharge* `Vanish` for the Kasami map — via Fourier analysis, the
   cross-correlation distribution, weight-divisibility (Ax–Katz / McEliece) and
   additive-energy / fourth-moment estimates.

## Entry points

There is no single `Headlines` module; the headline statements are:

| Result | Module |
| ------ | ------ |
| unconditional triple/m-tuple count is **false** | `MTuple.Disproof` |
| conditional count `imgCount … = 2^{(m−1)n − m}` (resp. `2^{2n−3}`) | `MTuple.Count` (`imgCount_of_vanish`, `triple_count_of_vanish`) |
| cube / Kasami-`k=1` triple count and admissibility | `Foundations.KasamiCrossCorrelation` |
| general-`k` Kasami triple count (conditional) | `Foundations.KasamiMTupleCount` |
| explicit `Vanish` discharge as a sign correlation | `Foundations.KasamiVanishSign` |

`MTuple.lean` is a small aggregator re-exporting `MTuple.Count` and
`MTuple.Disproof` (so `import ConjecturesMTupleTripleCount.MTuple` brings the whole
m-tuple development into scope).

## Module DAG (low level → high level)

Arrows point from a module to the modules it imports (intra-library only).

### 1. Shared Kasami spine

Identical in shape to the sibling library's spine:

```
APN.Defs ─► APN.CharTwoBasics
APN.Defs ─► Walsh.Transform ─► Walsh.Moments ─► Walsh.WalshAB ─► Walsh.WalshDivisibility
FiniteField.AutBase ─► FrobAlg ─► {TraceNorm, ExpArith}; Lemma31, BareLemma31Skeleton ─► AdjointBij ─► Thm32
Walsh.WalshDivisibility, APN.Defs ─► Support.AutocorrQuadratic
Core.KasamiAPN ─► KasamiEvenK; … ─► KasamiMCM ─► KasamiWalshDiv; … ─► Core.KasamiAB
Core.KasamiAB, DiffUniformity.DifferentialUniformity ─► DiffUniformity.KasamiDiffUniformity
```

| Directory | Role |
| --------- | ---- |
| `APN/`, `FiniteField/`, `Walsh/`, `Support/`, `Core/`, `DiffUniformity/` | the finite-field / Walsh / Kasami collision machinery that proves the Kasami map APN & AB (the foundation everything else builds on). |

### 2. `MTuple/` — the counts and the disproof

```
Walsh.Moments ─► MTuple.Count ─► MTuple.Disproof
MTuple.Count, MTuple.Disproof ─► MTuple   (aggregator)
```

| Module | Role |
| ------ | ---- |
| `MTuple.Count` | `sorry`-free count theory: `deriv`, `preCount`, `imgCount`, `Vanish`, the autocorrelation split, `preCount_of_vanish`, `imgCount_of_vanish` and the triple specialization `triple_count_of_vanish`. |
| `MTuple.Disproof` | refutations of the unconditional conjecture; APN-ness of the cube map; the cube triple count is false for odd `n`. |
| `MTuple` | aggregator re-exporting the two above. |

### 3. `Foundations/` — the "Kasami is Vanish" roadmap

Fourier / spectral base:

```
AddCharCount ─► Fourier
AddCharCount, MTuple.Count ─► ChiBridge
ChiBridge, Fourier ─► WalshTransform ─► WienerKhinchin
ValueDistribution, WalshTransform ─► ABSpectrum
ABSpectrum, Core.KasamiAB ─► KasamiSpectrum
MTuple.Disproof, KasamiSpectrum ─► SpectralSum
```

Cross-correlation distribution and its value set:

```
SpectralSum, MTuple, Support.AutocorrQuadratic ─► KasamiCrossCorrelation ─► {CubeMTupleCount, KasamiMTupleCount}
CubeMTupleCount ─► KasamiCrossCorrelationGeneralK ─► KasamiCrossCorrelationTable ─► KasamiCrossCorrelationValueSet
KasamiCrossCorrelationValueSet, ValueDistribution ─► KasamiWeightEnumerator
KasamiCrossCorrelationValueSet, SpectralSum ─► KasamiVanishSign
```

Weight-divisibility (Ax–Katz / McEliece and 2-adic) route:

```
Walsh.Transform ─► QuadraticGaussSum ─┐
KasamiCrossCorrelationValueSet, QuadraticGaussSum, Support.AutocorrQuadratic ─► KasamiTwoAdicValuation
KasamiWeightEnumerator ─► KasamiPlessMoments
KasamiAxKatz ─► AK2 ─► AK3 ─► AK3a ─► AK3b ─► AK3c
AK3 ─► AK3d ─► AK3e ;  AK3b, KasamiTwoAdicValuation ─► AK4 ;  AK3d ─► AK4a
```

Additive-energy / fourth-moment route:

```
KasamiPlessMoments, KasamiCrossCorrelationGeneralK, Core.KasamiAB ─► KasamiAdditiveEnergy
KasamiAdditiveEnergy ─► BE2 ─► BE3 ─► BE3a ─► BE3b ─► BE3c
```

| Group | Modules | Role |
| ----- | ------- | ---- |
| Fourier base | `AddCharCount`, `Fourier`, `ChiBridge`, `WalshTransform`, `WienerKhinchin`, `ValueDistribution`, `ABSpectrum`, `KasamiSpectrum`, `SpectralSum` | additive characters, the discrete Fourier / Walsh transform, Parseval / Wiener–Khinchin, and the Kasami Walsh spectrum / spectral-sum reformulation of `Vanish`. |
| Cross-correlation | `KasamiCrossCorrelation`, `CubeMTupleCount`, `KasamiCrossCorrelationGeneralK`, `KasamiCrossCorrelationTable`, `KasamiCrossCorrelationValueSet`, `KasamiMTupleCount`, `KasamiVanishSign`, `QuadraticGaussSum` | the explicit Kasami cross-correlation, its three-valued value set, the resulting triple counts and the explicit `Vanish` discharge. |
| Weight enumerator | `KasamiWeightEnumerator`, `KasamiPlessMoments` | the Kasami code weight enumerator and its Pless power moments. |
| Ax–Katz route | `KasamiAxKatz`, `KasamiAxKatzAK2`, `…AK3`, `…AK3a`–`…AK3e`, `…AK4`, `…AK4a`, `KasamiTwoAdicValuation` | the Ax–Katz / McEliece weight-divisibility sub-path (`2^{(n+1)/2} ∣ R(s)`) and the 2-adic valuation input. |
| Additive energy | `KasamiAdditiveEnergy`, `…BE2`, `…BE3`, `…BE3a`–`…BE3c` | the fourth-moment / additive-energy sub-path toward the same divisibility input. |

## Status

`lake build ConjecturesMTupleTripleCount` succeeds and the library is
**`sorry`-free**. The disproof and the conditional (`Vanish`-based) count theory
are complete; the `Foundations/` layers form a connected, fully-proved chain of
the "Kasami is Vanish" program.
