# ABTopos — Refactoring Report

## Summary

This report documents the structural refactoring performed on the ABTopos project,
merging content from the `reuse-merge/` directory into the main `ABTopos/` module
hierarchy.

## What was done

### 1. Walsh–Gauss Spectral Theory (`ABTopos/Spectral/WalshGauss.lean`)

**Merged from:** 5 variants in `reuse-merge/ABTopos_Spectral_WalshGauss(1)-(5).lean`
and 4 variants in `reuse-merge/RequestProject_ABSpectralCollapse(0)-(3).lean`

The best version (variant 5) was selected as the canonical file. This version
provides **genuine proofs** for several formerly-sorry'd declarations:

| Declaration | Status Before | Status After |
|---|---|---|
| `AbsTrace` | `sorry` (definition) | ✅ Defined via `Algebra.trace (ZMod 2) 𝔽` |
| `χ_add` | `sorry` | ✅ Proven via ZMod 2 exponent arithmetic |
| `χ_addChar` | missing | ✅ Constructed as `AddChar 𝔽 ℂ` |
| `χ_addChar_ne_one` | missing | ✅ Proven via `Algebra.trace_ne_zero` |
| `χ_orthogonality` | `sorry` | ✅ Proven via `AddChar.sum_eq_zero_of_ne_one` |
| `stickelberger_norm` | `sorry` | ✅ Proven (full Gauss sum norm computation) |
| `walsh_gauss_decomposition` | `sorry` | ✅ Proven (existential decomposition) |
| `walsh_parseval` | partial proof | ✅ Proven (character orthogonality) |
| `fourier_triple_identity` | `sorry` | ✅ Proven (Fubini + orthogonality) |
| `gauss_norm` | derived from sorry | ✅ Now sound (derived from stickelberger_norm) |

**Remaining sorry count:** 7 (down from 13), all deep finite field results:
- `kasami_apn` (Kasami APN theorem)
- `apn_fourth_moment_bound` (APN fourth-moment bound)
- `cauchy_schwarz_rigidity` (Cauchy–Schwarz flatness)
- `ab_spectral_collapse` (AB spectral collapse main theorem)
- `ab_delta_hat_spectrum` (deltaHat spectrum collapse)
- `delta_card` (|Δ| = 2^{n-1})
- `combined_identity_ab` (combined identity)

### 2. APN Conjectures (`ABTopos/Conjectures/APN.lean`)

**Fix applied:** Added missing characteristic-2 hypothesis `(hchar2 : ∀ x : G, x + x = 0)`
to `apn_image_size` and `apn_half_space_decomposition`. The original formulation was
**unprovable** without this hypothesis (counterexample exists in groups of characteristic ≠ 2).

| Declaration | Status Before | Status After |
|---|---|---|
| `differentialFibre_even` | missing | ✅ NEW — proven (fixed-point-free involution) |
| `apn_image_size` | `sorry` | ✅ Proven (fibre counting + char 2 pairing) |
| `apn_half_space_decomposition` | derived from sorry | ✅ Now sound |

### 3. New Module: Derived Counting (`ABTopos/Bridge/DerivedCounting.lean`)

**Merged from:** `reuse-merge/ABTopos_Bridge_DerivedCounting(1).lean`

This module replaces the original **definitional** m-tuple counting formula
with a **computational** one, making the bridge theorems genuine mathematical
results rather than tautologies.

Key contents (all fully proven, zero sorry):
- `computeKernelCount` — actual count of kernel tuples
- `computeMTupleCountFn` — computational count for a function
- `computeKernelCount_eq_card_pow` — formula |α|^{m-1}
- `DerivedSpectralTopos` — spectral topos with genuine counting
- `genuine_bridge_boolean` — non-tautological bridge theorem
- `derived_exponent_match` — p-valued / Boolean exponent agreement

### 4. New Module: Moment Conjectures (`ABTopos/Spectral/MomentConjectures.lean`)

**Merged from:** `reuse-merge/ABTopos_Spectral_MomentConjectures.lean`

Formalizes conjectures C₁–C₁₁ from the spectral moment theory (all fully proven):
- `three_valued_moment_general` — general m-th moment decomposition
- `three_valued_even_moment` / `three_valued_odd_moment` — parity splitting
- `parseval_three_valued` — Parseval as second moment
- `moment_recurrence` — M_{m+2} = c² · M_m
- `support_eq_sPos_add_sNeg` — spectral support count
- `generalized_moment_count_duality` — moment-count duality
- `κ_recurrence` — κ counting recurrence
- `kasami_spectral_chain` — full spectral collapse chain
- `carrier_partition` — carrier three-way partition

### 5. New Module: Dual Topological Theory (`ABTopos/Spectral/DualTopological.lean`)

**Merged from:** `reuse-merge/DualTopologicalConjectures(2).lean`

**Fix applied:** Removed broken imports (`HomotopySpectral`, `DualitySymmetry`)
that referenced nonexistent modules. The file is self-contained.

Key contents (all fully proven, zero sorry):
- `RealSpectrum` structure with bent/diversity/entropy analysis
- `deformationIndex` — cohomological deformation measure δ ∈ [0,1)
- Sheaf-theoretic local diversity bounds
- `spectralEntropy` / `normalizedEntropy` — information-theoretic analysis
- `SpectralState` trichotomy (crystalline/fluid/stochastic)
- `SymmetricSpectrum` temporal analysis
- `ExtendedDecomposition` rigid/residual splitting

## Files NOT merged (with reasons)

| File | Reason |
|---|---|
| `ABTopos_Bridge_PNBoolean.lean` | Identical to existing `ABTopos/Bridge/PNBoolean.lean` |
| `ABTopos_Candidates_*.lean` | Minor diffs only (extra proof arguments), existing versions already compile |
| `ABTopos_Conjectures_APN(1).lean` | Variant of APN with minor differences, merged corrections instead |
| `ABTopos_Conjectures_NewAB.lean` | Near-identical to existing `ABTopos/Conjectures/NewAB.lean` |
| `ABTopos_Spectral_Foundations(2)/(3)` | Content subsumed by improved WalshGauss.lean |
| `ABTopos_Spectral_MTupleCount(1)` | Minor variant of existing MTupleCount.lean |
| `RequestProject_ABSpectralCollapse(0)-(3)` | 4 variants subsumed by WalshGauss.lean |
| `RequestProject_LinearizedPoly_KasamiKernel.lean` | Imports nonexistent modules (`RequestProject.LinearizedPoly.Defs/Kernel`) |
| `RequestProject_QuadFormGF2_KasamiQF.lean` | Imports nonexistent modules (`RequestProject.Kasami.*`, `RequestProject.QuadFormGF2.*`) |

## Axiom Audit

All proven declarations use only standard axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

No custom axioms, `@[implemented_by]`, or `Lean.ofReduceBool` were introduced.

## Project Structure (Post-Refactoring)

```
ABTopos/
├── Bridge/
│   ├── Duality.lean           (unchanged)
│   ├── DerivedCounting.lean   ★ NEW — genuine bridge theorems
│   ├── PNBoolean.lean         (unchanged)
│   └── RosettaStone.lean      (unchanged)
├── Candidates/
│   ├── ABCandidates.lean      (unchanged)
│   ├── Discovery.lean         (unchanged)
│   ├── KasamiInduction.lean   (unchanged)
│   ├── RigidCandidates.lean   (unchanged)
│   └── RigidityDetector.lean  (unchanged)
├── Category/
│   └── APNFunctions.lean      (unchanged)
├── CodingTheory/
│   └── BinaryCode.lean        (unchanged)
├── Conjectures/
│   ├── APN.lean               ★ FIXED — char 2 hypothesis + proofs
│   ├── NewAB.lean             (unchanged)
│   └── NewAPN.lean            (unchanged)
├── Foundation/
│   ├── ElemTopos.lean         (unchanged)
│   └── TypeTopos.lean         (unchanged)
├── Spectral/
│   ├── DualTopological.lean   ★ NEW — spectral state classification
│   ├── KasamiCIC.lean         (unchanged)
│   ├── KasamiCollapse.lean    (unchanged)
│   ├── MomentConjectures.lean ★ NEW — moment theory C₁–C₁₁
│   ├── MTupleCount.lean       (unchanged)
│   ├── SpectralObject.lean    (unchanged)
│   └── WalshGauss.lean        ★ IMPROVED — 6 sorry→proven
└── Tests/
    ├── CategoryTheory.lean    (unchanged)
    └── Sanity.lean            (unchanged)
```

## Sorry Summary

| File | Before | After | Δ |
|---|---|---|---|
| `Spectral/WalshGauss.lean` | 13 | 7 | -6 |
| `Conjectures/APN.lean` | 1 | 0 | -1 |
| **Total** | **14** | **7** | **-7** |

The 7 remaining sorries are all deep results in algebraic number theory and
finite field theory (Kasami APN property, fourth-moment bounds, spectral collapse).
These represent genuine open formalization challenges rather than missing scaffolding.
