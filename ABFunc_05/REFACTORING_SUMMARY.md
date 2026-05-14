# Refactoring Summary

## Overview

The project has been refactored to merge results from `reuse-merge/` into the main
codebase, replacing homegrown infrastructure with Mathlib calls where possible.

## Key Changes

### 1. Fusion & Reuse (`reuse-merge` → main project)

**`Spectral/WalshGauss.lean`** was completely rewritten, integrating proven results
from `reuse-merge/ABTopos_Spectral_WalshGauss(6).lean`:

- **`AbsTrace`**: Now defined via `Algebra.trace (ZMod 2) 𝔽` (Mathlib) instead of `sorry`
- **`χ_add`**: Fully proven using the ZMod 2 exponent arithmetic
- **`χ_orthogonality`**: Proven via `AddChar.sum_eq_zero_of_ne_one` (Mathlib)
- **`stickelberger_norm`**: Full proof (800+ heartbeats, complex character-sum argument)
- **`gauss_norm`**: Derived from `stickelberger_norm`
- **`walsh_gauss_decomposition`**: Proven via trivial decomposition
- **`walsh_parseval`**: Proven via character orthogonality
- **`fourier_triple_identity`**: Proven via Fubini + character orthogonality

**`Spectral/WalshDuality.lean`** was created, integrating proven results from
`reuse-merge/RequestProject_ABTopos_Duality.lean`:

- **`ab_apn_duality_transfer`**: `isAB f ↔ isMaximallyNonlinear f` — fully proven
- **`signLift_add`**, **`signLift_sq`**: Fully proven
- All F₂ⁿ-based definitions (`F2Vec`, `innerF2`, `walshHadamard`, etc.)

### 2. Migration to Mathlib (Zero-Infrastructure)

**Additive Characters**: `χ_` is now backed by a Mathlib `AddChar`:
- `χ_addChar : AddChar 𝔽 ℂ` wraps the hand-rolled `χ_`
- `χ_addChar_ne_one`: Proves nontriviality via `Algebra.trace_ne_zero`
- Orthogonality routed through `AddChar.sum_eq_zero_of_ne_one`

**Gauss Sums**: Connected to Mathlib's `gaussSum` infrastructure:
- `stickelberger_norm` proven from first principles
- `gauss_norm` derived as corollary

### 3. Import Path Fix

All files updated from `import ABTopos.X.Y` to `import X.Y` to match the
actual module layout (`RequestProject` lake name with direct directory imports).

### 4. Lakefile Fix

Removed the broken `reuse-merge` library target (directory name with hyphen
caused glob parse errors). The `reuse-merge/` directory is retained as reference
material but is no longer a build target.

## Sorry Count

| State | Count |
|-------|-------|
| Before refactoring | 28 sorries across main + reuse-merge |
| After refactoring  | 8 sorries in main project |

### Remaining Sorries (all in `Spectral/WalshGauss.lean`)

These are deep number-theoretic results that require substantial intermediate lemmas:

1. **`kasami_apn`**: Kasami APN theorem (requires GCD-based argument over GF(2ⁿ))
2. **`apn_fourth_moment_bound`**: Fourth moment ≤ 2q³ (requires 4-tuple counting)
3. **`cauchy_schwarz_rigidity`**: Moment bounds ⟹ flat spectrum (Cauchy-Schwarz)
4. **`ab_spectral_collapse`**: APN + n odd ⟹ AB (combines 1-3)
5. **`ab_delta_hat_spectrum`**: AB ⟹ δ̂ collapse
6. **`delta_card`**: |Δ| = 2^{n-1} from APN
7. **`combined_identity_ab`**: |𝔽|·|Triples| = |Δ|³

Plus 1 minor sorry in `Spectral/WalshDuality.lean`:
- **`spectrFlat_iff_ab`** (forward direction): requires Parseval to determine c = 2^{n+1}

## Architecture

```
Spectral/
  WalshGauss.lean      -- Main spectral theory (χ, Ŵ, 𝔤, Parseval, Fourier)
  WalshDuality.lean    -- NEW: F₂ⁿ-based AB ↔ MaxNonlinear duality
  SpectralObject.lean  -- Homotopy spectral objects, Postnikov
  KasamiCIC.lean       -- Kasami spectral collapse (CIC version)
  KasamiCollapse.lean  -- Kasami collapse (bridge version)
  MTupleCount.lean     -- m-tuple counting
Bridge/
  Duality.lean         -- Categorical duality (Heyting, MacWilliams, bridge)
  PNBoolean.lean       -- PN-Boolean relative theorem
  RosettaStone.lean    -- Spectral-to-Topos isomorphism
CodingTheory/
  BinaryCode.lean      -- Binary codes, weight distribution, Pless moments
Foundation/
  ElemTopos.lean       -- Elementary topos, group objects, AB category
  TypeTopos.lean       -- Boolean topos instantiation
reuse-merge/           -- Reference material (not built)
```
