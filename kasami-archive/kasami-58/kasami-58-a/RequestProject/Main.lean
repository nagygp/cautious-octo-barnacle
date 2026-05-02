import RequestProject.KasamiDefs
import RequestProject.KasamiPhase1
import RequestProject.KasamiPhase2
import RequestProject.CCDCounting
import RequestProject.Mathlib.QuadraticFourier
import RequestProject.KasamiPhase3

/-!
# Kasami Almost Bent Functions — Unified Proof

## File Hierarchy

* `KasamiDefs.lean` — Core definitions: Kasami exponent, Frobenius iterates,
  linearized polynomials `L_k` and `M_k`, kernel and fixed-point sets.

* `KasamiPhase1.lean` — **Linearized Polynomial Foundations (fully verified)**
  - `linearized_kernel_subset_cube`: ker(L_k) ⊆ GF(2^{3k})
  - `mk_ker_eq_F2`: ker(L_k) ⊆ {0, 1} when gcd(3k, n) = 1

* `KasamiPhase2.lean` — **Cross-Term Decomposition**
  - `trace_frobenius_invariant`: Tr(x^{2^k}) = Tr(x) (verified)
  - `linPolyL_add`: L_k is GF(2)-linear (verified)
  - `radical_eq_ker_LA`: radical of Q_a = ker(L_a) (sorry — deep CCD identity)

* `CCDCounting.lean` — **CCD Counting Argument (fully verified)**
  - Frobenius-GCD theorem
  - CCD kernel bound: under gcd(3k, n) = 1, kernel ⊆ {0, 1}
  - GCD computation: gcd(3k, 2k+1) ∣ 3

* `Mathlib/QuadraticFourier.lean` — **Walsh Spectrum (fully verified)**
  - Walsh integer values: W² = 2^{n+1} implies W = ±2^{(n+1)/2}

* `KasamiPhase3.lean` — **WHT Squared Trichotomy**
  - `kasami_wht_sq_value` / `kasami_is_AB`: |W|² ∈ {0, 2^n, 2^{n+1}}
  - Structurally complete; depends on three sorry'd helper lemmas
    (`wht_vanishing`, `wht_peak`, `kerDimLA_mem`)

## Verified vs. Remaining Sorries

### Fully verified modules (0 sorries)
- `KasamiDefs.lean`
- `KasamiPhase1.lean`
- `CCDCounting.lean`
- `Mathlib/QuadraticFourier.lean`

### Modules with remaining sorries
- `KasamiPhase2.lean` (1 sorry: `radical_eq_ker_LA`)
- `KasamiPhase3.lean` (3 sorries: `wht_vanishing`, `wht_peak`, `kerDimLA_mem`)

## Core Hypotheses (standardized across all files)
- `[CharP F 2]`: F has characteristic 2
- `(hodd : ¬ 2 ∣ n)`: n is odd
- `(hgcd : Nat.gcd (3 * k) n = 1)`: GCD condition
- `(hcard : Nat.card F = 2 ^ n)`: field cardinality
-/
