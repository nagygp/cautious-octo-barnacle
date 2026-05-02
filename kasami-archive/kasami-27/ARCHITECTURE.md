# Architecture: Proof that Kasami Function is Almost Bent

## Overview

The **Kasami function** is `f(x) = x^d` on `GF(2^n)` where `d = 2^{2k} - 2^k + 1`,
with `gcd(k, n) = 1` and `n` odd.

**Almost Bent (AB)** means the Walsh–Hadamard transform
`W_f(a) = ∑_x (-1)^{Tr(a·x^d + x)}` takes values only in `{0, ±2^{(n+1)/2}}`.

The main theorem is `kasami_is_ab` in `Kasami/KasamiFunction.lean`.

---

## Proof Architecture (Quadratic Form Route)

```
Layer 0: Field/Trace infrastructure          ← FULLY PROVED
    ↓
Layer 1: Kasami exponent properties          ← FULLY PROVED
    ↓
Layer 2: Quadratic form Q_a, bilinear B_a    ← PARTIALLY PROVED (bridges sorry'd)
    ↓
Layer 3: Linearized polynomial kernel        ← MOSTLY PROVED (one sorry)
    ↓
Layer 4: GF(2) Gauss sum evaluation          ← FULLY PROVED (general theory)
    ↓
Layer 5: Assembly (WHT ↔ QuadForm bridge)    ← SORRY'D (new bridge lemmas)
```

---

## File Map and Lemma Status

### Layer 0: Field and Trace Infrastructure — `Kasami/Basic.lean`, `Kasami/Trace.lean`, `Kasami/AdditiveCharacter.lean`

| Lemma | Lean Name | Status |
|-------|-----------|--------|
| 0a. `galoisField_card` | `F2n.card` | ✅ Proved |
| 0b. `trace_is_GF2_valued` | `tr2` | ✅ Proved |
| 0c. `trace_additive` | `tr2_add` | ✅ Proved |
| 0d. `trace_frobenius` | `tr2_sq`, `tr2_pow2` | ✅ Proved |
| 0e. `trace_surjective` | `tr2_surjective` | ✅ Proved |
| 0f. `addChar_from_trace` | `chi`, `chiAddChar` | ✅ Proved |

**Bonus proved:** `tr2_kernel_card`, `tr2_fiber_one_card`, `tr2_balanced`, `chi_add`, `chi_sq`, `chi_orthogonality`, `chi_inner_product`, `chi_sum`

### Layer 1: Kasami Exponent — `Kasami/KasamiExponent.lean`

| Lemma | Lean Name | Status |
|-------|-----------|--------|
| 1a. `kasami_exp_def` | `kasamiExp` | ✅ Proved |
| 1b. `kasami_exp_odd` | `kasamiExp_odd` | ✅ Proved |
| 1c. `kasami_gcd` | `kasamiExp_coprime` | ✅ Proved |
| 1d. `kasami_is_permutation` | `kasamiExp_permutation` | ✅ Proved |

### Layer 2: Quadratic Form Q_a — `Kasami/QuadFormBridge.lean`, `QuadFormGF2/Defs.lean`

| Lemma | Lean Name | Status | File |
|-------|-----------|--------|------|
| 2a. `Qa_def` | `QuadFormF2` structure | ✅ Proved | `QuadFormGF2/Defs.lean` |
| **2b. `Qa_is_quadratic`** | `kasami_Qa_is_quadratic` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |
| 2c. `Ba_explicit` | `QuadFormF2.polar` | ✅ Proved | `QuadFormGF2/Defs.lean` |
| 2d. `kasami_power_expansion` | `char2_sum_powers`, `gold_deriv` | ✅ Proved | `Kasami/CCDHelpers.lean` |
| **2e. `Ba_simplified`** | `kasami_Ba_simplified` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |

### Layer 3: Linearized Polynomial Kernel — `LinearizedPoly/`

| Lemma | Lean Name | Status | File |
|-------|-----------|--------|------|
| 3a. `La_def` | `linPolyL` | ✅ Proved | `LinearizedPoly/Defs.lean` |
| 3b. `La_is_linearized` | `linPolyL_linearized` | ✅ Proved | `LinearizedPoly/Defs.lean` |
| **3c. `radical_eq_kernel_La`** | `kasami_radical_eq_kernel` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |
| 3d. `kernel_La_bound` | `linPolyL_ker_card_classification` | ✅ Proved | `LinearizedPoly/Kernel.lean` |
| **3e. `rank_Ba`** | `kasami_radical_small` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |

**Sub-lemmas for 3d (all proved):**
- 3d-i. `linPolyL_ker_nonzero_eq` in `LinearizedPoly/Kernel.lean`
- 3d-ii. `linPolyM_ker_card` in `LinearizedPoly/Kernel.lean`
- 3d-iii. `linPolyL_ker_trivial_of_three_ndvd` in `LinearizedPoly/Kernel.lean`

### Layer 4: Gauss Sum — `QuadFormGF2/GaussSum.lean`

| Lemma | Lean Name | Status | File |
|-------|-----------|--------|------|
| 4a. `expSum_def` | `QuadFormF2.expSum` | ✅ Proved | `QuadFormGF2/GaussSum.lean` |
| 4b. `expSum_sq_rank` | `expSum_sq_eq_card_mul_radical_card` | ✅ Proved | `QuadFormGF2/GaussSum.lean` |
| **4c. `Qa_vanishes_on_radical`** | `kasami_Qa_vanishes_on_radical` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |

### Layer 5: Assembly — `Kasami/QuadFormBridge.lean`, `Kasami/KasamiFunction.lean`

| Lemma | Lean Name | Status | File |
|-------|-----------|--------|------|
| **5a. `walsh_eq_expSum`** | `kasami_walsh_eq_expSum` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |
| **5b. `walsh_sq_values`** | `kasami_walsh_sq_values` | ❌ Sorry | `Kasami/QuadFormBridge.lean` |
| **5c. `kasami_is_ab`** | `kasami_is_ab` | ❌ Sorry | `Kasami/KasamiFunction.lean` |

---

## Bridge Lemma Dependency Graph

```
kasami_Qa_is_quadratic (2b)
        ↓
kasami_Ba_simplified (2e) ← char2_sum_powers + tr2_pow2
        ↓
kasami_radical_eq_kernel (3c) ← tr2_surjective
        ↓
kasami_radical_small (3e) ← linPolyL_ker_card_classification
        ↓
kasami_Qa_vanishes_on_radical (4c)
        ↓
kasami_walsh_eq_expSum (5a)
        ↓
kasami_walsh_sq_values (5b) ← expSum_sq_eq_card_mul_radical_card
        ↓
kasami_is_ab (5c)
```

---

## Additional Proved Infrastructure

### Walsh-Hadamard Transform — `Kasami/WalshHadamard.lean` ✅ ALL PROVED
- `wht` definition, `wht_parseval`, `wht_inversion`, `wht_abs_le`

### Almost Bent Theory — `Kasami/AlmostBent.lean`
- `IsAlmostBent` definition ✅
- `ab_nonzero_count` ✅, `ab_fourth_moment` ✅
- `ab_implies_apn` ❌ Sorry

### Fourth Moment / Autocorrelation — `Kasami/FourthMoment.lean` ✅ ALL PROVED
- `derivCount`, `derivCount_even`, `autocorr`, `wht_sq_as_autocorr`, `fourth_moment_eq_autocorr_sq`

### CCD Factorization — `Kasami/CCDFactorization.lean`, `CCDHelpers.lean` ✅ ALL PROVED
- `kasamiExp_mul_identity`, `char2_add_pow`, `F2n_frobenius`, `char2_sum_powers`, `gold_deriv`

### Triple Count / P₃ — `Kasami/TripleCount.lean`, `KasamiP3.lean`
- `tripleCount_charSum_eq` ✅, `tripleCount_from_vanishing` ✅
- `ab_implies_vanishing` ❌ Sorry (depends on kasami_is_ab)

### Linearized Poly Kernel — `LinearizedPoly/Kernel.lean` ✅ MOSTLY PROVED
- `linPolyM_ker_card`, `linPolyL_ker_card_classification`, `linPolyL_ker_trivial_of_three_ndvd`
- `kasamiDiff_eq_implies_linearized` ❌ Sorry (in `KasamiKernel.lean`)

### Difference Set — `Kasami/DifferenceSet.lean` ✅ ALL PROVED
### Dual P₃ — `Kasami/DualP3.lean` ✅ ALL PROVED
### APN from AB — `Kasami/APNFromAB.lean` ✅ ALL PROVED
### Vanishing Proof — `Kasami/VanishingProof.lean` ✅ MOSTLY PROVED
### Artin-Schreier — `LinearizedPoly/ArtinSchreier.lean` ✅ ALL PROVED

---

## Summary of All Sorry's (11 total)

### Original sorries (4):
1. `kasami_is_ab` — `Kasami/KasamiFunction.lean:62`
2. `ab_implies_apn` — `Kasami/AlmostBent.lean:96`
3. `ab_implies_vanishing` — `Kasami/TripleCount.lean:120`
4. `kasamiDiff_eq_implies_linearized` — `LinearizedPoly/KasamiKernel.lean:91`

### New bridge lemmas (7, in `Kasami/QuadFormBridge.lean`):
5. `kasami_Qa_is_quadratic` — Layer 2b
6. `kasami_Ba_simplified` — Layer 2e
7. `kasami_radical_eq_kernel` — Layer 3c
8. `kasami_radical_small` — Layer 3e
9. `kasami_Qa_vanishes_on_radical` — Layer 4c
10. `kasami_walsh_eq_expSum` — Layer 5a
11. `kasami_walsh_sq_values` — Layer 5b

### Difficulty ranking of bridge lemmas:
- **Easiest:** `kasami_walsh_eq_expSum` (5a) — essentially definitional unfolding
- **Medium:** `kasami_radical_eq_kernel` (3c) — uses trace surjectivity
- **Medium:** `kasami_radical_small` (3e) — combines 3c with kernel classification
- **Hard:** `kasami_Qa_is_quadratic` (2b) — needs multinomial expansion in char 2
- **Hard:** `kasami_Ba_simplified` (2e) — needs Frobenius absorption into trace
- **Hard:** `kasami_Qa_vanishes_on_radical` (4c) — needs specific kernel element analysis
- **Hard:** `kasami_walsh_sq_values` (5b) — assembles everything

---

## How to Complete the Proof

To close `kasami_is_ab`, prove the 7 bridge lemmas in `Kasami/QuadFormBridge.lean` in order.
The theorem `kasami_is_ab_from_bridge` at the bottom of that file shows that once
`kasami_walsh_sq_values` is proved, the main theorem follows immediately.

The alternative path through `ab_implies_apn` and `ab_implies_vanishing` serves
the P₃ counting application and is independent of the bridge lemmas.
