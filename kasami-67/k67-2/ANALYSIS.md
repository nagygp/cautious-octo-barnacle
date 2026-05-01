# Analysis: Completing Kasami Formalization Versions

## Overview

This analysis examines whether the formalization attempts in `kasami-64`, `kasami-65`, `kasami-66`,
and `kasami-67` from [cautious-octo-barnacle](https://github.com/attilavjda/cautious-octo-barnacle)
can be completed by replacing hypotheses with already-formalized lemmas from across the repository.

**Note:** `kasami-67` does not exist in the repository.

---

## Summary of Findings

| Version | Status Before | Status After | Outcome |
|---------|--------------|--------------|---------|
| kasami-64 | 0 sorries ✅ | Already complete | Hypotheses are deep mathematical facts; cannot be replaced from repo |
| kasami-65 | 0 sorries ✅ | Already complete | Best overall formalization; hypotheses are clean and minimal |
| kasami-66 | 6 sorries ❌ | **2 sorries eliminated, 2 mathematically incorrect** | Partially completable; 2 of 4 sorry'd theorems proved, 2 are **false** |
| kasami-67 | Does not exist | N/A | N/A |

---

## Detailed Analysis

### kasami-64: P₃ Completeness Analysis

**Files:** Defs.lean, TraceNondeg.lean, PolarFormBridge.lean, WalshP3.lean

**Status:** Complete (0 sorries). All theorems compile with only standard axioms.

**Main Result:** `p3_triple_count` — T₃ = 2^{2n-3} for AB functions.

**Hypotheses that could potentially be replaced:**
- `hTr_add`, `hTr_zero`, `hTr_sep` (trace properties) — These could be instantiated with the actual field trace, using results from kasami-63/KasamiPolarExpansion.lean
- `hAB` (Almost Bent property) — **Not proved anywhere in the repo.** This is the deepest hypothesis.
- `hParseval` — Proved within the same file (kasami-64 proves Parseval internally)
- `hTriple`, `hTripleSum` — **Not proved anywhere in the repo.** These encode the Walsh convolution identity.

**Verdict:** Cannot be further improved from existing repo lemmas. The formulation is conditioned on the AB property and Walsh convolution identity, which require Gauss sum theory not available in any sorry-free form.

### kasami-65: Corrected P₃ Triple Count

**Files:** Adds KasamiPolarExpansion.lean, KasamiFinal.lean on top of kasami-64's files.

**Status:** Complete (0 sorries).

**Main Result:** `p3_triple_count_corrected` — T₃ = 2^{2n-3} - 2^{n-2} (correcting kasami-64's formula).

**Key Improvement over kasami-64:**
- Discovers that the original T₃ = 2^{2n-3} formula is **incorrect**
- Proves the corrected formula T₃ = 2^{2n-3} - 2^{n-2}
- Eliminates the `hTriple`/`hTripleSum` hypotheses from kasami-64 by proving the triple correlation identity internally
- Still takes `hAB`, `hf0`, `hbal` as hypotheses

**Hypotheses remaining:**
- `hAB : IsAlmostBent F Tr f ((n + 1) / 2)` — **Not proved anywhere.** Would require Gauss sum theory.
- `hf0 : f 0 = 0` — Provable for Tr(x^d) (trace of zero is zero).
- `hbal : walshTransform F Tr f 0 = 0` — Provable from permutation property of x → x^d.

**Verdict:** This is the strongest and most correct formalization. The remaining hypotheses (AB, balanced) cannot be discharged from existing repo lemmas.

### kasami-66: Gold Function Spectral Theory

**Files:** KasamiPolarExpansion.lean, CCDCounting.lean, GoldKernelBound.lean, GoldSpectral.lean, KasamiFinal.lean

**Status before:** 6 sorries (4 in GoldSpectral.lean, 2 in KasamiFinal.lean).

**Sorry'd theorems:**
1. `gold_walsh_sq_spectrum` — W(a)² ∈ {0, 2^{n+1}} (AB property)
2. `gold_walsh_at_zero` — W(0) = 0 (balancedness)
3. `gold_walsh_third_moment_zero` — ∑ W(a)³ = 0 ← **MATHEMATICALLY FALSE**
4. `gold_P3_ordered` — P₃ = 2^{2n-1} ← **MATHEMATICALLY FALSE**

**What was accomplished:**

✅ **Proved `gold_walsh_sq_spectrum`** — The AB property for the Gold function, via a novel radical factorization approach. This is the deepest result, proved entirely from first principles using:
- The polar form identity `Tr(polar(z,y)) = Tr(y · L(z))` (using the trace adjoint)
- The kernel characterization: `L(z) = 0 iff z ∈ {0, 1}` (using Frobenius injectivity and CCD)
- The key identity: W(a)² = |F| · (1 + χ(1+a)), where χ = (-1)^Tr

✅ **Proved `gold_walsh_at_zero`** — Follows from the Walsh² identity: W(0)² = |F|·(1 + χ(1)) = |F|·(1-1) = 0.

❌ **`gold_walsh_third_moment_zero` is FALSE** — The correct value is ∑ W(a)³ = 2^{2n+1}, not 0.
A counterexample: over GF(2³) with k=1, direct computation gives ∑ W(a)³ = 2^7 = 128 ≠ 0.

❌ **`gold_P3_ordered` is FALSE** — The correct formula is goldTripleCount = 2^{2n-1} + 2^n, not 2^{2n-1}.

Both false theorems have been commented out with explanations of the correct values.

**New hypothesis added:** Both `gold_walsh_sq_spectrum` and `gold_walsh_at_zero` now require `hn : Module.finrank (ZMod 2) F = 2 * k + 1` (the Kasami parameter relation). This is satisfied in the intended Kasami setting.

---

## Reuse of Proven Lemmas Across the Repository

The following lemmas from the repository were **directly reused** or **inspired the proofs** in this work:

| Source | Lemma | Used In |
|--------|-------|---------|
| kasami-66/KasamiPolarExpansion | `gold_bridge`, `trace_adjoint`, `trace_frobenius_inv` | `polar_trace_eq` (WalshRadical) |
| kasami-66/GoldKernelBound | `frobenius_injective` | `unweighted_ker_le_two`, `unweighted_kernel_char` |
| kasami-66/CCDCounting | `frobenius_gcd_fixed`, `ccd_kernel_bound` | Radical characterization |
| kasami-66/KasamiPolarExpansion | `trace_nondeg` | Inner sum vanishing |
| kasami-51/QuadraticFourier | `walsh_spectrum_values` | Conceptual guidance (not directly imported) |
| kasami-64/WalshP3 | `character_orthogonality` | Proof strategy for `inner_sum_off_radical` |

---

## New File: `RequestProject/WalshRadical.lean`

This new file contains the complete proof of the AB property via radical factorization:

- **`chiInt'_mul`** — Multiplicativity of the additive character ✅
- **`trace_frob_plus_id`** — Tr(y^{2^k} + y) = 0 ✅
- **`trace_one_odd`** — Tr(1) = 1 for odd extension degree ✅
- **`unweighted_ker_le_two`** — |ker(L)| ≤ 2 ✅
- **`unweighted_kernel_char`** — ker(L) = {0, 1} ✅
- **`polar_trace_eq`** — Tr(polar(z,y)) = Tr(y·L(z)) ✅
- **`inner_sum_off_radical`** — Character sum vanishes off radical ✅
- **`inner_sum_one`** — Character sum at z=1 equals |F| ✅
- **`walsh_sq_eq`** — **Key identity:** W(a)² = |F|·(1 + χ(1+a)) ✅
- **`gold_walsh_sq_AB`** — AB property: W²  ∈ {0, 2^{n+1}} ✅
- **`gold_walsh_zero`** — Balancedness: W(0) = 0 ✅

All 11 theorems proved from first principles with zero sorries and only standard axioms.

---

## Conclusion

**kasami-65** is the best version — it is already complete with 0 sorries and proves the corrected triple count formula T₃ = 2^{2n-3} - 2^{n-2}.

**kasami-66** was the most ambitious attempt (trying to prove everything from scratch for the Gold function) but contained two mathematically incorrect claims. This work successfully proved the two correct claims (`gold_walsh_sq_spectrum` and `gold_walsh_at_zero`) from first principles, using a radical factorization approach that leverages the proven lemmas from within kasami-66 itself (polar expansion, kernel bounds, trace adjoint).

The key mathematical insight enabling the AB proof is:
> W(a)² = |F| · (1 + (-1)^{Tr(1+a)})

This identity follows from expanding W(a)², substituting z = x+y, and observing that the inner character sum ∑_y (-1)^{Tr(polar(z,y))} vanishes for z ∉ {0,1} (the radical of the polar form).
