# Adjoint Transfer Infrastructure — DAG Overview

## Purpose

These 5 Lean files form the foundational layers needed to bridge the gap between:

- ✅ **`dicksonF_injective_on_units'`** (proved in `DicksonPoly.lean`)
  — The Dickson polynomial `f_k` is injective on `F* = GF(2^n)\{0}`

- ❌ **`mcm_permutation`** (sorry in `KasamiCollisionMVP.lean`, line 302)
  — The MCM function `M(y) = S_k(y)^{q+1}/y^q` is injective on `F*`

The bridge uses the **Lemma 3.1 adjoint transfer machinery** from
Dempwolff-Müller (2013).

## DAG Structure

```
                    TraceNondeg.lean (T1)
                    ┌──────┴──────┐
                    │             │
               AdjointMap.lean (T2)
                    │             │
                    ├─────────────┤
                    │             │
              ExpTransfer.lean (T3)
                    │             │
                    ▼             │
          AdjointTransfer.lean (T4)
                    │             │
                    ▼             ▼
             MCMBridge.lean (T5) ◄── DicksonPoly.lean (proved ✅)
                    │
                    ▼
            mcm_permutation (KasamiCollisionMVP.lean)
                    │
                    ▼
            kasami_is_apn_mvp (proved, modulo mcm_permutation)
```

## Layer Details

### T1: TraceNondeg.lean — Trace Form Nondegeneracy
**Key theorems** (6 sorries):
- `Tr_n_sq` — `Tr(x)² = Tr(x)` (trace takes values in GF(2))
- `Tr_n_mem_GF2` — `Tr(x) ∈ {0, 1}`
- `Tr_n_surjective` — `∃ x, Tr(x) = 1`
- `trace_bilinear_nondegenerate` — `(∀ y, Tr(xy) = 0) → x = 0`
- `Tr_n_kernel_card` — `|ker(Tr)| = 2^{n-1}`
- `Tr_n_frob_pow` — `Tr(x^{2^j}) = Tr(x)` (Frobenius invariance)

**Proved**: `Tr_n_add`, `Tr_n_zero`, `Tr_n_mul_comm`, `Tr_n_frob` (from `Tr_n_frob_pow`)

### T2: AdjointMap.lean — Adjoint Linear Maps
**Key theorems** (7 sorries):
- `trAdjoint` — Construction of the trace-adjoint `L*`
- `trAdjoint_spec` — `Tr(L(x)·y) = Tr(x·L*(y))`
- `trAdjoint_unique` — Uniqueness of adjoint
- `trAdjoint_frobPow` — `(Frob^j)* = Frob^{n-j}`
- `trAdjoint_partialTrace` — `S_k*(y) = Σ y^{2^{n-i}}`
- `trAdjoint_comp` — `(L∘M)* = M*∘L*`

**Proved**: `frobPow`, `partialTrace`, `GF2Linear.comp`, `combinedMap_ne_zero`

### T3: ExpTransfer.lean — Exponent Arithmetic
**Key theorems** (7 sorries):
- `inv_pow_qp1_eq` — `y^{-(q+1)} = y^{expG}`
- `inv_pow_q_eq` — `y^{-q} = y^{expM}`
- `expG_add_qp1` — `expG + (q+1) = 2^n - 1`
- `expM_add_q` — `expM + q = 2^n - 1`
- `two_mul_halfExp` — `2 · halfExp = 2^n - 2^k`
- `dualExp_to_M` — Connects dual exponent to M-function exponent
- `G_eq_dicksonF` — G-function equals Dickson polynomial

### T4: AdjointTransfer.lean — The Transfer Theorem
**Key theorems** (6 sorries):
- `G_factors_through_sq` — `G = G_half²`
- `G_half_injective_of_G_injective` — Squaring bijective in char 2
- `adjoint_transfer_injective` — **Dempwolff-Müller Lemma 3.1**
- `trAdjoint_partialTrace_injective` — Transfer for `S_k`
- `adjoint_partialTrace_eq_frob_Sk` — `S_k* = S_k^{2^{n-k}}`
- `Sk_combined_injective` — End-to-end: Dickson → MCM

### T5: MCMBridge.lean — Final Bridge
**Key theorem** (0 additional sorries):
- `mcm_permutation_bridge` — Delegates to `Sk_combined_injective`

## Sorry Count Summary

| Layer | Sorries | Content |
|-------|---------|---------|
| T1 | 6 | Trace theory |
| T2 | 7 | Adjoint maps |
| T3 | 7 | Exponent arithmetic |
| T4 | 6 | Transfer theorem |
| T5 | 0 | Bridge (delegates to T4) |
| **Total** | **26** | |

## Mathematical Proof Chain

The complete proof follows Cohen-Matthews (1994) + Dempwolff-Müller (2013):

1. **Dickson injectivity** (proved): `f_k` injective on F*
2. **G-function identity**: `S_k(y)² · y^{expG} = f_k(y + y^q)` (connects to Dickson)
3. **Factor through squaring**: `G(y) = G_half(y)²`, and Frobenius bijective ⟹ G_half bijective
4. **Adjoint transfer** (Lemma 3.1): G_half = S_k · y^{halfExp} injective
   ⟹ S_k* · y^{dualExp} injective
5. **S_k* rewrite**: `S_k*(y) = S_k(y)^{2^{n-k}}` (Frobenius cycling)
6. **Exponent arithmetic**: Convert to `S_k(y)^{q+1} · y^{expM}` form
7. **Cross-product form**: This is exactly `mcm_permutation`

## Build Verification

All 5 files compile (with sorries) against Lean 4.28.0 + Mathlib:
```
lake build RequestProject.Foundations.AdjointTransfer.TraceNondeg    ✅
lake build RequestProject.Foundations.AdjointTransfer.AdjointMap     ✅
lake build RequestProject.Foundations.AdjointTransfer.ExpTransfer    ✅
lake build RequestProject.Foundations.AdjointTransfer.AdjointTransfer ✅
lake build RequestProject.Foundations.AdjointTransfer.MCMBridge      ✅
```
