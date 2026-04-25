# APN / Almost Bent Function Theory — Lean 4 Formalization

## Overview

This module provides a formal Lean 4 / Mathlib formalization of the theory of
**Almost Perfect Nonlinear (APN)** and **Almost Bent (AB)** functions over
`GF(2)^n`, which are fundamental objects in symmetric cryptography.

## Module Structure

| File | Description |
|------|-------------|
| `Defs.lean` | Core definitions: differential uniformity, APN, Walsh transform, AB, nonlinearity |
| `Basic.lean` | Basic properties of APN functions and the difference distribution table |
| `WalshTransform.lean` | Walsh–Hadamard transform: signF2, character orthogonality, Parseval's identity |
| `AlmostBent.lean` | AB theory: autocorrelation-Walsh identity, AB↔components spectrum, delta values |
| `Examples.lean` | Concrete examples: non-APN functions (zero, identity, additive), APN on GF(2) |

## Key Definitions

- **`APN.IsAPN`**: `F : α → α` is APN iff `∀ a ≠ 0, ∀ b, Δ_F(a,b) ≤ 2`
- **`APN.differentialUniformity`**: `δ(F) = max_{a≠0,b} |{x : F(x+a)-F(x) = b}|`
- **`APN.walshCoeff`**: `W_F(a,b) = ∑_x (-1)^{⟨b,F(x)⟩ + ⟨a,x⟩}`
- **`APN.IsAlmostBent`**: `∀ b ≠ 0, W_F(a,b) ∈ {0, ±2^((n+1)/2)}`
- **`APN.componentFunction`**: `F_b(x) = ⟨b, F(x)⟩` (inner product over GF(2))
- **`APN.walshHadamard`**: Walsh–Hadamard transform of a Boolean function

## Proved Theorems (35/36 — all verified, no sorry)

### Differential Uniformity & APN
- `isAPN_iff_differentialUniformity_le` — APN ↔ δ(F) ≤ 2
- `delta_sum` — ∑_b Δ(a,b) = |α|
- `delta_zero_zero` — Δ(0,0) = |α|
- `delta_zero_ne` — Δ(0,b) = 0 for b ≠ 0
- `delta_le_card` — Δ(a,b) ≤ |α|
- `delta_eq_fiber_card` — Δ via derivative fibers
- `isAPN_iff_derivatives` — APN via derivative characterization
- `isAPN_iff_derivative_two_to_one` — APN ↔ two-to-one derivatives (char 2)
- `isAPN_add_const` — APN invariant under adding constants
- `isAPN_translate` — APN invariant under translation

### Walsh Transform
- `signF2_sq`, `signF2_mul`, `signF2_abs`, `signF2_ne_zero` — sign function properties
- `walshCoeff_zero_zero` — W_F(0,0) = 2^n
- `walshCoeff_b_zero` — W_F(a,0) as character sum
- `walshCoeff_eq_walshHadamard` — vectorial = component Walsh
- `innerProductF2_zero_left/right`, `innerProductF2_add_left`, `innerProductF2_comm`
- **`character_sum_zero`** — character orthogonality: ∑_a (-1)^{⟨a,v⟩} = 0 for v ≠ 0
- **`character_sum_eq_pow`** — ∑_a (-1)^{⟨a,0⟩} = 2^n
- **`parseval_bool`** — Parseval's identity: ∑_a W_f(a)² = 2^(2n)
- **`parseval_vectorial`** — ∑_a W_F(a,b)² = 2^(2n)

### Almost Bent Theory
- **`autocorrelation_walsh`** — Wiener–Khinchin: 2^n·C_f(a) = ∑_u W_f(u)²·(-1)^{⟨u,a⟩}
- `ab_iff_components_spectrum` — AB ↔ all nontrivial components have spectrum {0,±2^((n+1)/2)}
- **`apn_delta_values`** — APN functions have Δ(a,b) ∈ {0, 2} for a ≠ 0

### Examples
- `zero_not_apn` — the zero function is not APN (|α| > 2)
- `id_not_apn` — the identity is not APN (|α| > 2)
- `additive_not_apn` — additive functions are not APN (|α| > 2)
- `every_function_apn_on_gf2` — every function on GF(2) is APN

## Open Formalization (1 sorry)

- **`ab_implies_apn`** — AB ⟹ APN. This is the deepest theorem in the theory,
  requiring the fourth-moment identity linking `∑ W^4` to `∑ Δ²`. The proof
  involves intricate Fourier-analytic arguments over GF(2)^n that go beyond
  the currently formalized infrastructure.

## Design Decisions

- APN is defined abstractly for any `[Fintype α] [AddCommGroup α]`
- Walsh transform is defined concretely over `Fin n → ZMod 2` (the standard model for GF(2)^n)
- The sign function `signF2 : ZMod 2 → ℤ` maps `0 ↦ 1, 1 ↦ -1`
- AB uses natural number division `(n+1)/2` for the exponent (note: mathematically
  meaningful only for odd n, but the definition is well-formed for all n)
