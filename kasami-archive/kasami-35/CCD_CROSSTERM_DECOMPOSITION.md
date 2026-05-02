# Decomposition of `ccd_crossterm_gives_linPolyL`

## Overview

The lemma `ccd_crossterm_gives_linPolyL` (in `LinearizedPoly/KasamiKernel.lean:164`)
is the deepest algebraic step in the CCD (Canteaut–Charpin–Dobbertin 2000) proof
of the Kasami derivative kernel theorem. It states:

> Given `z ≠ 0`, `z ≠ 1`, and the derivative equation
> `(y+z+1)^d + (y+z)^d = (y+1)^d + y^d`
> where `d = 2^{2k} − 2^k + 1`, conclude `L_k(z) = 0`.

This document describes its decomposition into 7 sub-lemmas in
`LinearizedPoly/CCDCrossterm.lean`, 4 of which are fully proved and
2 of which remain `sorry`.

## Decomposition Tree

```
ccd_crossterm_gives_linPolyL  (original, KasamiKernel.lean:164)
│
└── ccd_crossterm_gives_linPolyL'  (assembly, delegates to Step 6)
    │
    └── Mk_eq_wMk_implies_Lk_zero  ❌  (Step 6 — deepest, sorry)
        │
        ├── Mk_Lk_eq  ✅  (Step 1 — pure identity)
        │   └── uses: add_pow_char_pow (Mathlib), CharTwo.add_self_eq_zero (Mathlib)
        │
        ├── ccd_second_deriv_eq  ✅  (Step 2 — already in KasamiKernel.lean)
        │   └── uses: ccd_power_factorization (KasamiKernel.lean)
        │
        ├── crossterm_diff_eq_bilinear  ✅  (Step 3)
        │   ├── uses: deriv_eq_implies_B'_eq  ✅
        │   └── uses: add_pow_char_pow (Mathlib)
        │
        ├── bilinear_Mk_factor  ✅  (Step 4)
        │   └── uses: linPolyM (LinearizedPoly/Defs.lean)
        │
        └── deriv_w_ne_zero  ❌  (Step 5 — sorry)
            └── would use: Nat.Coprime.pow_left_bijective (Mathlib)
```

## Lemma-by-Lemma Detail

### ✅ Step 1: `Mk_Lk_eq`
**Statement**: `M_k(L_k(z)) = z^{2^{3k}} + z`

**What it does**: Establishes that composing `M_k` with `L_k` gives the Frobenius
difference `z^{2^{3k}} + z`. This is a pure algebraic identity that holds
in any characteristic-2 ring.

**Mathlib reuse**: `add_pow_char_pow` (Freshman's dream), `CharTwo.add_self_eq_zero`.

**Proof technique**: Expand via Freshman's dream, cancel paired terms in char 2.

---

### ✅ Step 2: `ccd_second_deriv_eq` (already in KasamiKernel.lean)
**Statement**: If `D₁f(y+z) = D₁f(y)`, then `z^{2^{3k}} + z = C(y) + C(y+z)`.

**What it does**: Takes the "second derivative" of the CCD power factorization.
Already proved in the project.

---

### ✅ Step 3a: `deriv_eq_implies_B'_eq`
**Statement**: From `heq`, derive `(y+z+1)^d = (y+1)^d + ((y+z)^d + y^d)`.

**What it does**: Rearranges the hypothesis `B' + A' = B + A` into `B' = B + δ`,
using char-2 cancellation (`a + a = 0`).

**Mathlib reuse**: `CharTwo.add_self_eq_zero`.

---

### ✅ Step 3b: `crossterm_diff_eq_bilinear`
**Statement**: `C(y) + C(y+z) = δ · w^{2^k} + δ^{2^k} · w`

**What it does**: Expands `C(y+z)` by substituting `B' = B + δ` and `A' = A + δ`,
applying Freshman's dream to `(A+δ)^{2^k}` and `(B+δ)^{2^k}`, and
collecting terms. The cross terms `δ·δ^{2^k} + δ^{2^k}·δ` cancel in char 2.

**Mathlib reuse**: `add_pow_char_pow` (Freshman's dream).

---

### ✅ Step 4: `bilinear_Mk_factor`
**Statement**: `δ · w^{2^k} + δ^{2^k} · w = w^{2^k+1} · M_k(δ / w)` (for `w ≠ 0`)

**What it does**: Factors the bilinear form through `M_k` by substituting `t = δ/w`
and recognizing `t^{2^k} + t = M_k(t)`.

**Project reuse**: `linPolyM` from `LinearizedPoly/Defs.lean`.

---

### ❌ Step 5: `deriv_w_ne_zero` (sorry)
**Statement**: `(y+1)^d + y^d ≠ 0` (under the given hypotheses)

**What it does**: Shows the derivative value `w` is nonzero. If `w = 0` then
`(y+1)^d = y^d`, contradicting injectivity of `x ↦ x^d` (since `y ≠ y+1`
in char 2).

**Mathlib connection**: Would use `Nat.Coprime.pow_left_bijective` from Mathlib,
which states `x ↦ x^n` is bijective when `gcd(n, |G|) = 1`.

**Note**: May need additional hypotheses (`Fintype.card F = 2^n`, `Nat.Coprime k n`)
to ensure `gcd(d, |F*|) = 1`.

---

### ❌ Step 6: `Mk_eq_wMk_implies_Lk_zero` (sorry)
**Statement**: Given `heq`, `z ≠ 0`, `z ≠ 1`, conclude `L_k(z) = 0`.

**What it does**: The deepest algebraic conclusion. Combines Steps 1–5 and uses
polynomial-identity reasoning specific to the Kasami exponent `d = 2^{2k} − 2^k + 1`.

The argument involves showing that the cross-term difference structure,
combined with the identity `d · (2^k + 1) = 2^{3k} + 1`, forces
`L_k(z) = 0`. This is the core content of CCD 2000, Proposition 2.

---

## Mathlib Lemmas Used (Standing on Giants)

| Lemma | Module | Used in |
|-------|--------|---------|
| `add_pow_char_pow` | `Mathlib.Algebra.CharP.Lemmas` | Steps 1, 3 |
| `CharTwo.add_self_eq_zero` | `Mathlib.Algebra.CharP.CharTwo` | Steps 1, 3a |
| `CharP.cast_eq_zero` | `Mathlib.Algebra.CharP.Defs` | Step 1 |
| `Nat.Coprime.pow_left_bijective` | `Mathlib.GroupTheory.OrderOfElement` | Step 5 (potential) |

## Project-Internal Lemmas Used

| Lemma | File | Used in |
|-------|------|---------|
| `linPolyL` / `linPolyM` | `LinearizedPoly/Defs.lean` | Steps 1, 4, 6 |
| `ccd_second_deriv_eq` | `LinearizedPoly/KasamiKernel.lean` | Step 2 |
| `ccd_power_factorization` | `LinearizedPoly/KasamiKernel.lean` | Step 2 |

## File Locations

- **New file**: `RequestProject/LinearizedPoly/CCDCrossterm.lean`
- **Original sorry**: `RequestProject/LinearizedPoly/KasamiKernel.lean:176`
- **Imports added to**: `RequestProject/Main.lean`
