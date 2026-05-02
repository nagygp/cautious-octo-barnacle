# Summary of changes for run 54f47201-0452-43f0-a1e0-e45b26e51aeb
# Decomposition of `ccd_crossterm_gives_linPolyL`

Created `RequestProject/LinearizedPoly/CCDCrossterm.lean` — a new file that decomposes the deepest algebraic step in the CCD proof into 7 composable sub-lemmas, following a "one function does one thing" philosophy.

## What was done

The original `ccd_crossterm_gives_linPolyL` (in `LinearizedPoly/KasamiKernel.lean:164`) was a single monolithic `sorry`. It has been decomposed into a chain of sub-lemmas:

### ✅ Proved (4 lemmas)

1. **`Mk_Lk_eq`** — Pure identity: `M_k(L_k(z)) = z^{2^{3k}} + z`. Uses `add_pow_char_pow` from Mathlib (Freshman's dream) and char-2 cancellation.

2. **`deriv_eq_implies_B'_eq`** — Char-2 rearrangement: from the derivative equation `heq`, derives `(y+z+1)^d = (y+1)^d + δ`. Uses `CharTwo.add_self_eq_zero` from Mathlib.

3. **`crossterm_diff_eq_bilinear`** — Cross-term difference expansion: shows `C(y) + C(y+z) = δ·w^{2^k} + δ^{2^k}·w` where `δ` and `w` are the derivative values. Uses `add_pow_char_pow` from Mathlib.

4. **`bilinear_Mk_factor`** — Bilinear form factorization: shows `δ·w^{2^k} + δ^{2^k}·w = w^{2^k+1} · M_k(δ/w)` for `w ≠ 0`. Uses `linPolyM` from `LinearizedPoly/Defs.lean`.

### ❌ Sorry'd (2 lemmas — the genuinely deep algebraic core)

5. **`deriv_w_ne_zero`** — Derivative nonvanishing: `w = (y+1)^d + y^d ≠ 0`. Would use `Nat.Coprime.pow_left_bijective` from Mathlib; may need additional hypotheses.

6. **`Mk_eq_wMk_implies_Lk_zero`** — The deepest conclusion: from the combined identity chain and `z ∉ {0,1}`, conclude `L_k(z) = 0`. This is the core content of CCD 2000, Proposition 2.

## Mathlib / project reuse identified

- **From Mathlib**: `add_pow_char_pow`, `CharTwo.add_self_eq_zero`, `CharP.cast_eq_zero`, `Nat.Coprime.pow_left_bijective` (for Step 5)
- **From project**: `linPolyL`/`linPolyM` (Defs.lean), `ccd_second_deriv_eq`/`ccd_power_factorization` (KasamiKernel.lean, already proved)

## Files

- **Created**: `RequestProject/LinearizedPoly/CCDCrossterm.lean` (the decomposition)
- **Created**: `CCD_CROSSTERM_DECOMPOSITION.md` (detailed analysis with decomposition tree)
- **Modified**: `RequestProject/Main.lean` (added import)
- **Unchanged**: `RequestProject/LinearizedPoly/KasamiKernel.lean` (original sorry preserved)