# Summary of changes for run 8fe77fb6-fb38-4750-a563-723cfddffa30
# Decomposition Summary

I decomposed the two sorry'd theorems `ccd_crossterm_gives_linPolyL` and `kasami_wht_sq_trichotomy` into a hierarchy of lemmas and sub-lemmas across 4 Lean files. The project builds successfully with Lean 4.28.0 + Mathlib.

## Project Structure

- **`RequestProject/Defs.lean`** — Basic definitions: finite field helpers (char 2), linearized polynomials `L_k`, `M_k`, Kasami exponent/function, CCD cross-term, trace class, WHT, Almost Bent
- **`RequestProject/QuadFormGF2.lean`** — Quadratic form theory over GF(2): structure, polar form, radical, sign function, exponential sum, **Gauss sum square formula** (fully proved)
- **`RequestProject/CCDCrossterm.lean`** — CCD cross-term decomposition (18 of 20 lemmas proved)
- **`RequestProject/WHTTrichotomy.lean`** — WHT² trichotomy decomposition (8 of 13 lemmas proved)
- **`DECOMPOSITION_SUMMARY.md`** — Full status table, dependency graph, and mathematical notes

## Proved Results (37 total, all with standard axioms only)

### CCD Cross-Term (Theorem 1) — Key Proved Lemmas:
- **`mk_lk_factorization`** (S3.1): `z^{2^{3k}} + z = M_k(L_k(z))` — the key algebraic factorization
- **`ccd_cross_diff_expansion`** (S3.2): Full CCD cross-term difference `C(y+z) + C(y)` expanded
- **`frob_fixed_in_GF2`** (S3.3b): Frobenius fixed points `{x : x^{2^k} = x} ⊆ {0,1}` when `gcd(k,n)=1`
- **`mk_ker_eq_F2`** (S3.3): `ker(M_k) = {0,1}` when `gcd(k,n)=1`
- Plus: `linPolyL_add`, `linPolyM_add`, `pow2_cross_term`, `mk_lk_zero_implies_lk_01`, etc.

### WHT Trichotomy (Theorem 2) — Key Proved Lemmas:
- **`expSum_sq_eq_card_mul_radical_card`**: `S(Q)² = |V| · |rad(Q)|` — the Gauss sum square formula
- **`expSum_zero_of_radical_nonvanishing`**: `S(Q) = 0` when Q is nonzero on radical
- **`trace_nondeg`**: Trace non-degeneracy: `∀y, Tr(y·c) = 0 → c = 0`
- **`kasami_radical_eq_kernel`**: `rad(Q_a) = ker(L_a)` (using trace non-degeneracy)
- Plus: `kasamiCrossTerm_symm/self`, `kasamiTracePower_polar`, `kasami_wht_eq_expSum`, etc.

## Remaining Sorry'd Lemmas (7 total — all are genuinely hard)

1. **`lk_ne_one_from_ccd`** — `L_k(z) ≠ 1` under CCD constraints (requires deep kernel analysis)
2. **`ccd_crossterm_gives_linPolyL`** — Main CCD theorem (depends on #1)
3. **`kasamiCrossTerm_add_right`** — Cross-term bilinearity (requires multinomial expansion of `(x+y)^d` in char 2)
4. **`kasami_polar_eq_trace_linpoly`** — Polar form = `Tr(y·L_a(x))` (requires cross-term expansion + trace-Frobenius)
5. **`kasamiLinPoly_ker_card`** — `|ker(L_a)| ∈ {1, 2}` (requires linearized polynomial kernel theory)
6. **`kasami_trace_vanishes_on_kernel`** — `Tr(a·x^d) = 0` on kernel (requires Artin-Schreier argument)
7. **`kasami_wht_sq_value`** — Assembly of WHT² trichotomy (depends on #3-6)