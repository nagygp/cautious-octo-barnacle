# Decomposition Summary — `ccd_crossterm_gives_linPolyL` and `kasami_wht_sq_trichotomy`

## Project Structure

```
RequestProject/
├── Defs.lean              — Basic definitions (fields, linearized polynomials, WHT, AB)
├── QuadFormGF2.lean       — Quadratic form theory over GF(2)
├── CCDCrossterm.lean      — CCD cross-term theorem decomposition
├── WHTTrichotomy.lean     — WHT² trichotomy decomposition
└── Main.lean              — Entry point (imports all modules)
```

## Status Summary

| File | Theorems | Proved | Sorry'd |
|------|----------|--------|---------|
| `Defs.lean` | 8 defs + 5 thms | **5** ✅ | **0** |
| `QuadFormGF2.lean` | 3 defs + 6 thms | **6** ✅ | **0** |
| `CCDCrossterm.lean` | 20 thms | **18** ✅ | **2** |
| `WHTTrichotomy.lean` | 3 defs + 13 thms | **8** ✅ | **5** |
| **Total** | **55** | **37** ✅ | **7** sorry'd |

---

## Theorem 1: `ccd_crossterm_gives_linPolyL`

### Proved Sub-Lemmas ✅

| Lemma | Description |
|-------|-------------|
| `linPolyL_add` | `L_k(a+b) = L_k(a) + L_k(b)` (additivity) |
| `linPolyM_add` | `M_k(a+b) = M_k(a) + M_k(b)` (additivity) |
| `linPolyL_pow2k` | `L_k(z)^{2^k}` expanded via Freshman's dream |
| `mk_lk_factorization` | **S3.1**: `z^{2^{3k}} + z = M_k(L_k(z))` |
| `pow2_cross_term` | Generic `(y+z)^{2^i+2^j}` cross-term in char 2 |
| `pow2_cross_term_one` | Cross-term for `2^i + 1` exponents |
| `ccd_cross_diff_expansion` | **S3.2**: Full CCD `C(y+z) + C(y)` expansion |
| `mk_ker_zero` | `M_k(0) = 0` |
| `mk_ker_one` | `M_k(1) = 0` |
| `mk_zero_iff` | `M_k(x) = 0 ↔ x^{2^k} = x` |
| `frob_fixed_in_GF2` | **S3.3b**: Frobenius fixed points → `{0,1}` when `gcd(k,n)=1` |
| `mk_ker_eq_F2` | **S3.3**: `ker(M_k) = {0,1}` |
| `mk_eq_implies_diff_zero` | `M_k(a) = M_k(b) → M_k(a+b) = 0` |
| `linPolyL_one` | `L_k(1) = 1` |
| `linPolyL_zero` | `L_k(0) = 0` |
| `lk_eq_one_implies_shifted_zero` | `L_k(z) = 1 → L_k(z+1) = 0` |
| `mk_lk_zero_implies_lk_01` | `M_k(L_k(z)) = 0 → L_k(z) ∈ {0,1}` |

### Remaining Sorry'd Lemmas ❌

| Lemma | Difficulty | Description |
|-------|-----------|-------------|
| `lk_ne_one_from_ccd` | **Hard** | `L_k(z) = 1` is incompatible with CCD constraints when `z ∉ GF(2)`. Requires deep kernel analysis: when `|ker(L_k)| = 1`, contradicts `z ≠ 1`; when `|ker(L_k)| = 4` (3∣n), additional CCD constraints must rule it out. |
| `ccd_crossterm_gives_linPolyL` | **Hard** | Main theorem. Needs `lk_ne_one_from_ccd` plus showing `M_k(L_k(z)) = 0` from the CCD equation. |

---

## Theorem 2: `kasami_wht_sq_trichotomy`

### Proved Sub-Lemmas ✅

| Lemma | Description |
|-------|-------------|
| `kasamiCrossTerm_symm` | Cross-term symmetry |
| `kasamiCrossTerm_self` | Cross-term vanishes on diagonal |
| `kasamiTracePower_zero` | `Q_a(0) = 0` |
| `kasamiTracePower_polar` | Polar form = `Tr(a · crossTerm(x,y))` |
| `kasamiTracePower_polar_add_right` | Polar form is additive in second arg |
| `kasamiLinPoly_add` | `L_a(x+y) = L_a(x) + L_a(y)` |
| `trace_nondeg` | Trace non-degeneracy: `∀y, Tr(y·c) = 0 → c = 0` |
| `kasami_radical_eq_kernel` | `rad(Q_a) = ker(L_a)` |
| `kasami_wht_eq_expSum` | WHT = exponential sum (definitional) |

### From `QuadFormGF2.lean` ✅

| Lemma | Description |
|-------|-------------|
| `signZ_add` | `signZ(a+b) = signZ(a) · signZ(b)` |
| `signZ_sq` | `signZ(a)² = 1` |
| `expSum_sq_eq_card_mul_radical_card` | **S(Q)² = \|V\| · \|rad\|** (Gauss sum square formula) |
| `expSum_zero_of_radical_nonvanishing` | `S(Q) = 0` when Q is nonzero on radical |

### Remaining Sorry'd Lemmas ❌

| Lemma | Difficulty | Description |
|-------|-----------|-------------|
| `kasamiCrossTerm_add_right` | **Hard** | Cross-term bilinearity. Requires multinomial expansion of `(x+y)^d` for `d = 2^{2k}-2^k+1` in char 2. |
| `kasami_polar_eq_trace_linpoly` | **Hard** | `B_a(x,y) = Tr(y · L_a(x))`. Requires cross-term expansion + trace-Frobenius compatibility + Frobenius identity. |
| `kasamiLinPoly_ker_card` | **Hard** | `\|ker(L_a)\| ∈ {1, 2}`. Requires linearized polynomial kernel theory. |
| `kasami_trace_vanishes_on_kernel` | **Hard** | `Tr(a·x^d) = 0` when `L_a(x) = 0`. Requires Artin-Schreier image characterization. |
| `kasami_wht_sq_value` | **Medium** (assembly) | Combines all layers. Once sub-lemmas are proved, this is a case analysis on `\|rad\|`. |

---

## Dependency Graph

```
                    ccd_crossterm_gives_linPolyL
                    ├── mk_lk_factorization ✅
                    ├── ccd_cross_diff_expansion ✅
                    ├── mk_ker_eq_F2 ✅
                    │   └── frob_fixed_in_GF2 ✅
                    └── lk_ne_one_from_ccd ❌

                    kasami_wht_sq_trichotomy
                    └── kasami_wht_sq_value ❌
                        ├── kasami_wht_eq_expSum ✅
                        ├── expSum_sq_eq_card_mul_radical_card ✅
                        ├── expSum_zero_of_radical_nonvanishing ✅
                        ├── kasami_radical_eq_kernel ✅
                        │   └── trace_nondeg ✅
                        ├── kasami_polar_eq_trace_linpoly ❌
                        │   └── kasamiCrossTerm_add_right ❌
                        ├── kasamiLinPoly_ker_card ❌
                        └── kasami_trace_vanishes_on_kernel ❌
```

---

## Mathematical Notes on Remaining Sorries

### `kasamiCrossTerm_add_right` (Hardest)
The cross-term `(x+y)^d + x^d + y^d` for `d = 2^{2k} - 2^k + 1` must be shown
bilinear. The standard proof uses the factorization `d(2^k+1) = 2^{3k}+1`:
the cross-term for `2^{3k}+1` is `xy^{2^{3k}} + yx^{2^{3k}}` (clearly bilinear),
and `d`'s cross-term inherits bilinearity through the `(2^k+1)`-power structure.
This requires careful multinomial expansion in characteristic 2.

### `kasami_polar_eq_trace_linpoly`
After expanding the cross-term into monomials `x^{2^i}·y^{2^j}`, apply
`Tr(z^{2^i}) = Tr(z)` repeatedly to merge Frobenius-shifted y terms,
then factor out y to obtain `L_a(x)`. Uses `x^{2^n} = x` to reduce indices mod n.

### `kasamiLinPoly_ker_card`
The kernel of `L_a` is an F₂-subspace. Its dimension is bounded by the degree
of `L_a` as a linearized polynomial (degree 2 in σ). The classification uses
the connection to `linPolyL k` and its kernel structure.

### `kasami_trace_vanishes_on_kernel`
When `L_a(x) = 0`, algebraic manipulation shows `a·x^d = z² + z` for some `z`,
placing it in `Im(Artin-Schreier) = ker(Tr)`.
