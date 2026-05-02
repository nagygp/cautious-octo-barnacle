# Summary of changes for run 964f0ac4-d132-40f9-9cd1-7e34e8de6c78
## Summary of Changes

### New File: `RequestProject/Kasami/KasamiABProof.lean`

Created a comprehensive decomposition of the `kasami_is_ab` theorem into 9 modular sub-steps following the Quadratic Form / CCD proof route:

**Proved (sorry-free):**
1. **`wht_perm_zero`** — The WHT of any permutation function at 0 vanishes
2. **`kasami_wht_at_zero`** — For the Kasami function specifically, `wht f 0 = 0`
3. **`kasami_wht_as_shifted_sum`** — Expresses `wht f a` as a shifted exponential sum `∑_x (-1)^{Tr(x^d) + Tr(a·x)}`
4. **`kasami_is_ab_from_steps`** — Assembles `IsAlmostBent` from the Gauss sum value (Step 6) and the shifted dichotomy (Step 7)

**Decomposed sub-lemmas (sorry'd, each a single mathematical step):**
5. **`kasami_trace_power_is_quadratic`** — Bilinearity of the polar form of `Tr(x^d)`
6. **`kasami_radical_card`** — Radical of the Kasami bilinear form has size 1 or 2
7. **`kasami_gauss_sum_sq_eq`** — Gauss sum² = 2^n · |radical|
8. **`kasami_gauss_sum_sq_value`** — For odd n: Gauss sum² = 2^{n+1} (parity argument)
9. **`shifted_gauss_sq_dichotomy`** — Shifted Gauss sum² is 0 or unshifted² (with Q-vanishes-on-radical hypothesis)

### Modified: `RequestProject/LinearizedPoly/KasamiKernel.lean`

**Discovered and documented a mathematical bug:** The theorem `ccd_crossterm_gives_linPolyL` was stated for ALL characteristic-2 fields, but is FALSE in general. Counterexample: over GF(2^4) with k=2, take z ∈ GF(4)\GF(2) (a primitive cube root of unity). Then D₁f(0) = D₁f(z) = 1, but `linPolyL 2 z = z ≠ 0`.

The corrected statement requires finiteness conditions (|F| = 2^n, gcd(k,n) = 1). Added detailed documentation explaining the issue and noting that downstream usage in `kasamiDelta_two_to_one` (which already has these conditions) is still valid.

### Overall Sorry Status

The project now has 9 sorries total (was 4 in the original files):
- **Original 4:** `kasami_is_ab`, `ab_implies_vanishing`, `ccd_crossterm_gives_linPolyL`, `kasami_wht_sq_trichotomy`  
- **New 5 (from decomposition):** `kasami_trace_power_is_quadratic`, `kasami_radical_card`, `kasami_gauss_sum_sq_eq`, `kasami_gauss_sum_sq_value`, `shifted_gauss_sq_dichotomy`

The new sorries are strictly simpler than the originals — each represents a single, well-defined mathematical step rather than a multi-page proof. The assembly lemma `kasami_is_ab_from_steps` shows that proving Steps 6 and 7 would immediately give `kasami_is_ab`.

### Build Status
The full project builds successfully with `lake build` (8054 jobs, no errors).