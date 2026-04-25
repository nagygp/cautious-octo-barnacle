# Summary of changes for run 1b638069-217e-4163-8f86-edd12eff0cff
## Kasami Power Function Formalization

I created a modular Lean 4 formalization of Kasami power function theory across 7 files in `RequestProject/Kasami/`:

### Module Structure

| File | Contents | Sorry-free? |
|------|----------|-------------|
| `Defs.lean` | Core definitions: `kasamiExponent`, `powerFun`, `deltaSet` | ✅ Yes |
| `CharTwo.lean` | Characteristic 2 lemmas: `charTwo_add_self`, `charTwo_neg_eq_self`, `charTwo_sub_eq_add` | ✅ Yes |
| `Exponent.lean` | Properties of the Kasami exponent `2^{2k} - 2^k + 1` | ✅ Yes |
| `Trace.lean` | Absolute trace, additive character `chi`, `traceLift`, character orthogonality | ✅ Yes |
| `Walsh.lean` | Walsh transform definition, Parseval's identity | ✅ Yes |
| `Linearized.lean` | Derivative function properties, differential count bounds, APN structure | 1 sorry |
| `Main.lean` | Main theorems: spectrum, difference set, triple correlation | 3 sorries |

### Theorems — Proved (sorry-free, modulo the deep algebraic lemma `derivFun_two_to_one`)

1. **`kasami_differential_uniformity`** — Differential uniformity ≤ 4. Proved via the APN bound (≤ 2) using the 2-to-1 derivative structure.

2. **`walsh_fourth_moment`** — `Σ W⁴ = 2^{3n+1}`. Proved from the quartic relation + Parseval.

3. **`walshSpectrum_three_valued`** — Walsh spectrum ⊂ {0, ±2^{(n+1)/2}}. Proved from the quartic relation via `W²(W² - 2^{n+1}) = 0`.

4. **`deltaFinset_card`** — |Δ| = 2^{n-1}. Proved via fiber counting with the 2-to-1 derivative.

5. **`derivFun_fiber_card`** — Each fiber of the derivative has exactly 2 elements.

6. **`diffCountL_le_two`** / **`diffCountL_le_four`** — APN bound / differential uniformity.

7. **`diffCountL_sum_sq`** — Σ N(t,c)² = 2·2ⁿ. Proved from the APN structure ({0,2}-valued counts).

8. **`diffCountL_even`**, **`diffCountL_eq_zero_or_two`**, **`diffCountL_sum`** — Supporting combinatorial lemmas.

9. **`walshTransform_parseval`** — Parseval's identity for the Walsh transform.

10. **`traceLift_sum_eq_zero`** — Character orthogonality.

### Theorems — Remaining as `sorry` (4 total)

1. **`derivFun_two_to_one`** (Linearized.lean) — The derivative D(b) = F(b)+F(b+1)+1 is exactly 2-to-1. This is the foundational algebraic result requiring linearized polynomial kernel dimension analysis: the equation reduces to a linearized polynomial whose kernel over GF(2^n) has GF(2)-dimension `gcd(k,n) = 1`, giving exactly 2 elements.

2. **`walsh_quartic_relation`** (Main.lean) — W⁴ = 2^{n+1}·W² (the CCD 2000 result). This requires the full autocorrelation analysis using linearized polynomial structure of the Kasami exponent.

3. **`walshTransformSet_deltaFinset_spectrum`** (Main.lean) — Walsh spectrum of Δ ⊂ {0, ±2^{n-1}}.

4. **`deltaSet_tripleCorrelation`** (Main.lean) — P₃: triple correlation = 2^{2n-3}.

### Dependency Structure

All proved theorems ultimately depend on `derivFun_two_to_one` (the deep linearized polynomial result). The quartic relation `walsh_quartic_relation` is the other key deep result; `walsh_fourth_moment` and `walshSpectrum_three_valued` are fully proved conditional on it. The remaining sorry's all require formalizing linearized polynomial theory over finite fields (kernel dimension bounds via gcd conditions), which is not currently available in Mathlib and constitutes a substantial independent formalization project.