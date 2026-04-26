# Summary of changes for run 59215aa2-3307-45ef-ac8e-c8c3e5fee50d
## Summary of Work

I set up the project with the full kasami-14 codebase and the linearized polynomial infrastructure from kasami-09, then worked on proving the CCD factorization and `kasami_is_ab`.

### What Was Accomplished

**New sorry-free files created:**

1. **`RequestProject/Kasami/CCDHelpers.lean`** — Four key algebraic lemmas for the CCD factorization, all proved without sorry:
   - `char2_sum_powers`: In char 2, a^(2^k+1) + b^(2^k+1) = (a+b)^(2^k+1) + a·b^(2^k) + a^(2^k)·b
   - `gold_deriv`: Derivative of the Gold function x^(2^m+1) at direction z
   - `gold_second_deriv`: Second derivative D₁D_z(x^(2^m+1)) = z^(2^m) + z (independent of x)
   - `bilinear_form_factor`: The bilinear form a·b^(2^k) + a^(2^k)·b = b^(2^k+1)·M_k(a/b)

2. **`RequestProject/Kasami/CCDFactorization.lean`** — Additional infrastructure, all sorry-free:
   - `kasamiExp_mul_identity`: The fundamental identity d·(2^k+1) = 2^(3k)+1
   - `F2n_frobenius`: The Frobenius identity x^(2^n) = x in F_{2^n}
   - `char2_add_pow`: Freshman's dream (a+b)^(2^k) = a^(2^k) + b^(2^k)

3. **`RequestProject/Kasami/KasamiFunction.lean`** — Proved key results:
   - `wht_kasamiF_zero`: Walsh transform of the Kasami function at a=0 is zero (using bijection argument via `kasamiExp_permutation`)
   - Decomposed `kasami_is_ab` into the trivial a=0 case (proved) and the deep a≠0 case (`wht_kasamiF_sq_nonzero`, sorry'd)

4. **Imported linearized polynomial infrastructure** from the kasami-09 iteration:
   - `RequestProject/LinearizedPoly/Defs.lean` — Linearized polynomial definitions (L_k, M_k)
   - `RequestProject/LinearizedPoly/Kernel.lean` — Kernel dimension theory
   - `RequestProject/LinearizedPoly/KasamiKernel.lean` — Kasami derivative analysis

### Remaining Sorries (4 total)

1. **`wht_kasamiF_sq_nonzero`** (`KasamiFunction.lean:88`) — The deep part of `kasami_is_ab`: for a ≠ 0, W_f(a)² ∈ {0, 2^(n+1)}. This requires the full CCD factorization connecting the Walsh spectrum to the linearized polynomial kernel, plus quadratic form rank analysis. The helper lemmas in CCDHelpers.lean provide the algebraic building blocks.

2. **`kasamiDiff_eq_implies_linearized`** (`KasamiKernel.lean:91`) — The CCD factorization proper: if D₁h(y₁) = D₁h(y₂), then y₁ = y₂ ∨ y₁ = y₂+1 ∨ L_k(y₁+y₂) = 0. The proved helper lemmas (gold_second_deriv, bilinear_form_factor, etc.) provide the key algebraic steps, but assembling the full proof requires establishing how z^(2^(3k)) = z implies L_k(z) = 0 via the derivative structure.

3. **`ab_implies_apn`** (`AlmostBent.lean:96`) — AB implies APN (independent of P₃ critical path)

4. **`ab_implies_vanishing`** (`TripleCount.lean:120`) — AB implies AlmostBentVanishing (needed for P₃)

### Proof Architecture

The `kasami_is_ab` theorem is now structured as:
```
kasami_is_ab
├── Case a = 0: wht_kasamiF_zero ✅ (proved via bijection + chi_sum_all_zero)
└── Case a ≠ 0: wht_kasamiF_sq_nonzero ❌ (sorry)
    └── Requires CCD factorization + rank analysis
        ├── kasamiExp_mul_identity ✅ (d·(2^k+1) = 2^(3k)+1)
        ├── gold_second_deriv ✅ (D₁D_z(x^(2^m+1)) = z^(2^m)+z)
        ├── char2_sum_powers ✅ (char 2 norm factorization)
        ├── bilinear_form_factor ✅ (bilinear form = norm·M_k)
        └── [gap: assembling these into the full Walsh spectrum argument]
```

These are deep research-level theorems (Kasami 1971 / Canteaut-Charpin-Dobbertin 2000) that typically require hundreds of lines of formal proof for the remaining gap.