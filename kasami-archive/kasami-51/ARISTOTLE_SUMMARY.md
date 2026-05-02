# Summary of changes for run 97a1413f-09a9-4f7b-8f73-ed38d0a40478
Created `RequestProject/QuadraticFourier.lean` with all proofs fully verified (no sorries, only standard axioms).

### What was proved

1. **`walsh_int_values`** (Key lemma): If `W² = 2^(n+1)` and `n` is odd, then `W = 2^((n+1)/2)` or `W = -2^((n+1)/2)`. The proof lifts to `natAbs` via `Int.natAbs_sq`, rewrites the exponent using the fact that `n+1` is even (since `n` is odd), and concludes with `Int.natAbs_eq_iff`.

2. **`walsh_spectrum_values`** (Assembly theorem): For a quadratic Boolean function on GF(2^n) with n odd, every Walsh value `W` satisfying `W = 0 ∨ W² = 2^(n+1)` belongs to the explicit set `{0, 2^((n+1)/2), -2^((n+1)/2)}`.

### Supporting sublemmas (all proved, no sorries)

- `int_eq_or_neg_of_natAbs_eq`: If `W.natAbs = k` then `W = k` or `W = -k`.
- `nat_sq_inj`: Square function is injective on ℕ.
- `natAbs_eq_of_sq_eq_pow`: If `W² = 2^(2k)` then `W.natAbs = 2^k`.

The proof structure is high-level as requested: the main `walsh_int_values` theorem delegates to three clean sublemmas, each with a short proof.