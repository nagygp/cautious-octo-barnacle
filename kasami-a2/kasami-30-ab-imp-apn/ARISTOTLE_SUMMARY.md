# Summary of changes for run 5ebc1ff6-3c0d-4171-a946-ba93c6d1a53e
## Decomposition of `ab_implies_apn`

I created `RequestProject/Kasami/ABImpliesAPN.lean`, which decomposes `ab_implies_apn` into 7 tiny lemmas. Here's the proof architecture:

### Proof structure

For a fixed `a ≠ 0`, let `N(b) := |{x : f(x+a) + f(x) = b}|`. We need `N(b) ≤ 2`.

| # | Lemma | Status | Where |
|---|-------|--------|-------|
| 1 | `derivCount_even` — N(b) is always even | ✅ Already proved | `FourthMoment.lean` |
| 2 | `derivCount_sum_int` — ∑_b N(b) = 2^n | ✅ Already proved | `FourthMoment.lean` |
| 3 | `even_sum_sq_bound` — even + sum + sum-sq bound ⟹ N(b) ≤ 2 | ✅ Already proved | `FourthMoment.lean` |
| 4 | `deriv_parseval` — 2^n · ∑_b N(b)² = ∑_c S(c,a)² | ✅ Already proved | `APNFromAB.lean` |
| 5 | `deriv_char_sum_zero` — S(0,a) = 2^n | ✅ Proved (new) | `ABImpliesAPN.lean` |
| 6 | `deriv_char_sum_sq_split` — split ∑_c into c=0 and c≠0 | ✅ Proved (new) | `ABImpliesAPN.lean` |
| 7 | **`ab_deriv_char_sum_sq_nonzero_le`** — ∑_{c≠0} S(c,a)² ≤ (2^n)² | ❌ **Sorry'd** | `ABImpliesAPN.lean` |

### Assembly (all proved from the above)

- `ab_deriv_char_sum_sq_le`: combines lemmas 6+7 → total character sum bound ≤ 2·(2^n)²
- `ab_deriv_sum_sq_le`: uses Parseval (lemma 4) + above → ∑_b N(b)² ≤ 2^{n+1}
- `ab_deriv_sum_sq_le_nat`: casts to ℕ
- **`ab_implies_apn'`**: final assembly using lemmas 1+2+3 + sum-sq bound

### The one remaining sorry

`ab_deriv_char_sum_sq_nonzero_le` is the hard core inequality: for an AB function f and a ≠ 0, the sum ∑_{c≠0} (∑_x χ(c·(f(x+a)+f(x))))² ≤ (2^n)². This connects the Walsh spectrum condition (which constrains the c=1 component) to the character sums for all nonzero c. For **power functions** f(x) = x^d (like the Kasami function), this follows because scalar multiplication by c preserves the Walsh spectrum via the substitution x ↦ c^{1/d}·x, so all component functions inherit the AB property. For general functions, this step may require strengthening the `IsAlmostBent` definition to include all nonzero components (the standard vectorial AB definition).