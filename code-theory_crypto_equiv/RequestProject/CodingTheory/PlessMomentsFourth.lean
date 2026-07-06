import RequestProject.CodingTheory.PlessMomentsThird

set_option maxHeartbeats 3200000

/-!
# The fourth Pless power moment (`K₄`)

This module continues `RequestProject/CodingTheory/PlessMomentsThird.lean`,
supplying the quartic polynomial form of the fourth Krawtchouk value `K₄` and the
**fourth Pless power moment**, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977
  (Ch. 5, §2).

## Main results

* `krawtchouk_four` — the fourth Krawtchouk value in choose form,
  `K₄(x) = (q-1)⁴ C(n-x,4) - (q-1)³ x C(n-x,3) + (q-1)² C(x,2) C(n-x,2)
    - (q-1) C(x,3)(n-x) + C(x,4)`.
* `twentyfour_mul_krawtchouk_four` — the polynomial form (cleared of the factor
  `1/24`): `24·K₄(x) = q⁴ x⁴ + c₃ x³ + c₂ x² + c₁ x + c₀`, with the coefficients
  written in the `(q-1)` basis (verified with a computer-algebra system).
* `pless_fourth_moment` — the fourth power moment in recursive cleared form, read
  off `macwilliams_distribution` at `k = 4`:
  `q⁴ Σ_i i⁴ A_i = -c₃ Σ_i i³ A_i - c₂ Σ_i i² A_i - c₁ Σ_i i A_i - c₀ |C|
    + 24 |C| B₄` (the even-degree leading term `+q⁴` flips the signs of the
  lower moments and the dual term relative to the odd third moment).
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
The fourth **Krawtchouk value** in choose form (with `ℕ`-truncated `n - x`, so
valid for all `x`):
`K₄(x) = (q-1)⁴ C(n-x,4) - (q-1)³ x C(n-x,3) + (q-1)² C(x,2) C(n-x,2)
  - (q-1) C(x,3)(n-x) + C(x,4)`.
-/
theorem krawtchouk_four (q n x : ℕ) :
    krawtchouk q n 4 x
      = ((q : ℤ) - 1) ^ 4 * ((n - x).choose 4 : ℤ)
        - ((q : ℤ) - 1) ^ 3 * (x : ℤ) * ((n - x).choose 3 : ℤ)
        + ((q : ℤ) - 1) ^ 2 * (x.choose 2 : ℤ) * ((n - x).choose 2 : ℤ)
        - ((q : ℤ) - 1) * (x.choose 3 : ℤ) * ((n - x : ℕ) : ℤ)
        + (x.choose 4 : ℤ) := by
  unfold krawtchouk;
  norm_num [ Finset.sum_range_succ ] ; ring

/-
**The fourth Krawtchouk value in polynomial form** (cleared of the factor
`1/24`): for `x ≤ n`,
`24·K₄(x) = q⁴ x⁴ + c₃ x³ + c₂ x² + c₁ x + c₀`, where, with `p = q-1`,
* `c₃ = -2(2n-3)p⁴ - 12(n-1)p³ - 12n p² - 4(n+3)p - 6`,
* `c₂ = (6n²-18n+11)p⁴ + 4(3n²-6n+2)p³ + 6(n²+n-1)p² + 4(3n+2)p + 11`,
* `c₁ = -2(2n-3)(n²-3n+1)p⁴ - 4n(n-2)(n-1)p³ - 6n(n-1)p² - 8n p - 6`,
* `c₀ = p⁴ n(n-1)(n-2)(n-3)`.
-/
theorem twentyfour_mul_krawtchouk_four (q n x : ℕ) (hx : x ≤ n) :
    24 * krawtchouk q n 4 x
      = (q : ℤ) ^ 4 * (x : ℤ) ^ 4
        + (-2 * (2 * (n : ℤ) - 3) * ((q : ℤ) - 1) ^ 4
            - 12 * ((n : ℤ) - 1) * ((q : ℤ) - 1) ^ 3
            - 12 * (n : ℤ) * ((q : ℤ) - 1) ^ 2
            - 4 * ((n : ℤ) + 3) * ((q : ℤ) - 1) - 6) * (x : ℤ) ^ 3
        + ((6 * (n : ℤ) ^ 2 - 18 * (n : ℤ) + 11) * ((q : ℤ) - 1) ^ 4
            + 4 * (3 * (n : ℤ) ^ 2 - 6 * (n : ℤ) + 2) * ((q : ℤ) - 1) ^ 3
            + 6 * ((n : ℤ) ^ 2 + (n : ℤ) - 1) * ((q : ℤ) - 1) ^ 2
            + 4 * (3 * (n : ℤ) + 2) * ((q : ℤ) - 1) + 11) * (x : ℤ) ^ 2
        + (-2 * (2 * (n : ℤ) - 3) * ((n : ℤ) ^ 2 - 3 * (n : ℤ) + 1) * ((q : ℤ) - 1) ^ 4
            - 4 * (n : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) - 1) * ((q : ℤ) - 1) ^ 3
            - 6 * (n : ℤ) * ((n : ℤ) - 1) * ((q : ℤ) - 1) ^ 2
            - 8 * (n : ℤ) * ((q : ℤ) - 1) - 6) * (x : ℤ)
        + ((q : ℤ) - 1) ^ 4 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
  convert congr_arg ( fun x : ℤ => 24 * x ) ( krawtchouk_four q n x ) using 1 ; ring;
  -- By definition of binomial coefficients, we know that $\binom{n}{k} = \frac{n!}{k!(n-k)!}$.
  have h_binom : ∀ m k : ℕ, (m.choose k : ℤ) * (Nat.factorial k) = ∏ i ∈ Finset.range k, (m - i : ℤ) := by
    intros m k; norm_cast; rcases le_or_gt k m with h | h <;> simp_all +decide [ Nat.choose_eq_zero_of_lt, mul_comm ] ;
    · rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
      rw [ Nat.descFactorial_eq_prod_range ];
      rw [ Nat.cast_prod, Finset.prod_congr rfl fun i hi => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hi ] ) ];
    · rw [ Finset.prod_eq_zero ( Finset.mem_range.mpr h ) ] ; norm_num [ Int.subNatNat_eq_coe ];
  have := h_binom x 4; have := h_binom ( n - x ) 4; have := h_binom x 3; have := h_binom ( n - x ) 3; have := h_binom x 2; have := h_binom ( n - x ) 2; simp_all +decide ;
  have := h_binom x 3; have := h_binom ( n - x ) 3; have := h_binom x 4; have := h_binom ( n - x ) 4; norm_num [ Finset.prod_range_succ ] at * ;
  grind

/-
**Distributing a degree-4 polynomial weight over the weight distribution.**
For any coefficients `a b c d e : ℂ`,
`Σ_i A_i (a i⁴ + b i³ + c i² + d i + e) = a M₄ + b M₃ + c M₂ + d M₁ + e |C|`,
where `M_ν = Σ_i i^ν A_i` and `Σ_i A_i = |C|` (`pless_zeroth_moment`).
-/
theorem sum_weight_mul_poly_four (C : Submodule F (ι → F)) (a b c d e : ℂ) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ)
        * (a * (i : ℂ) ^ 4 + b * (i : ℂ) ^ 3 + c * (i : ℂ) ^ 2 + d * (i : ℂ) + e)
      = a * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 4 * (weightDistribution C i : ℂ)
        + b * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 3 * (weightDistribution C i : ℂ)
        + c * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 2 * (weightDistribution C i : ℂ)
        + d * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) * (weightDistribution C i : ℂ)
        + e * (Fintype.card C : ℂ) := by
  simp +decide only [mul_add, mul_comm, sum_add_distrib, Finset.mul_sum _ _ _];
  simp +decide only [mul_left_comm, mul_assoc];
  have h_sum : ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) = (Fintype.card C : ℂ) := by
    exact_mod_cast pless_zeroth_moment C;
  rw [ ← h_sum, Finset.mul_sum _ _ _ ]

/-
**The fourth Pless power moment** (MacWilliams–Sloane, Ch. 5, §2), in the
recursive cleared form over `ℂ`.  With `A_i = weightDistribution C i`,
`B_4 = weightDistribution Cᗮ 4`, `n = #ι`, `q = #F`:

`q⁴ Σ_i i⁴ A_i = -c₃ Σ_i i³ A_i - c₂ Σ_i i² A_i - c₁ Σ_i i A_i - c₀ |C|
  + 24 |C| B_4`,

where `c₃, c₂, c₁, c₀` are the coefficients of `twentyfour_mul_krawtchouk_four`.
Unlike the odd third moment, the even-degree leading Krawtchouk term is `+q⁴`,
so the lower moments and the dual term enter with the **opposite** sign.
Requires `4 ≤ n`.
-/
theorem pless_fourth_moment (C : Submodule F (ι → F)) (hn : 4 ≤ Fintype.card ι) :
    (Fintype.card F : ℂ) ^ 4 *
        ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 4 * (weightDistribution C i : ℂ)
      = (2 * (2 * (Fintype.card ι : ℂ) - 3) * ((Fintype.card F : ℂ) - 1) ^ 4
            + 12 * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 3
            + 12 * (Fintype.card ι : ℂ) * ((Fintype.card F : ℂ) - 1) ^ 2
            + 4 * ((Fintype.card ι : ℂ) + 3) * ((Fintype.card F : ℂ) - 1) + 6)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 3 * (weightDistribution C i : ℂ)
        + (-(6 * (Fintype.card ι : ℂ) ^ 2 - 18 * (Fintype.card ι : ℂ) + 11) * ((Fintype.card F : ℂ) - 1) ^ 4
            - 4 * (3 * (Fintype.card ι : ℂ) ^ 2 - 6 * (Fintype.card ι : ℂ) + 2) * ((Fintype.card F : ℂ) - 1) ^ 3
            - 6 * ((Fintype.card ι : ℂ) ^ 2 + (Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 2
            - 4 * (3 * (Fintype.card ι : ℂ) + 2) * ((Fintype.card F : ℂ) - 1) - 11)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 2 * (weightDistribution C i : ℂ)
        + (2 * (2 * (Fintype.card ι : ℂ) - 3) * ((Fintype.card ι : ℂ) ^ 2 - 3 * (Fintype.card ι : ℂ) + 1) * ((Fintype.card F : ℂ) - 1) ^ 4
            + 4 * (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) - 2) * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 3
            + 6 * (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 2
            + 8 * (Fintype.card ι : ℂ) * ((Fintype.card F : ℂ) - 1) + 6)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) * (weightDistribution C i : ℂ)
        - ((Fintype.card F : ℂ) - 1) ^ 4 * (Fintype.card ι : ℂ)
            * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card ι : ℂ) - 2) * ((Fintype.card ι : ℂ) - 3)
            * (Fintype.card C : ℂ)
        + 24 * (Fintype.card C : ℂ) * (weightDistribution (dualCode C) 4 : ℂ) := by
  set Q : ℂ := (Fintype.card F : ℂ)
  set N : ℂ := (Fintype.card ι : ℂ)
  set m : ℂ := (Fintype.card C : ℂ);
  have h_B4 : 24 * m * (weightDistribution (dualCode C) 4 : ℂ) = ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (24 * (krawtchouk (Fintype.card F) (Fintype.card ι) 4 i : ℂ)) := by
    have h_B4 : (weightDistribution (dualCode C) 4 : ℂ) = m⁻¹ * ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (krawtchouk (Fintype.card F) (Fintype.card ι) 4 i : ℂ) := by
      convert macwilliams_distribution C 4 ( by linarith ) using 1;
    rw [ h_B4, mul_comm ];
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  have h_sum : ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (24 * (krawtchouk (Fintype.card F) (Fintype.card ι) 4 i : ℂ)) =
    ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (Q^4 * (i : ℂ)^4 + (-2 * (2 * N - 3) * (Q - 1)^4 - 12 * (N - 1) * (Q - 1)^3 - 12 * N * (Q - 1)^2 - 4 * (N + 3) * (Q - 1) - 6) * (i : ℂ)^3 + ((6 * N^2 - 18 * N + 11) * (Q - 1)^4 + 4 * (3 * N^2 - 6 * N + 2) * (Q - 1)^3 + 6 * (N^2 + N - 1) * (Q - 1)^2 + 4 * (3 * N + 2) * (Q - 1) + 11) * (i : ℂ)^2 + (-2 * (2 * N - 3) * (N^2 - 3 * N + 1) * (Q - 1)^4 - 4 * N * (N - 2) * (N - 1) * (Q - 1)^3 - 6 * N * (N - 1) * (Q - 1)^2 - 8 * N * (Q - 1) - 6) * (i : ℂ) + (Q - 1)^4 * N * (N - 1) * (N - 2) * (N - 3)) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      convert congr_arg ( fun x : ℤ => ( weightDistribution C i : ℂ ) * x ) ( twentyfour_mul_krawtchouk_four ( Fintype.card F ) ( Fintype.card ι ) i ( Finset.mem_range_succ_iff.mp hi ) ) using 1 ; norm_cast;
      norm_num +zetaDelta at *;
  rw [ h_B4, h_sum, sum_weight_mul_poly_four ];
  ring

end CodingTheory