import RequestProject.CodingTheory.PlessMomentsHigher

set_option maxHeartbeats 1600000

/-!
# The third Pless power moment (`K₃`)

This module continues `RequestProject/CodingTheory/PlessMomentsHigher.lean`,
supplying the cubic polynomial form of the third Krawtchouk value `K₃` and the
**third Pless power moment**, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977
  (Ch. 5, §2).

## Main results

* `six_mul_krawtchouk_three` — the polynomial form (cleared of the factor `1/6`)
  `6·K₃(x) = -q³ x³ + c₂ x² + c₁ x + c₀`, with
  `c₂ = 3(n-1)(q-1)³ + 3(2n-1)(q-1)² + 3(n+1)(q-1) + 3`,
  `c₁ = (-3n²+6n-2)(q-1)³ + (-3n²+3n)(q-1)² - 3n(q-1) - 2`,
  `c₀ = (q-1)³ n(n-1)(n-2)`.
* `pless_third_moment` — the third power moment in recursive cleared form, read
  off `macwilliams_distribution` at `k = 3`:
  `q³ Σ_i i³ A_i = c₂ Σ_i i² A_i + c₁ Σ_i i A_i + c₀ |C| - 6 |C| B₃`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
**The third Krawtchouk value in polynomial form** (cleared of the factor `1/6`):
for `x ≤ n`,
`6·K₃(x) = -q³ x³
  + (3(n-1)(q-1)³ + 3(2n-1)(q-1)² + 3(n+1)(q-1) + 3) x²
  + ((-3n²+6n-2)(q-1)³ + (-3n²+3n)(q-1)² - 3n(q-1) - 2) x
  + (q-1)³ n(n-1)(n-2)`.
-/
theorem six_mul_krawtchouk_three (q n x : ℕ) (hx : x ≤ n) :
    6 * krawtchouk q n 3 x
      = -((q : ℤ) ^ 3) * (x : ℤ) ^ 3
        + (3 * ((n : ℤ) - 1) * ((q : ℤ) - 1) ^ 3
            + 3 * (2 * (n : ℤ) - 1) * ((q : ℤ) - 1) ^ 2
            + 3 * ((n : ℤ) + 1) * ((q : ℤ) - 1) + 3) * (x : ℤ) ^ 2
        + ((-3 * (n : ℤ) ^ 2 + 6 * (n : ℤ) - 2) * ((q : ℤ) - 1) ^ 3
            + (-3 * (n : ℤ) ^ 2 + 3 * (n : ℤ)) * ((q : ℤ) - 1) ^ 2
            - 3 * (n : ℤ) * ((q : ℤ) - 1) - 2) * (x : ℤ)
        + ((q : ℤ) - 1) ^ 3 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  rw [krawtchouk_three q n x hx];
  have h3 : ∀ m : ℕ, (m.choose 3 : ℤ) * 6 = m * (m - 1) * (m - 2) := by
    intro m; induction m <;> simp_all +decide [ Nat.choose ] ; ring;
    rename_i k hk; rw [ hk ] ; rw [ Nat.choose_two_right ] ; ring;
    cases k <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] ; ring;
    linarith [ Int.ediv_mul_cancel ( show 2 ∣ ( ↑‹ℕ› : ℤ ) + ↑‹ℕ› ^ 2 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ) ]
  have h2 : ∀ m : ℕ, (m.choose 2 : ℤ) * 2 = m * (m - 1) := by
    exact fun m => by induction m <;> simp +decide [ Nat.choose, * ] ; linarith;
  have := h3 ( n - x ) ; have := h2 ( n - x ) ; have := h3 x; have := h2 x; norm_num [ Nat.cast_sub hx ] at * ; ring_nf at *;
  grind

/-
**The third Pless power moment** (MacWilliams–Sloane, Ch. 5, §2), in the
recursive cleared form over `ℂ`.  With `A_i = weightDistribution C i`,
`B_3 = weightDistribution Cᗮ 3`, `n = #ι`, `q = #F`:

`q³ Σ_i i³ A_i = c₂ Σ_i i² A_i + c₁ Σ_i i A_i + c₀ |C| - 6 |C| B_3`,

with the coefficients of `six_mul_krawtchouk_three`.  Requires `3 ≤ n`.
-/
theorem pless_third_moment (C : Submodule F (ι → F)) (hn : 3 ≤ Fintype.card ι) :
    (Fintype.card F : ℂ) ^ 3 *
        ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 3 * (weightDistribution C i : ℂ)
      = (3 * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 3
            + 3 * (2 * (Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 2
            + 3 * ((Fintype.card ι : ℂ) + 1) * ((Fintype.card F : ℂ) - 1) + 3)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 2 * (weightDistribution C i : ℂ)
        + ((-3 * (Fintype.card ι : ℂ) ^ 2 + 6 * (Fintype.card ι : ℂ) - 2) * ((Fintype.card F : ℂ) - 1) ^ 3
            + (-3 * (Fintype.card ι : ℂ) ^ 2 + 3 * (Fintype.card ι : ℂ)) * ((Fintype.card F : ℂ) - 1) ^ 2
            - 3 * (Fintype.card ι : ℂ) * ((Fintype.card F : ℂ) - 1) - 2)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) * (weightDistribution C i : ℂ)
        + ((Fintype.card F : ℂ) - 1) ^ 3 * (Fintype.card ι : ℂ)
            * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card ι : ℂ) - 2) * (Fintype.card C : ℂ)
        - 6 * (Fintype.card C : ℂ) * (weightDistribution (dualCode C) 3 : ℂ) := by
  rw [ macwilliams_distribution C 3 ( by omega ) ];
  -- Now use the given formula to simplify the expression.
  have h_simp : ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (6 * (krawtchouk (Fintype.card F) (Fintype.card ι) 3 i : ℂ)) =
    ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (-((Fintype.card F : ℂ) ^ 3) * (i : ℂ) ^ 3 +
      (3 * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 3 +
      3 * (2 * (Fintype.card ι : ℂ) - 1) * ((Fintype.card F : ℂ) - 1) ^ 2 +
      3 * ((Fintype.card ι : ℂ) + 1) * ((Fintype.card F : ℂ) - 1) + 3) * (i : ℂ) ^ 2 +
      ((-3 * (Fintype.card ι : ℂ) ^ 2 + 6 * (Fintype.card ι : ℂ) - 2) * ((Fintype.card F : ℂ) - 1) ^ 3 +
      (-3 * (Fintype.card ι : ℂ) ^ 2 + 3 * (Fintype.card ι : ℂ)) * ((Fintype.card F : ℂ) - 1) ^ 2 -
      3 * (Fintype.card ι : ℂ) * ((Fintype.card F : ℂ) - 1) - 2) * (i : ℂ) +
      ((Fintype.card F : ℂ) - 1) ^ 3 * (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) - 1) * ((Fintype.card ι : ℂ) - 2)) := by
        refine' Finset.sum_congr rfl fun i hi => _;
        norm_cast;
        rw [ six_mul_krawtchouk_three ] ; norm_num [ Int.subNatNat_eq_coe ] ; ring;
        · grind;
        · linarith [ Finset.mem_range.mp hi ];
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, pless_zeroth_moment ] ; ring;
  rw [ show ( ∑ x ∈ Finset.range ( 1 + Fintype.card ι ), ( weightDistribution C x : ℂ ) ) = Fintype.card C from mod_cast by rw [ add_comm, pless_zeroth_moment ] ] ; ring

end CodingTheory