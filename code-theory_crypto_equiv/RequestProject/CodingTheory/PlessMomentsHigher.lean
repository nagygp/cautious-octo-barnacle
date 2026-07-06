import RequestProject.CodingTheory.PlessMoments

/-!
# Higher Pless power moments (second moment; `K₂`, `K₃`)

This module continues `RequestProject/CodingTheory/PlessMoments.lean`, supplying
the next **Krawtchouk values** and the **second Pless power moment**, transcribed
from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977
  (Ch. 5, §2).

## Main results

* `krawtchouk_two` — `K₂(x) = (q-1)² C(n-x,2) - (q-1)·x·(n-x) + C(x,2)`.
* `krawtchouk_three` — `K₃(x) = (q-1)³ C(n-x,3) - (q-1)² x C(n-x,2)
  + (q-1) C(x,2)(n-x) - C(x,3)`.
* `two_mul_krawtchouk_two` — the polynomial form
  `2·K₂(x) = q² x² + (-2(q-1)²n + (q-1)² - 2(q-1)n - 1) x + (q-1)² n(n-1)`.
* `pless_second_moment` — the second power moment, in the recursive cleared form
  `q² · Σ_i i² A_i = 2|C| B_2 + (2(q-1)²n - (q-1)² + 2(q-1)n + 1)·Σ_i i A_i
  − (q-1)² n(n-1) |C|`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
The second **Krawtchouk value**:
`K₂(x) = (q-1)² C(n-x,2) - (q-1)·x·(n-x) + C(x,2)` (for `x ≤ n`).
-/
theorem krawtchouk_two (q n x : ℕ) (hx : x ≤ n) :
    krawtchouk q n 2 x
      = ((q : ℤ) - 1) ^ 2 * ((n - x).choose 2 : ℤ)
        - ((q : ℤ) - 1) * (x : ℤ) * ((n - x : ℕ) : ℤ)
        + (x.choose 2 : ℤ) := by
  unfold krawtchouk;
  norm_num [ Finset.sum_range_succ ] ; ring;

/-
The third **Krawtchouk value**:
`K₃(x) = (q-1)³ C(n-x,3) - (q-1)² x C(n-x,2) + (q-1) C(x,2)(n-x) - C(x,3)`
(for `x ≤ n`).
-/
theorem krawtchouk_three (q n x : ℕ) (hx : x ≤ n) :
    krawtchouk q n 3 x
      = ((q : ℤ) - 1) ^ 3 * ((n - x).choose 3 : ℤ)
        - ((q : ℤ) - 1) ^ 2 * (x : ℤ) * ((n - x).choose 2 : ℤ)
        + ((q : ℤ) - 1) * (x.choose 2 : ℤ) * ((n - x : ℕ) : ℤ)
        - (x.choose 3 : ℤ) := by
  simp +decide [ Finset.sum_range_succ, krawtchouk ];
  grind

/-
**The second Krawtchouk value in polynomial form** (cleared of the factor
`1/2`): for `x ≤ n`,
`2·K₂(x) = q² x² + (-2(q-1)²n + (q-1)² - 2(q-1)n - 1) x + (q-1)² n(n-1)`.
-/
theorem two_mul_krawtchouk_two (q n x : ℕ) (hx : x ≤ n) :
    2 * krawtchouk q n 2 x
      = (q : ℤ) ^ 2 * (x : ℤ) ^ 2
        + (-2 * ((q : ℤ) - 1) ^ 2 * (n : ℤ) + ((q : ℤ) - 1) ^ 2
            - 2 * ((q : ℤ) - 1) * (n : ℤ) - 1) * (x : ℤ)
        + ((q : ℤ) - 1) ^ 2 * (n : ℤ) * ((n : ℤ) - 1) := by
  convert congr_arg ( fun z : ℤ => 2 * z ) ( krawtchouk_two q n x hx ) using 1 ; ring;
  -- Simplify the terms involving combinations and binomial coefficients.
  have h_binom : ∀ m : ℕ, (m.choose 2 : ℤ) * 2 = m * (m - 1) := by
    exact fun m => by induction m <;> simp +decide [ Nat.choose, * ] ; linarith;
  grind +splitIndPred

/-
**The second Pless power moment** (MacWilliams–Sloane, Ch. 5, §2), in the
recursive cleared form over `ℂ`.  With `A_i = weightDistribution C i`,
`B_2 = weightDistribution Cᗮ 2`, `n = #ι`, `q = #F`:

`q² · Σ_i i² A_i = 2|C| B_2 + (2(q-1)²n - (q-1)² + 2(q-1)n + 1)·Σ_i i A_i
  − (q-1)² n(n-1) |C|`.

Requires `2 ≤ n` so that the dual weight `B_2` is in range.
-/
theorem pless_second_moment (C : Submodule F (ι → F)) (hn : 2 ≤ Fintype.card ι) :
    (Fintype.card F : ℂ) ^ 2 *
        ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) ^ 2 * (weightDistribution C i : ℂ)
      = 2 * (Fintype.card C : ℂ) * (weightDistribution (dualCode C) 2 : ℂ)
        + (2 * ((Fintype.card F : ℂ) - 1) ^ 2 * (Fintype.card ι : ℂ)
            - ((Fintype.card F : ℂ) - 1) ^ 2
            + 2 * ((Fintype.card F : ℂ) - 1) * (Fintype.card ι : ℂ) + 1)
          * ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) * (weightDistribution C i : ℂ)
        - ((Fintype.card F : ℂ) - 1) ^ 2 * (Fintype.card ι : ℂ)
            * ((Fintype.card ι : ℂ) - 1) * (Fintype.card C : ℂ) := by
  have h_eq : 2 * (Fintype.card C : ℂ) * (weightDistribution (dualCode C) 2 : ℂ) = ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℂ) * (2 * (krawtchouk (Fintype.card F) (Fintype.card ι) 2 i : ℂ)) := by
    convert congr_arg ( fun x : ℂ => 2 * ( Fintype.card C : ℂ ) * x ) ( macwilliams_distribution C 2 ( by linarith ) ) using 1;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Fintype.card_ne_zero ];
  rw [ h_eq ];
  rw [ show ( ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( weightDistribution C i : ℂ ) * ( 2 * ( krawtchouk ( Fintype.card F ) ( Fintype.card ι ) 2 i : ℂ ) ) ) = ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( weightDistribution C i : ℂ ) * ( ( Fintype.card F : ℂ ) ^ 2 * ( i : ℂ ) ^ 2 + ( -2 * ( Fintype.card F - 1 ) ^ 2 * ( Fintype.card ι : ℂ ) + ( Fintype.card F - 1 ) ^ 2 - 2 * ( Fintype.card F - 1 ) * ( Fintype.card ι : ℂ ) - 1 ) * ( i : ℂ ) + ( Fintype.card F - 1 ) ^ 2 * ( Fintype.card ι : ℂ ) * ( Fintype.card ι - 1 ) ) from ?_ ];
  · simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_add_distrib ];
    rw [ show ( ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( weightDistribution C i : ℂ ) ) = Fintype.card C from mod_cast pless_zeroth_moment C ] ; ring;
  · exact Finset.sum_congr rfl fun i hi => congr_arg _ ( mod_cast two_mul_krawtchouk_two _ _ _ ( Finset.mem_range_succ_iff.mp hi ) )

end CodingTheory