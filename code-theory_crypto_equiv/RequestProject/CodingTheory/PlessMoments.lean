import RequestProject.CodingTheory.MacWilliamsDistribution

/-!
# Pless power moments of the weight distribution

This module continues the MacWilliams coding-theory spine
(`RequestProject/CodingTheory/MacWilliamsDistribution.lean`), transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977
  (Ch. 5, §2: the power moments of the distance distribution).

The **Pless power moments** express the moments `Σ_i i^ν A_i` of the weight
distribution `A_i = weightDistribution C i` in terms of the dual weight
distribution `B_k = weightDistribution Cᗮ k`.  They are obtained from the
MacWilliams identity `macwilliams_distribution` by evaluating it at small `k`
using the explicit Krawtchouk values `K_0(i) = 1` and `K_1(i) = (q-1)n - q·i`.

## Main results

* `krawtchouk_one` — the first Krawtchouk value `K_1(x) = (q-1)·n - q·x`
  (for `x ≤ n`).
* `pless_zeroth_moment` — `Σ_i A_i = |C|` (the `ν = 0` moment).
* `pless_first_moment` — the `ν = 1` moment, in cleared form
  `q · Σ_i i·A_i = |C| · ((q-1)·n − B_1)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
The first **Krawtchouk value**: `K_1(x) = (q-1)·n - q·x` for `x ≤ n`.
-/
theorem krawtchouk_one (q n x : ℕ) (hx : x ≤ n) :
    krawtchouk q n 1 x = ((q : ℤ) - 1) * (n : ℤ) - (q : ℤ) * (x : ℤ) := by
  unfold krawtchouk;
  norm_num [ Finset.sum_range_succ ] ; ring;
  rw [ Nat.cast_sub hx ] ; ring

/-- **The zeroth Pless power moment.** `Σ_i A_i = |C|`. -/
theorem pless_zeroth_moment (C : Submodule F (ι → F)) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1), weightDistribution C i = Fintype.card C :=
  sum_weightDistribution C

/-
**The first Pless power moment** (MacWilliams–Sloane, Ch. 5, §2), in cleared
form over `ℂ`:
`q · Σ_i i·A_i = |C| · ((q-1)·n − B_1)`,
where `A_i = weightDistribution C i`, `B_1 = weightDistribution Cᗮ 1`,
`n = #ι`, `q = #F`.  Requires `1 ≤ n` so that the dual weight `B_1` is in range.
-/
theorem pless_first_moment (C : Submodule F (ι → F)) (hn : 1 ≤ Fintype.card ι) :
    (Fintype.card F : ℂ) *
        ∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℂ) * (weightDistribution C i : ℂ)
      = (Fintype.card C : ℂ) *
          (((Fintype.card F : ℂ) - 1) * (Fintype.card ι : ℂ)
            - (weightDistribution (dualCode C) 1 : ℂ)) := by
  have := CodingTheory.macwilliams_distribution C 1 (by linarith);
  rw [ inv_mul_eq_div, eq_div_iff ] at this;
  · rw [ Finset.sum_congr rfl fun i hi => by rw [ krawtchouk_one _ _ _ ( Finset.mem_range_succ_iff.mp hi ) ] ] at this;
    norm_num [ Finset.sum_add_distrib, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] at *;
    simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ];
    have := pless_zeroth_moment C; norm_cast at *; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  · exact Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero )

end CodingTheory