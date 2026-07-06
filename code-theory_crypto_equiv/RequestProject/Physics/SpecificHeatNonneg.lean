import RequestProject.Physics.SpecificHeat

/-!
# Nonnegativity of the energy variance and the specific heat

This module continues the **physics** track of
`RequestProject/Physics/SpecificHeat.lean`.  Thermodynamic stability requires the
heat capacity of any physical system to be nonnegative; in the
statistical-mechanical reading of a linear code this is the statement that the
energy variance (the second central moment of the Hamming weight of a uniformly
random codeword) is nonnegative, and hence so is the specific heat
`C_v(β) = β² Var(E)`.

The mathematical content is the Cauchy–Schwarz inequality applied to the weight
distribution: `(Σ_i i A_i)² ≤ (Σ_i A_i)(Σ_i i² A_i) = |C| Σ_i i² A_i`.

## Main results

* `energyVariance_nonneg` — `0 ≤ Var(E)`.
* `specificHeat` — the specific heat `C_v(β) = β² Var(E)`.
* `specificHeat_nonneg` — `0 ≤ C_v(β)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
**The energy variance is nonnegative.**  `0 ≤ Var(E)` for every linear code,
by Cauchy–Schwarz applied to the weight distribution.
-/
theorem energyVariance_nonneg (C : Submodule F (ι → F)) :
    0 ≤ energyVariance C := by
  refine' sub_nonneg_of_le _;
  convert ( Finset.sum_mul_sq_le_sq_mul_sq _ _ _ ) using 1;
  any_goals exact Finset.range ( Fintype.card ι + 1 );
  rotate_left;
  rotate_left;
  all_goals try infer_instance;
  use fun i => Real.sqrt ( weightDistribution C i );
  use fun i => ( i : ℝ ) * Real.sqrt ( weightDistribution C i ) / Fintype.card C;
  · simp +decide [ mul_div, mul_comm, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, meanEnergy ];
    rw [ Finset.sum_div _ _ _ ];
  · simp +decide [ meanSqEnergy, mul_pow, div_pow, Finset.sum_div _ _ _, Real.sq_sqrt ( Nat.cast_nonneg _ ) ];
    simp +decide [ ← Finset.sum_div _ _ _, ← Finset.sum_mul, sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_div, div_eq_mul_inv ];
    rw [ show ( ∑ i ∈ Finset.range ( Fintype.card ι + 1 ), ( weightDistribution C i : ℝ ) ) = Fintype.card C from mod_cast pless_zeroth_moment C ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Fintype.card_pos ) ]

/-- The **specific heat** `C_v(β) = β² Var(E)` of the weight-enumerator spin
system at inverse temperature `β`. -/
noncomputable def specificHeat (C : Submodule F (ι → F)) (β : ℝ) : ℝ :=
  β ^ 2 * energyVariance C

/-- **The specific heat is nonnegative** (thermodynamic stability):
`0 ≤ C_v(β)` for every inverse temperature `β`. -/
theorem specificHeat_nonneg (C : Submodule F (ι → F)) (β : ℝ) :
    0 ≤ specificHeat C β := by
  unfold specificHeat
  exact mul_nonneg (sq_nonneg _) (energyVariance_nonneg C)

end CodingTheory