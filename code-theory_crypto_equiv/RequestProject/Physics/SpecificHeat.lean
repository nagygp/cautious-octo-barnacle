import RequestProject.Physics.InternalEnergy
import RequestProject.CodingTheory.PlessMomentsHigher

/-!
# Energy variance and specific heat of the weight-enumerator spin system

This module continues the **physics** track of
`RequestProject/Physics/InternalEnergy.lean`.  In the statistical-mechanical
reading of a linear code (energy `E(c) = wt(c)`), the infinite-temperature
*energy variance* is the second central moment of the Hamming weight of a
uniformly random codeword,

  `Var(E) = ⟨E²⟩ − ⟨E⟩²`,   `⟨E²⟩ = (1/|C|) Σ_i i² A_i`.

By the fluctuation–dissipation relation the **specific heat** is
`C_v(β) = β² Var(E)`, so at fixed temperature the heat capacity is governed by
the energy variance, which the second Pless power moment
(`pless_second_moment`) expresses through the dual weight distribution.

## Main results

* `meanSqEnergy`, `energyVariance` — `⟨E²⟩` and `Var(E)`.
* `card_sq_mul_energyVariance` — the combinatorial identity
  `|C|²·Var(E) = |C|·Σ_i i²A_i − (Σ_i i A_i)²`.
* `energyVariance_of_dualDist` — when the dual distance is `≥ 3`
  (`B_1 = B_2 = 0`), the variance takes the "random" (binomial) value
  `Var(E) = n(q−1)/q²`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The infinite-temperature **mean square energy** of a linear code `C`: the
mean squared Hamming weight of a uniformly random codeword,
`⟨E²⟩ = (Σ_i i²·A_i)/|C|`. -/
noncomputable def meanSqEnergy (C : Submodule F (ι → F)) : ℝ :=
  (∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℝ) ^ 2 * (weightDistribution C i : ℝ))
    / (Fintype.card C : ℝ)

/-- The infinite-temperature **energy variance** of a linear code `C`,
`Var(E) = ⟨E²⟩ − ⟨E⟩²`. -/
noncomputable def energyVariance (C : Submodule F (ι → F)) : ℝ :=
  meanSqEnergy C - (meanEnergy C) ^ 2

/-
**The energy variance as a combinatorial identity.**
`|C|²·Var(E) = |C|·Σ_i i²A_i − (Σ_i i A_i)²`.
-/
theorem card_sq_mul_energyVariance (C : Submodule F (ι → F)) :
    (Fintype.card C : ℝ) ^ 2 * energyVariance C
      = (Fintype.card C : ℝ)
          * (∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℝ) ^ 2 * (weightDistribution C i : ℝ))
        - (∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℝ) * (weightDistribution C i : ℝ)) ^ 2 := by
  unfold energyVariance;
  unfold meanSqEnergy meanEnergy;
  field_simp

/-
**Random (binomial) energy variance at large dual distance.**  If the dual
distance is at least `3` (`B_1 = B_2 = 0`) then the first two moments of the
weight distribution agree with the binomial `B(n, (q-1)/q)`, and the variance is
the random value `Var(E) = n(q-1)/q²`.  Requires `2 ≤ n`.
-/
theorem energyVariance_of_dualDist (C : Submodule F (ι → F)) (hn : 2 ≤ Fintype.card ι)
    (hB1 : weightDistribution (dualCode C) 1 = 0)
    (hB2 : weightDistribution (dualCode C) 2 = 0) :
    energyVariance C
      = (Fintype.card ι : ℝ) * ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) ^ 2 := by
  rw [ @energyVariance ];
  rw [ meanEnergy, meanSqEnergy, div_pow ];
  rw [ div_sub_div, div_eq_div_iff ];
  · have := @pless_second_moment ι _ F _ _ C hn; have := @pless_first_moment ι _ F _ _ C ( by linarith ) ; simp_all +decide [ ← @Complex.ofReal_inj ] ;
    grind;
  · simp +zetaDelta at *;
  · exact pow_ne_zero 2 ( Nat.cast_ne_zero.mpr Fintype.card_ne_zero );
  · exact Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero );
  · simp +decide

end CodingTheory