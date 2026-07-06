import RequestProject.Physics.PartitionFunction

/-!
# Free energy of the weight-enumerator statistical-mechanical system

This module continues the **physics** track begun in
`RequestProject/Physics/PartitionFunction.lean`, where the weight enumerator of a
linear code `C` is read as the partition function

  `Z_C(y) = Σ_{c ∈ C} y^{wt c}`,   `y = e^{-β}`,

of a system of non-interacting spins with energy = Hamming weight, and the
MacWilliams identity is a Kramers–Wannier (high/low-temperature) duality.

Here we add the **free energy**

  `F_C(β) = −β^{-1} log Z_C(e^{-β})`,

the standard thermodynamic potential, and record its two basic properties:

* `codeZ_pos` — the partition function is strictly positive at positive Boltzmann
  weight (so its logarithm, hence the free energy, is well defined);
* `codeZ_eq_exp_neg_beta_freeEnergy` — the defining relation `Z = e^{-βF}`;
* `freeEnergy_dualCode_relation` — the **dual-temperature relation** for the free
  energy, the logarithmic form of the Kramers–Wannier duality
  `macwilliams_partition_dual_temp`: at inverse temperature `β > 0`, with dual
  Boltzmann weight `y* = (1 - y)/(1 + (q-1)y)` (`y = e^{-β}`),

  `−β · F_{Cᗮ}(β) = n · log(1 + (q-1)y) − log|C| + log Z_C(y*)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The **free energy** of a linear code `C` at inverse temperature `β`:
`F_C(β) = −β^{-1} log Z_C(e^{-β})`, the thermodynamic potential of the
weight-enumerator spin system. -/
noncomputable def freeEnergy (C : Submodule F (ι → F)) (β : ℝ) : ℝ :=
  -β⁻¹ * Real.log (codeZ C (Real.exp (-β)))

/-
The partition function is strictly positive at a positive Boltzmann weight:
every Boltzmann factor `y^{wt c}` is positive and the zero codeword contributes
`y^0 = 1 > 0`.
-/
theorem codeZ_pos (C : Submodule F (ι → F)) {y : ℝ} (hy : 0 < y) :
    0 < codeZ C y := by
  exact Finset.sum_pos ( fun _ _ => pow_pos hy _ ) ⟨ 0, Finset.mem_univ _ ⟩

/-
**The defining relation of the free energy, `Z = e^{-βF}`.**  For `β ≠ 0`,
`Z_C(e^{-β}) = exp(-β · F_C(β))`.
-/
theorem codeZ_eq_exp_neg_beta_freeEnergy (C : Submodule F (ι → F)) {β : ℝ}
    (hβ : β ≠ 0) :
    codeZ C (Real.exp (-β)) = Real.exp (-β * freeEnergy C β) := by
  rw [ freeEnergy, mul_comm ];
  rw [ show -β⁻¹ * Real.log ( codeZ C ( Real.exp ( -β ) ) ) * -β = Real.log ( codeZ C ( Real.exp ( -β ) ) ) by ring_nf; aesop ] ; rw [ Real.exp_log ( codeZ_pos _ ( Real.exp_pos _ ) ) ]

/-
**The dual-temperature relation for the free energy** (Kramers–Wannier
duality in logarithmic form).  At inverse temperature `β > 0`, writing
`y = e^{-β}` and the dual Boltzmann weight `y* = (1 - y)/(1 + (q-1)y)`,

`−β · F_{Cᗮ}(β) = n · log(1 + (q-1)y) − log|C| + log Z_C(y*)`.
-/
theorem freeEnergy_dualCode_relation (C : Submodule F (ι → F)) {β : ℝ}
    (hβ : 0 < β) :
    -β * freeEnergy (dualCode C) β
      = (Fintype.card ι : ℝ)
          * Real.log (1 + ((Fintype.card F : ℝ) - 1) * Real.exp (-β))
        - Real.log (Fintype.card C)
        + Real.log (codeZ C
            ((1 - Real.exp (-β)) / (1 + ((Fintype.card F : ℝ) - 1) * Real.exp (-β)))) := by
  convert congr_arg Real.log ( macwilliams_partition_dual_temp C ( Real.exp ( -β ) ) ( by nlinarith [ Real.exp_pos ( -β ), Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hβ ), show ( Fintype.card F : ℝ ) ≥ 2 by exact_mod_cast Fintype.one_lt_card ] ) ) using 1;
  · unfold freeEnergy; ring_nf; norm_num [ hβ.ne' ] ;
  · rw [ Real.log_mul, Real.log_div, Real.log_pow ] <;> norm_num;
    · exact fun h => absurd h <| ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| mul_nonneg ( sub_nonneg.2 <| Nat.one_le_cast.2 <| Fintype.card_pos ) <| Real.exp_nonneg _;
    · exact fun h => absurd h <| ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| mul_nonneg ( sub_nonneg.2 <| Nat.one_le_cast.2 <| Fintype.card_pos ) <| Real.exp_nonneg _;
    · refine' ne_of_gt ( codeZ_pos _ _ );
      exact div_pos ( by norm_num; positivity ) ( by nlinarith [ Real.exp_pos ( -β ), show ( Fintype.card F : ℝ ) ≥ 2 by exact_mod_cast Fintype.one_lt_card ] )

end CodingTheory