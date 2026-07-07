import Mathlib
import RequestProject.CodingTheory.MacWilliams
import RequestProject.CodingTheory.WeightEnumerator

/-!
# A statistical-mechanics reading of the weight enumerator

This is the **physics** companion module (`FUTURE_DIRECTIONS_FOUNDATIONS.md`
"variety" track): the most directly *equivalent / supportive* piece of physics to
the coding-theory spine already in the repository, because the weight enumerator
of a linear code **is** the partition function of a statistical-mechanical system,
and the **MacWilliams identity** (`CodingTheory.MacWilliams.macwilliams`) **is** a
high–low temperature (Kramers–Wannier-type) **duality**.

Model `n = #ι` non-interacting "spins", one per coordinate, where a codeword `c`
is a configuration with energy `E(c) = wt(c)` (its Hamming weight) and Boltzmann
weight `y^{wt c}` with `y = e^{-β}` (inverse temperature `β`).  The **partition
function** restricted to the code `C` is

  `Z_C(y) = Σ_{c ∈ C} y^{wt c} = Σ_{i} A_i y^i`,

where `A_i` is the weight distribution.  The MacWilliams identity then expresses
the partition function of the **dual** code `Cᗮ` in terms of `Z_C` evaluated at a
**dual temperature** `y* = (1 - y) / (1 + (q-1)y)` — exactly the Kramers–Wannier
structure relating a model to its dual at the conjugate temperature.

## Main results

* `codeZ_eq_sum_weightDistribution` — `Z_C(y) = Σ_i A_i y^i` (partition function
  as the weight-distribution generating function).
* `codeZ_boltzmann` — `Z_C(e^{-β}) = Σ_{c∈C} e^{-β·wt c}` (the Boltzmann form).
* `macwilliams_partition` — the MacWilliams identity for partition functions:
  `|C| · Z_{Cᗮ}(y) = Σ_{u∈C} (1+(q-1)y)^{n-wt u} (1-y)^{wt u}`.
* `macwilliams_partition_dual_temp` — the **Kramers–Wannier duality**:
  `Z_{Cᗮ}(y) = (1+(q-1)y)^n / |C| · Z_C(y*)` with `y* = (1-y)/(1+(q-1)y)`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The **partition function** of a linear code `C` at Boltzmann weight `y`
(`y = e^{-β}` for inverse temperature `β`): `Z_C(y) = Σ_{c ∈ C} y^{wt c}`, summing
the Boltzmann factor over codeword configurations with energy = Hamming weight. -/
noncomputable def codeZ (C : Submodule F (ι → F)) (y : ℝ) : ℝ :=
  ∑ c : C, y ^ (hammingNorm (c : ι → F))

/-
The partition function is the generating function of the weight distribution:
`Z_C(y) = Σ_{i=0}^{n} A_i y^i`.
-/
theorem codeZ_eq_sum_weightDistribution (C : Submodule F (ι → F)) (y : ℝ) :
    codeZ C y = ∑ i ∈ Finset.range (Fintype.card ι + 1),
      (weightDistribution C i : ℝ) * y ^ i := by
  unfold codeZ weightDistribution;
  -- By reorganizing the summation over codewords `c` by group ("fiber") according to `i=wt(c)`,
  -- each weight class contributes `A_i * y^i`. The sum over `i` should range over all possible weights,
  -- restricted by `hammingNorm(c) ≤ Fintype.card ι` (so `i ∈ range (n+1)` for `n=Fintype.card ι`).
  have hfib : ∑ c : C, y ^ (hammingNorm (c : ι → F)) = ∑ i ∈ Finset.range (Fintype.card ι + 1), (∑ c ∈ Finset.univ.filter (fun c : C => hammingNorm (c : ι → F) = i), y ^ i) := by
    simp +decide only [sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    simp +decide [ hammingNorm ];
    exact fun a ha h => False.elim <| h.not_ge <| le_trans ( Finset.card_le_univ _ ) <| by simp +decide ;
  simp_all +decide [ mul_comm, Fintype.card_subtype ]

/-- The Boltzmann form: with `y = e^{-β}`, `Z_C(e^{-β}) = Σ_{c∈C} e^{-β·wt c}`. -/
theorem codeZ_boltzmann (C : Submodule F (ι → F)) (β : ℝ) :
    codeZ C (Real.exp (-β)) = ∑ c : C, Real.exp (-β * (hammingNorm (c : ι → F) : ℝ)) := by
  unfold codeZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Real.exp_nat_mul]
  ring_nf

/-
**MacWilliams identity for partition functions.**  Clearing the `1/|C|`
denominator in the MacWilliams identity (evaluated at `X = 1`, `Y = y`) gives
`|C| · Z_{Cᗮ}(y) = Σ_{u∈C} (1+(q-1)y)^{n-wt u} (1-y)^{wt u}`.
-/
theorem macwilliams_partition (C : Submodule F (ι → F)) (y : ℝ) :
    (Fintype.card C : ℝ) * codeZ (dualCode C) y
      = ∑ u : C,
          (1 + ((Fintype.card F : ℝ) - 1) * y) ^ (Fintype.card ι - hammingNorm (u : ι → F))
            * (1 - y) ^ hammingNorm (u : ι → F) := by
  convert congr_arg ( fun x : ℂ => x * ( Fintype.card C : ℂ ) ) ( MacWilliams.macwilliams C 1 y ) using 1 ; norm_num [ codeZ ] ; ring!;
  rw [ inv_mul_eq_div, eq_div_iff ] <;> norm_cast ; norm_num [ mul_comm ];
  exact Fintype.card_ne_zero

/-
**Kramers–Wannier duality for codes.**  The partition function of the dual
code is, up to the factor `(1+(q-1)y)^n / |C|`, the partition function of `C`
evaluated at the **dual temperature** `y* = (1-y)/(1+(q-1)y)`.
-/
theorem macwilliams_partition_dual_temp (C : Submodule F (ι → F)) (y : ℝ)
    (hA : 1 + ((Fintype.card F : ℝ) - 1) * y ≠ 0) :
    codeZ (dualCode C) y
      = (1 + ((Fintype.card F : ℝ) - 1) * y) ^ (Fintype.card ι)
          / (Fintype.card C : ℝ)
          * codeZ C ((1 - y) / (1 + ((Fintype.card F : ℝ) - 1) * y)) := by
  convert congr_arg ( fun x : ℝ => x / ( Fintype.card C : ℝ ) ) ( macwilliams_partition C y ) using 1;
  · rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr <| Fintype.card_ne_zero ) ];
  · -- Let's simplify the expression using the properties of exponents and multiplication.
    have h_simp : ∀ u : C, (1 + ((Fintype.card F : ℝ) - 1) * y) ^ (Fintype.card ι - hammingNorm (u : ι → F)) * (1 - y) ^ hammingNorm (u : ι → F) =
                  ((1 + ((Fintype.card F : ℝ) - 1) * y) ^ Fintype.card ι) *
                  ((1 - y) / (1 + ((Fintype.card F : ℝ) - 1) * y)) ^ hammingNorm (u : ι → F) := by
                    intro u; rw [ div_pow ] ; rw [ mul_div ] ; rw [ eq_div_iff ( pow_ne_zero _ hA ) ] ; ring;
                    rw [ ← pow_add, Nat.sub_add_cancel ];
                    exact Finset.card_le_univ _;
    simp +decide only [codeZ, h_simp];
    rw [ ← Finset.mul_sum _ _ _, div_mul_eq_mul_div ]

end CodingTheory