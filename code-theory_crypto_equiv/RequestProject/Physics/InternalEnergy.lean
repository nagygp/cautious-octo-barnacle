import RequestProject.Physics.PartitionFunction
import RequestProject.CodingTheory.PlessMoments

/-!
# Internal energy of the weight-enumerator spin system

This module continues the **physics** track of
`RequestProject/Physics/PartitionFunction.lean` and
`RequestProject/Physics/FreeEnergy.lean`.  In the statistical-mechanical reading
of a linear code, a codeword `c` is a configuration with energy `E(c) = wt(c)`
(its Hamming weight).  At **infinite temperature** (`β = 0`, all Boltzmann
weights equal) the configurations are uniformly distributed on `C`, and the
*internal energy* is the mean Hamming weight

  `⟨E⟩ = (1/|C|) Σ_{c ∈ C} wt(c) = (1/|C|) Σ_i i·A_i`.

The first Pless power moment (`pless_first_moment`) expresses this in terms of the
dual code: `q·⟨E⟩ = (q-1)n - B_1`, where `B_1 = weightDistribution Cᗮ 1` is the
number of weight-`1` dual codewords.  When the dual distance is at least `2`
(`B_1 = 0`) this recovers the "random" value `⟨E⟩ = (1 - 1/q)·n`.

## Main results

* `meanEnergy` — the infinite-temperature internal energy `⟨E⟩ = (Σ_i i A_i)/|C|`.
* `card_mul_meanEnergy` — `q·⟨E⟩ = (q-1)n - B_1` (the first Pless moment, read
  thermodynamically).
* `meanEnergy_of_dualDist` — if `B_1 = 0` then `q·⟨E⟩ = (q-1)n`, i.e.
  `⟨E⟩ = (1 - 1/q)·n`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The **internal energy** of a linear code `C` at infinite temperature: the
mean Hamming weight of a uniformly random codeword,
`⟨E⟩ = (Σ_i i·A_i)/|C|`. -/
noncomputable def meanEnergy (C : Submodule F (ι → F)) : ℝ :=
  (∑ i ∈ Finset.range (Fintype.card ι + 1), (i : ℝ) * (weightDistribution C i : ℝ))
    / (Fintype.card C : ℝ)

/-
**Internal energy via the first Pless power moment.**  `q·⟨E⟩ = (q-1)n - B_1`,
where `B_1 = weightDistribution Cᗮ 1`.  Requires `1 ≤ n`.
-/
theorem card_mul_meanEnergy (C : Submodule F (ι → F)) (hn : 1 ≤ Fintype.card ι) :
    (Fintype.card F : ℝ) * meanEnergy C
      = ((Fintype.card F : ℝ) - 1) * (Fintype.card ι : ℝ)
        - (weightDistribution (dualCode C) 1 : ℝ) := by
  unfold meanEnergy;
  field_simp;
  convert pless_first_moment C hn using 1;
  norm_cast

/-
**Random internal energy at large dual distance.**  If there are no weight-`1`
dual codewords (`B_1 = 0`) then `q·⟨E⟩ = (q-1)n`, i.e. `⟨E⟩ = (1 - 1/q)n`.
-/
theorem meanEnergy_of_dualDist (C : Submodule F (ι → F)) (hn : 1 ≤ Fintype.card ι)
    (hB : weightDistribution (dualCode C) 1 = 0) :
    (Fintype.card F : ℝ) * meanEnergy C
      = ((Fintype.card F : ℝ) - 1) * (Fintype.card ι : ℝ) := by
  rw [card_mul_meanEnergy C hn, hB]; simp

end CodingTheory