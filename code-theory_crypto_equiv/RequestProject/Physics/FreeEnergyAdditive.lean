import Mathlib
import RequestProject.CodingTheory.DirectSum
import RequestProject.Physics.FreeEnergy

/-!
# Physics track: extensivity of the free energy under direct sums

In the statistical-mechanics reading of a linear code (see
`RequestProject/Physics/PartitionFunction.lean` and
`RequestProject/Physics/FreeEnergy.lean`), a code `C` is a spin system whose
configurations are the codewords, with energy equal to the Hamming weight and
partition function `Z_C(y) = Σ_{c ∈ C} y^{wt c}` at Boltzmann weight
`y = e^{-β}`.

The **direct sum** `C₁ ⊕ C₂` (`RequestProject/CodingTheory/DirectSum.lean`) is
the composite of two *independent* subsystems: a codeword is an independent
choice of a codeword in each factor, and its energy is the sum of the two
energies (`hammingNorm_sum`).  Independence of subsystems is exactly what makes a
partition function *multiply* and a free energy *add*:

* `codeZ_directSumCode` — the partition function factorizes,
  `Z_{C₁ ⊕ C₂}(y) = Z_{C₁}(y) · Z_{C₂}(y)`;
* `freeEnergy_directSumCode` — the free energy is **extensive/additive**,
  `F_{C₁ ⊕ C₂}(β) = F_{C₁}(β) + F_{C₂}(β)` (at every inverse temperature `β`).

This is the coding-theoretic incarnation of the elementary but foundational
statistical-mechanics fact that the free energy of a system of independent
subsystems is the sum of their free energies.

## Main results

* `codeZ_directSumCode` — multiplicativity of the partition function.
* `freeEnergy_directSumCode` — additivity of the free energy.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {F : Type*} [Field F] [Fintype F]

/-
**Multiplicativity of the partition function under direct sums.**
`Z_{C₁ ⊕ C₂}(y) = Z_{C₁}(y) · Z_{C₂}(y)`.
-/
theorem codeZ_directSumCode (C₁ : Submodule F (ι → F)) (C₂ : Submodule F (κ → F))
    (y : ℝ) :
    codeZ (directSumCode C₁ C₂) y = codeZ C₁ y * codeZ C₂ y := by
  -- We'll use the fact that summing over a product type is the product of the sums.
  have h_prod : ∑ c : ↥(directSumCode C₁ C₂), y ^ (hammingNorm (c : (ι ⊕ κ) → F)) = ∑ c₁ : ↥C₁ × ↥C₂, y ^ (hammingNorm (c₁.1 : ι → F) + hammingNorm (c₁.2 : κ → F)) := by
    refine' Finset.sum_bij ( fun c _ => ( ⟨ c.val ∘ Sum.inl, by
      exact ( mem_directSumCode _ |>.1 c.2 ).1 ⟩, ⟨ c.val ∘ Sum.inr, by
      exact ( mem_directSumCode _ |>.1 c.2 ).2 ⟩ ) ) _ _ _ _ <;> simp +decide [ hammingNorm_sum ];
    · intro a ha b hb hab hba; ext x; cases x <;> simp_all +decide [ funext_iff ] ;
    · intro a ha b hb
      use Sum.elim a b
      simp [directSumCode];
      aesop;
  simp_all +decide [ pow_add, Fintype.sum_prod_type ];
  simp_all +decide only [codeZ];
  simp +decide only [sum_mul_sum]

/-
**Extensivity (additivity) of the free energy under direct sums.**
`F_{C₁ ⊕ C₂}(β) = F_{C₁}(β) + F_{C₂}(β)` at every inverse temperature `β`
(the `β⁻¹` prefactor makes the identity hold at `β = 0` as well). -/
theorem freeEnergy_directSumCode (C₁ : Submodule F (ι → F)) (C₂ : Submodule F (κ → F))
    (β : ℝ) :
    freeEnergy (directSumCode C₁ C₂) β = freeEnergy C₁ β + freeEnergy C₂ β := by
  unfold freeEnergy;
  rw [ ← mul_add, codeZ_directSumCode, Real.log_mul ( ne_of_gt ( codeZ_pos _ ( Real.exp_pos _ ) ) ) ( ne_of_gt ( codeZ_pos _ ( Real.exp_pos _ ) ) ) ]

end CodingTheory