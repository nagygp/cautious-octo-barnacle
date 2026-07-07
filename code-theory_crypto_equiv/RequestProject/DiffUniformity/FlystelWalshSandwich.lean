import Mathlib
import RequestProject.DiffUniformity.FlystelWalshLinearPotential
import RequestProject.DiffUniformity.FlystelTheorem33
import RequestProject.DiffUniformity.FlystelWalshPoseidon
import RequestProject.DiffUniformity.FlystelWalshAnemoi

/-!
# Sandwiching the maximal Walsh coefficient of concrete ZK S-boxes (ZK track)

This module instantiates the two complementary Walsh-spectrum bounds on the
concrete arithmetisation-oriented S-boxes formalised in `FlystelWalshAnemoi.lean`
(the Anemoi `x³` Flystel over `F₁₁`) and `FlystelWalshPoseidon.lean` (the
Poseidon `x⁵` Flystel over `F₁₃`):

* the **unconditional Parseval lower bound** `exists_walsh_sq_ge`
  (`FlystelWalshLinearPotential.lean`): some nonzero mask `(a, b)` carries squared
  Walsh mass at least `q⁴ / (q² + 1)`;
* the **conditional Theorem 3.3 upper bound** `closedFlystel_walsh_norm_le`
  (`FlystelTheorem33.lean`): every nonzero-mask coefficient has modulus at most
  `(d − 1)·p`.

Together they **sandwich** the largest absolute Walsh coefficient (the linear
potential governing linear cryptanalysis) of each S-box:

```
q⁴ / (q² + 1)  ≤  ‖W_V(ψ, a, b)‖²        and        ‖W_V(ψ, a, b)‖ ≤ (d − 1)·p
```

for a single witnessing nonzero mask `(a, b)`.

## Main results

* `walsh_V_anemoi_sandwich` — Anemoi `x³` over `F₁₁`: `14641/122 ≤ ‖W_V‖²` and
  `‖W_V‖ ≤ (d−1)·p = 22` for a common nonzero mask.
* `walsh_V5_poseidon_sandwich` — Poseidon `x⁵` over `F₁₃`: `28561/170 ≤ ‖W_V‖²`
  and `‖W_V‖ ≤ (d−1)·p = 52` for a common nonzero mask.
-/

open Finset

namespace APN
namespace FlystelWalsh

/-! ### Anemoi `x³` over `F₁₁` -/

namespace Anemoi

/-- **Conditional Theorem 3.3 bound for the Anemoi closed Flystel.** Given the
Rojas-León character-sum input on the deep entries, every nonzero-mask Walsh
coefficient obeys `‖W_V(ψ, a, b)‖ ≤ (d−1)·p = 2·11 = 22`. -/
theorem walsh_V_norm_le (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hdeep : ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      CharSumBounds.RojasLeonBoundTwo ψ (walshFun V a b) 3)
    (a b : ZMod p × ZMod p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖walsh ψ V a b‖ ≤ (22 : ℝ) := by
  have h := closedFlystel_walsh_norm_le (K := ZMod p) ψ hψ E Qγ Qδ E_bijective 3
    (by norm_num) hdeep a b hab
  have hcard : (Fintype.card (ZMod p) : ℝ) = 11 := by
    rw [ZMod.card]; norm_num [p]
  rw [hcard] at h
  norm_num at h
  exact h

/-- **Walsh sandwich for the Anemoi `x³` Flystel over `F₁₁`.** The Parseval lower
bound and the conditional Theorem 3.3 upper bound trap the largest Walsh
coefficient: some nonzero mask `(a, b)` satisfies both
`14641/122 ≤ ‖W_V(ψ, a, b)‖²` and `‖W_V(ψ, a, b)‖ ≤ 22`. -/
theorem walsh_V_anemoi_sandwich (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hdeep : ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      CharSumBounds.RojasLeonBoundTwo ψ (walshFun V a b) 3) :
    ∃ a b : ZMod p × ZMod p, (a, b) ≠ (0, 0) ∧
      (14641 : ℝ) / 122 ≤ Complex.normSq (walsh ψ V a b) ∧
      ‖walsh ψ V a b‖ ≤ (22 : ℝ) := by
  have hc : 2 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; norm_num [p]
  obtain ⟨a, b, hab0, hlow⟩ := exists_walsh_sq_ge ψ hψ V hc
  have hcard : (Fintype.card (ZMod p) : ℝ) = 11 := by rw [ZMod.card]; norm_num [p]
  rw [hcard] at hlow
  norm_num at hlow
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inr (by rintro rfl; exact hab0 (by rw [ha]))
    · exact Or.inl ha
  exact ⟨a, b, hab0, by rw [div_le_iff₀ (by norm_num)]; linarith,
    walsh_V_norm_le ψ hψ hdeep a b hne⟩

end Anemoi

/-! ### Poseidon `x⁵` over `F₁₃` -/

namespace Poseidon

/-- **Walsh sandwich for the Poseidon `x⁵` Flystel over `F₁₃`.** The Parseval
lower bound and the conditional Theorem 3.3 upper bound trap the largest Walsh
coefficient: some nonzero mask `(a, b)` satisfies both
`28561/170 ≤ ‖W_V(ψ, a, b)‖²` and `‖W_V(ψ, a, b)‖ ≤ 52`. -/
theorem walsh_V5_poseidon_sandwich (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (hdeep : ∀ a b : ZMod p × ZMod p, DeepEntry a b →
      CharSumBounds.RojasLeonBoundTwo ψ (walshFun V5 a b) 5) :
    ∃ a b : ZMod p × ZMod p, (a, b) ≠ (0, 0) ∧
      (28561 : ℝ) / 170 ≤ Complex.normSq (walsh ψ V5 a b) ∧
      ‖walsh ψ V5 a b‖ ≤ (52 : ℝ) := by
  have hc : 2 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; norm_num [p]
  obtain ⟨a, b, hab0, hlow⟩ := exists_walsh_sq_ge ψ hψ V5 hc
  have hcard : (Fintype.card (ZMod p) : ℝ) = 13 := by rw [ZMod.card]; norm_num [p]
  rw [hcard] at hlow
  norm_num at hlow
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inr (by rintro rfl; exact hab0 (by rw [ha]))
    · exact Or.inl ha
  exact ⟨a, b, hab0, by rw [div_le_iff₀ (by norm_num)]; linarith,
    walsh_V5_norm_le ψ hψ hdeep a b hne⟩

end Poseidon

end FlystelWalsh
end APN