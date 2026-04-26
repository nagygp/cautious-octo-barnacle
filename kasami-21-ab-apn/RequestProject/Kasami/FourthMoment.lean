/-
# Fourth Moment Identity and Power Function AB Extension

This module provides:
- Extension of single-component AB to full AB for power functions
- Helper lemmas for the AB→APN proof

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.2
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Scaling for power functions -/

/-- For a power function x ↦ x^d with bijective power map, the extended WHT at (a,b)
    for b ≠ 0 equals the standard WHT at a shifted argument. -/
theorem wht2_power_scaling {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d))
    (a b : F2n n) (hb : b ≠ 0) :
    ∃ c : F2n n, c ≠ 0 ∧ c ^ d = b ∧
      wht2 (fun x => x ^ d) a b = wht (fun x => x ^ d) (a * c⁻¹) := by
  obtain ⟨c, hc⟩ : ∃ c : F2n n, c^d = b := hbij.surjective b
  use c
  unfold wht2 wht
  by_cases hc0 : c = 0 <;> simp_all +decide [mul_assoc, mul_left_comm]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft₀ c⁻¹ (inv_ne_zero hc0))]
  simp +decide [← mul_assoc, ← hc, mul_pow, hc0]

/-- For power functions, single-component AB implies full AB on all components. -/
theorem power_ab_all_components {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d))
    (hab : ∀ a : F2n n, wht (fun x : F2n n => x ^ d) a ^ 2 = 0 ∨
      wht (fun x : F2n n => x ^ d) a ^ 2 = (2 ^ (n + 1) : ℤ)) :
    IsAlmostBent (fun x : F2n n => x ^ d) := by
  intro a b hb
  obtain ⟨c, _, _, heq⟩ := wht2_power_scaling hn d hd hbij a b hb
  rw [heq]
  exact hab (a * c⁻¹)

end
end Kasami
