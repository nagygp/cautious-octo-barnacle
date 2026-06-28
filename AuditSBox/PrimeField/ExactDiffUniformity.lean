import Mathlib
import AuditSBox.PrimeFieldDiffUnif
import AuditSBox.PrimeField.AbstractBridge
import RequestProject.DiffUniformity.DifferentialUniformityUpstream

/-!
# Exact differential uniformity of prime-field power maps (Nyberg-style)

The module `AuditSBox.PrimeField.AbstractBridge` records the *upper* bounds
`APN.differentialUniformity (powerMap d) ≤ d - 1` for the arithmetization-friendly
power maps (`poseidon_diffUnif_le_four`, `cube_diffUnif_le_two`, …).  For the
sharpest security statements one wants the *exact* value `δ`, not just a bound
(MacWilliams/Nyberg-style "differentially `δ`-uniform").

This file supplies the matching **lower** bound for power maps with an *odd*
exponent, and combines it with the existing `≤ 2` bound to prove the headline
exact result: the cube map `x ↦ x^3` is **APN** over `ZMod p` for `p > 3`
(`APN.differentialUniformity (powerMap 3) = 2`, i.e. `APN.IsAPN (powerMap 3)`).

## Lower-bound mechanism

For any odd `d` and any `a ≠ 0`, both `x = 0` and `x = -a` are solutions of
`(x + a)^d - x^d = a^d`: at `x = 0` the left side is `a^d`, and at `x = -a` it is
`0^d - (-a)^d = -(-a)^d = a^d` because `d` is odd.  Since `0 ≠ -a`, that fibre has
at least two elements, so the differential uniformity is at least `2`.

## Main results

* `two_le_powerMap_diffUnif` — for odd `d`, `2 ≤ APN.differentialUniformity (powerMap d)`.
* `cube_diffUnif_eq_two` — `APN.differentialUniformity (powerMap 3) = 2` for `p > 3`.
* `cube_isAPN` — the cube map is APN over `ZMod p` for `p > 3`.
-/

open scoped Classical

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-
For an *odd* exponent `d`, the power map `x ↦ x^d` over `ZMod p` has
differential uniformity at least `2`: the fibre of `a^d` under the direction-`1`
derivative contains both `0` and `-1`.
-/
theorem two_le_powerMap_diffUnif (d : ℕ) (hd : Odd d) :
    2 ≤ APN.differentialUniformity (powerMap (p := p) d) := by
  obtain ⟨ k, hk ⟩ := hd;
  refine' le_trans _ ( APN.diffUnif_le_iff _ _ |>.1 le_rfl 1 ( one_ne_zero' _ ) 1 );
  refine' le_trans _ ( Set.ncard_le_ncard <| show { 0, -1 } ⊆ { x : ZMod p | ( x + 1 ) ^ d - x ^ d = 1 } from _ );
  · rw [ Set.ncard_pair ] ; norm_num;
  · norm_num [ Set.insert_subset_iff, hk ]

/-- **Exact differential uniformity of the cube map.** Over `ZMod p` with `p > 3`,
the S-box `x ↦ x^3` is differentially `2`-uniform: `δ = 2`. -/
theorem cube_diffUnif_eq_two (hp3 : 3 < p) :
    APN.differentialUniformity (powerMap (p := p) 3) = 2 :=
  le_antisymm (cube_diffUnif_le_two hp3) (two_le_powerMap_diffUnif 3 (by decide))

/-- The cube map `x ↦ x^3` is **APN** over `ZMod p` for `p > 3`. -/
theorem cube_isAPN (hp3 : 3 < p) : APN.IsAPN (powerMap (p := p) 3) :=
  cube_diffUnif_eq_two hp3

end PrimeFieldAudit