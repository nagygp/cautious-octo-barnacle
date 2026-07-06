import Mathlib
import RequestProject.DiffUniformity.FlystelWalshFourthMoment

/-!
# A lower bound on second-order collisions from the two moments

This module is the next step of the Flystel / AG track (`FLYSTEL_WALSH_ROADMAP.md`),
combining the **Parseval second moment** (`walsh_parseval`: `∑ ‖W‖² = q⁶`) with the
**fourth moment** (`walsh_fourth_moment`: `∑ ‖W‖⁴ = q⁴ · N`,
`N = #(secondOrderCollisions F)`) through the Cauchy–Schwarz inequality to obtain an
**unconditional lower bound** on the number of second-order collision quadruples.

Cauchy–Schwarz over the `q⁴` masks gives
`(∑ ‖W‖²)² ≤ (#masks) · (∑ ‖W‖⁴)`, i.e. `(q⁶)² ≤ q⁴ · (q⁴ · N)`, hence
`N ≥ q⁴`. This is the second-moment/fourth-moment analogue of the fact that a code
has at least the "trivial" number of second-order collisions, and it holds for
*every* `F : K × K → K × K`.

## Main results

* `secondOrderCollisions_card_ge` — `q⁴ ≤ #(secondOrderCollisions F)`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-
**Lower bound on second-order collisions.** For any `F : K × K → K × K` over a
finite field `K` (`q = #K`) and any nontrivial additive character `ψ`, the number
of second-order collision quadruples is at least `q⁴`. This is the Cauchy–Schwarz
consequence of the Parseval second moment `∑ ‖W‖² = q⁶` and the fourth moment
`∑ ‖W‖⁴ = q⁴ · N`.
-/
theorem secondOrderCollisions_card_ge (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) :
    (Fintype.card K : ℝ) ^ 4 ≤ (secondOrderCollisions F).card := by
  have := FlystelWalsh.walsh_parseval ψ hψ F;
  -- Apply the Cauchy-Schwarz inequality to the sum of the fourth powers of the Walsh transforms.
  have h_cauchy_schwarz : (∑ a : K × K, ∑ b : K × K, Complex.normSq (walsh ψ F a b)) ^ 2 ≤ (Fintype.card (K × K) : ℝ) ^ 2 * (∑ a : K × K, ∑ b : K × K, Complex.normSq (walsh ψ F a b) ^ 2) := by
    have h_cauchy_schwarz : ∀ (f : (K × K) × (K × K) → ℝ), (∑ p : (K × K) × (K × K), f p)^2 ≤ (Fintype.card ((K × K) × (K × K)) : ℝ) * (∑ p : (K × K) × (K × K), f p^2) := by
      intro f; have := Finset.univ.sum_le_sum fun x _ => pow_two_nonneg ( f x - ( ∑ y : ( K × K ) × K × K, f y ) / Fintype.card ( ( K × K ) × K × K ) ) ; simp_all +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ;
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      nlinarith [ mul_div_cancel₀ ( ∑ i, f i ) ( show ( Fintype.card K : ℝ ) * Fintype.card K * ( Fintype.card K * Fintype.card K ) ≠ 0 by norm_cast; aesop ) ];
    convert h_cauchy_schwarz ( fun p => Complex.normSq ( walsh ψ F p.1 p.2 ) ) using 1 <;> simp +decide [ ← Finset.sum_product' ];
    exact Or.inl ( by ring );
  simp_all +decide [ FlystelWalsh.walsh_fourth_moment ];
  nlinarith [ show 0 < ( Fintype.card K : ℝ ) ^ 8 by exact pow_pos ( Nat.cast_pos.mpr Fintype.card_pos ) _ ]

end FlystelWalsh
end APN