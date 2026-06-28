import Mathlib

/-!
# Prime-field linear / correlation analysis

The binary Walsh transform uses `±1` characters; over `ZMod p` the right object is
the **additive character** `ZMod p → ℂ` valued in roots of unity.  Linear
cryptanalysis of a prime-field S-box `f` is governed by the *correlation sums*

  `charSum f χ ψ = ∑ x, χ (f x) · ψ x`,

the prime-field analog of the Walsh coefficient, where `χ` is an *output* mask
character and `ψ` an *input* mask character.

This module sets up that machinery on `ZMod p` and proves the foundational facts:
character orthogonality kills the trivial coefficients, and every correlation sum
obeys the trivial `≤ p` bound.

## Main results

* `charSum_trivial_output` — with the trivial output mask (`χ = 1`) and a
  nontrivial input mask (`ψ ≠ 1`), the correlation sum vanishes.
* `charSum_trivial_input_of_bijective` — for a permutation `f`, with the trivial
  input mask (`ψ = 1`) and a nontrivial output mask (`χ ≠ 1`), it vanishes.
* `charSum_self` — the full-mask trivial coefficient `charSum f 1 1 = p`.
* `norm_charSum_le` — `‖charSum f χ ψ‖ ≤ p` for all masks (each summand is a unit
  modulus root of unity).
-/

open Finset BigOperators

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The prime-field correlation (Walsh-type) sum of an S-box `f` against an output
mask character `χ` and an input mask character `ψ`. -/
noncomputable def charSum (f : ZMod p → ZMod p)
    (χ ψ : AddChar (ZMod p) ℂ) : ℂ :=
  ∑ x : ZMod p, χ (f x) * ψ x

/-
With the trivial output mask and a nontrivial input mask, the correlation sum
vanishes (additive-character orthogonality).
-/
theorem charSum_trivial_output (f : ZMod p → ZMod p)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    charSum f 1 ψ = 0 := by
  unfold charSum
  simp only [AddChar.one_apply, one_mul]
  exact AddChar.sum_eq_zero_of_ne_one hψ

/-
For a permutation `f`, with the trivial input mask and a nontrivial output
mask, the correlation sum vanishes.
-/
theorem charSum_trivial_input_of_bijective (f : ZMod p → ZMod p)
    (hf : Function.Bijective f) (χ : AddChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    charSum f χ 1 = 0 := by
  -- Since $f$ is bijective, we can reindex the sum to be over the entire field.
  have h_reindex : ∑ x : ZMod p, χ (f x) = ∑ y : ZMod p, χ y := by
    exact Equiv.sum_comp ( Equiv.ofBijective f hf ) _;
  convert AddChar.sum_eq_zero_of_ne_one hχ using 1;
  unfold charSum; aesop;

/-
The full trivial coefficient counts the field: `charSum f 1 1 = p`.
-/
theorem charSum_self (f : ZMod p → ZMod p) :
    charSum f 1 1 = (p : ℂ) := by
  unfold charSum
  simp +decide [ AddChar.one_apply ]

/-
Every correlation sum is bounded in modulus by the field size `p`.
-/
theorem norm_charSum_le (f : ZMod p → ZMod p) (χ ψ : AddChar (ZMod p) ℂ) :
    ‖charSum f χ ψ‖ ≤ (p : ℝ) := by
  refine' le_trans ( norm_sum_le _ _ ) _;
  simp +decide [ AddChar.norm_apply ]

end PrimeFieldAudit