/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additive Character for F_{2^n}

Defines the canonical additive character `χ : F_{2^n} → ℤ` via the trace:
  `χ(x) = (-1)^{Tr(x)}`

## Main results
- `chi_add`: `χ(x + y) = χ(x) · χ(y)`
- `chi_orthogonality`: `∑_x χ(ax) = 0` for `a ≠ 0`
- `chi_sum`: `∑_a χ(ax) = 2^n` if `x = 0`, else `0`

## References
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 5
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §4.1
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

/-! ### The canonical additive character -/

/-- The canonical additive character `χ : F_{2^n} → ℤ`.
    `χ(x) = (-1)^{val(Tr(x))}` where `val : ZMod 2 → ℕ`. -/
def chi (n : ℕ) (x : F2n n) : ℤ :=
  (-1 : ℤ) ^ (tr2 n x).val

/-- `χ(0) = 1`. -/
@[simp]
theorem chi_zero (n : ℕ) : chi n (0 : F2n n) = 1 := by
  simp [chi]

/-- `χ(x)` is always `±1`. -/
theorem chi_val {n : ℕ} (x : F2n n) : chi n x = 1 ∨ chi n x = -1 := by
  unfold chi
  have hv : (tr2 n x).val < 2 := ZMod.val_lt _
  have : (tr2 n x).val = 0 ∨ (tr2 n x).val = 1 := by omega
  rcases this with h | h <;> simp [h]

/-- `|χ(x)| = 1`. -/
theorem chi_abs {n : ℕ} (x : F2n n) : |chi n x| = 1 := by
  rcases chi_val x with h | h <;> simp [h]

/-- `χ(x)^2 = 1`. -/
theorem chi_sq {n : ℕ} (x : F2n n) : chi n x ^ 2 = 1 := by
  rcases chi_val x with h | h <;> simp [h]

/-- `χ(x + y) = χ(x) · χ(y)` — the character property. -/
theorem chi_add {n : ℕ} (x y : F2n n) : chi n (x + y) = chi n x * chi n y := by
  unfold chi
  rw [map_add]
  have h2 : ∀ a b : ZMod 2, (-1 : ℤ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
    decide
  exact h2 _ _

/-- `χ(x) = 1` iff `Tr(x) = 0`. -/
theorem chi_eq_one_iff {n : ℕ} (x : F2n n) : chi n x = 1 ↔ tr2 n x = 0 := by
  unfold chi
  constructor
  · intro h
    have hv : (tr2 n x).val < 2 := ZMod.val_lt _
    have hv01 : (tr2 n x).val = 0 ∨ (tr2 n x).val = 1 := by omega
    rcases hv01 with hv0 | hv1
    · rwa [ZMod.val_eq_zero] at hv0
    · exfalso; simp [hv1] at h
  · intro h; rw [h]; simp

/-- `χ(x) = -1` iff `Tr(x) = 1`. -/
theorem chi_eq_neg_one_iff {n : ℕ} (x : F2n n) : chi n x = -1 ↔ tr2 n x = 1 := by
  unfold chi
  constructor
  · intro h
    have hv : (tr2 n x).val < 2 := ZMod.val_lt _
    have hv01 : (tr2 n x).val = 0 ∨ (tr2 n x).val = 1 := by omega
    rcases hv01 with hv0 | hv1
    · exfalso; simp [hv0] at h
    · exact ZMod.val_injective 2 (by rw [hv1]; decide)
  · intro h; rw [h]; decide

/-! ### Orthogonality -/

/-
Character orthogonality: `∑_x χ(a·x) = 0` when `a ≠ 0`.
-/
theorem chi_orthogonality {n : ℕ} (hn : n ≠ 0) (a : F2n n) (ha : a ≠ 0) :
    ∑ x : F2n n, chi n (a * x) = 0 := by
  have h_reindex : ∑ x : F2n n, chi n (a * x) = ∑ y : F2n n, chi n y := by
    have h_bij : Function.Bijective (fun x : F2n n => a * x) := by
      exact ⟨ mul_right_injective₀ ha, mul_left_surjective₀ ha ⟩;
    exact?;
  -- Split the sum into two parts: one over elements with trace 0 and one over elements with trace 1.
  have h_split : ∑ y : F2n n, chi n y = ∑ y ∈ Finset.univ.filter (fun y => tr2 n y = 0), 1 + ∑ y ∈ Finset.univ.filter (fun y => tr2 n y = 1), (-1 : ℤ) := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; rcases h : tr2 n x with ( _ | _ | k ) <;> simp_all +decide [ chi ] ;
    contradiction;
  have := tr2_kernel_card hn; have := tr2_fiber_one_card hn; aesop;

/-- Character sum: `∑_a χ(a·x) = 2^n` if `x = 0`, else `0`. -/
theorem chi_sum {n : ℕ} (hn : n ≠ 0) (x : F2n n) :
    ∑ a : F2n n, chi n (a * x) = if x = 0 then (2 ^ n : ℤ) else 0 := by
  split_ifs with h
  · subst h; simp [chi_zero, F2n.card n hn]
  · have : ∑ a : F2n n, chi n (a * x) = ∑ a : F2n n, chi n (x * a) := by
      congr 1; ext a; ring_nf
    rw [this]
    exact chi_orthogonality hn x h

end
end Kasami