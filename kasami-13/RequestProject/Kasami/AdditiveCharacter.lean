/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical Additive Character of F_{2^n}

Constructs the canonical additive character `χ : F_{2^n} → ℤ` defined by
`χ(x) = (-1)^{Tr(x)}`, where `Tr` is the absolute trace to F₂.

## Main definitions
- `chi n : F2n n → ℤ` — the canonical additive character

## Main results
- `chi_values`: `χ(x) ∈ {-1, 1}`
- `chi_sq`: `χ(x)^2 = 1`
- `chi_add`: `χ(x+y) = χ(x) * χ(y)`
- `chi_orthogonality`: `∑_x χ(a*x) = 0` for `a ≠ 0`

## References
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 5
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §2.3
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### Definition of the canonical character -/

/-- The canonical additive character `χ(x) = (-1)^{val(Tr(x))}`.
    Takes values in `{-1, 1} ⊂ ℤ`. -/
noncomputable def chi (n : ℕ) (x : F2n n) : ℤ :=
  (-1 : ℤ) ^ (ZMod.val (tr2 n x))

/-! ### Basic properties -/

theorem chi_zero (n : ℕ) : chi n (0 : F2n n) = 1 := by
  simp [chi, tr2_zero]

theorem chi_values {n : ℕ} (x : F2n n) : chi n x = 1 ∨ chi n x = -1 := by
  unfold chi
  have hv := ZMod.val_lt (tr2 n x)
  interval_cases (tr2 n x).val <;> simp

theorem chi_sq {n : ℕ} (x : F2n n) : chi n x ^ 2 = 1 := by
  rcases chi_values x with h | h <;> simp [h]

theorem chi_ne_zero {n : ℕ} (x : F2n n) : chi n x ≠ 0 := by
  rcases chi_values x with h | h <;> simp [h]

theorem chi_abs {n : ℕ} (x : F2n n) : |chi n x| = 1 := by
  rcases chi_values x with h | h <;> simp [h]

private theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℤ) ^ (ZMod.val (a + b)) = (-1 : ℤ) ^ (ZMod.val a) * (-1 : ℤ) ^ (ZMod.val b) := by
  revert a b; decide

/-- The character is multiplicative: `χ(x+y) = χ(x) · χ(y)`. -/
theorem chi_add {n : ℕ} (x y : F2n n) : chi n (x + y) = chi n x * chi n y := by
  unfold chi
  rw [tr2_add]
  exact neg_one_pow_val_add (tr2 n x) (tr2 n y)

/-- `χ(-x) = χ(x)` in characteristic 2. -/
theorem chi_neg {n : ℕ} (x : F2n n) : chi n (-x) = chi n x := by
  rw [F2n.neg_eq]

/-! ### Orthogonality -/

/-- When `a = 0`, the character sum equals `2^n`. -/
theorem chi_sum_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ x : F2n n, chi n (0 * x) = (2 ^ n : ℤ) := by
  simp only [zero_mul, chi_zero]
  rw [Finset.sum_const, Finset.card_univ, F2n.card n hn]
  simp

/-
Character orthogonality: `∑_x χ(a·x) = 0` for `a ≠ 0`.
-/
theorem chi_orthogonality {n : ℕ} (hn : n ≠ 0) (a : F2n n) (ha : a ≠ 0) :
    ∑ x : F2n n, chi n (a * x) = 0 := by
  -- Since $a \neq 0$, multiplication by $a$ is a bijection on $F_{2^n}$. So $\sum_{x \in F_{2^n}} \chi(a \cdot x) = \sum_{x \in F_{2^n}} \chi(x)$.
  have h_bij : ∑ x : F2n n, chi n (a * x) = ∑ x : F2n n, chi n x := by
    apply Finset.sum_bij (fun x _ => a * x);
    · grind;
    · aesop;
    · exact fun b _ => ⟨ a⁻¹ * b, Finset.mem_univ _, by rw [ mul_inv_cancel_left₀ ha ] ⟩;
    · exact fun _ _ => rfl;
  -- Since `tr2 n x` is either 0 or 1, we can split the sum into two parts: one where `tr2 n x = 0` and one where `tr2 n x = 1`.
  have h_split : (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n x))) = (∑ x ∈ Finset.univ.filter (fun x => tr2 n x = 0), 1) - (∑ x ∈ Finset.univ.filter (fun x => tr2 n x = 1), 1) := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    rw [ ← Finset.sum_sub_distrib ] ; congr ; ext x ; rcases h : tr2 n x with ( _ | _ | m ) <;> simp_all +decide [ ZMod ] ;
    grind +qlia;
  simp_all +decide [ chi ];
  rw [ tr2_kernel_card hn, tr2_fiber_one_card hn ] ; norm_num

/-- The full orthogonality relation combining both cases. -/
theorem chi_sum {n : ℕ} (hn : n ≠ 0) (a : F2n n) :
    ∑ x : F2n n, chi n (a * x) = if a = 0 then (2 ^ n : ℤ) else 0 := by
  split
  · next h => subst h; exact chi_sum_zero hn
  · next h => exact chi_orthogonality hn a h

/-- Sum of `χ(x)` over all `x` is `0` (since `Tr` is balanced, for `n ≥ 1`). -/
theorem chi_sum_all_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ x : F2n n, chi n x = 0 := by
  have := chi_orthogonality hn 1 one_ne_zero
  simpa using this

/-
Character inner product: `∑_x χ(ax)χ(bx) = 2^n · [a = b]`.
-/
theorem chi_inner_product {n : ℕ} (hn : n ≠ 0) (a b : F2n n) :
    ∑ x : F2n n, chi n (a * x) * chi n (b * x) =
    if a = b then (2 ^ n : ℤ) else 0 := by
  split_ifs with h;
  · simp +decide [ ← sq, chi_sq, h ];
    exact mod_cast F2n.card n hn;
  · convert chi_orthogonality hn ( a + b ) ( add_eq_zero_iff_eq_neg.not.mpr <| by aesop ) using 1;
    simp +decide only [← chi_add, add_mul]

/-- `χ(x) = 1` iff `Tr(x) = 0`. -/
theorem chi_eq_one_iff {n : ℕ} (x : F2n n) : chi n x = 1 ↔ tr2 n x = 0 := by
  unfold chi
  constructor
  · intro h
    by_contra h'
    have hv := ZMod.val_lt (tr2 n x)
    have hne : tr2 n x ≠ 0 := h'
    have : (tr2 n x).val = 1 := by
      have := ZMod.val_lt (tr2 n x) (n := 2)
      have h0 : ¬ (tr2 n x).val = 0 := by
        intro heq; exact hne ((ZMod.val_eq_zero (n := 2) (a := tr2 n x)).1 heq)
      omega
    simp [this] at h
  · intro h; simp [h]

/-- `χ(x) = -1` iff `Tr(x) = 1`. -/
theorem chi_eq_neg_one_iff {n : ℕ} (x : F2n n) : chi n x = -1 ↔ tr2 n x = 1 := by
  unfold chi
  constructor
  · intro h
    by_contra h'
    have hv := ZMod.val_lt (tr2 n x)
    have hne : tr2 n x ≠ 1 := h'
    have : (tr2 n x).val = 0 := by
      have := ZMod.val_lt (tr2 n x) (n := 2)
      have h1 : ¬ (tr2 n x).val = 1 := by
        intro heq
        apply hne
        have : tr2 n x = (1 : ZMod 2) := by
          have : (1 : ZMod 2).val = 1 := by decide
          exact ZMod.val_injective 2 (by omega)
        exact this
      omega
    have htr : tr2 n x = 0 := (ZMod.val_eq_zero (n := 2) (a := tr2 n x)).1 this
    simp [htr] at h
  · intro h
    have : (tr2 n x).val = 1 := by rw [h]; decide
    simp [this]

end
end Kasami