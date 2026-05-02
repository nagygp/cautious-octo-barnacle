/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical Additive Character of F_{2^n}

Constructs the canonical additive character `χ : F_{2^n} → ℤ` defined by
`χ(x) = (-1)^{Tr(x)}`, where `Tr` is the absolute trace to F₂.

## Main definitions
- `chi n : F2n n → ℤ` — the canonical additive character
- `chiAddChar n : AddChar (F2n n) ℤ` — packaged as an `AddChar`

## Main results
- `chi_values`: `χ(x) ∈ {-1, 1}`
- `chi_sq`: `χ(x)^2 = 1`
- `chi_add`: `χ(x+y) = χ(x) * χ(y)`
- `chi_orthogonality`: `∑_x χ(a·x) = 0` for `a ≠ 0`
- `chi_sum`: the full orthogonality relation
- `chi_inner_product`: `∑_x χ(ax)χ(bx) = 2^n · [a = b]`

## References
- [Lidl, Niederreiter, *Finite Fields*], Chapter 5
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §2.3
-/

import Mathlib
import RequestProject.WalshHadamard.Basic
import RequestProject.WalshHadamard.Trace

namespace WalshHadamardTheory

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

/-- Key property: `(-1)^{val(a + b)} = (-1)^{val(a)} * (-1)^{val(b)}` in ZMod 2. -/
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

/-! ### Packaging as AddChar -/

/-- The canonical character as an `AddChar`. -/
noncomputable def chiAddChar (n : ℕ) : AddChar (F2n n) ℤ where
  toFun := chi n
  map_zero_eq_one' := chi_zero n
  map_add_eq_mul' := chi_add

@[simp]
theorem chiAddChar_apply {n : ℕ} (x : F2n n) : chiAddChar n x = chi n x := rfl

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
  -- Since $a \neq 0$, multiplication by $a$ is a bijection on $F_{2^n}$.
  have h_bij : Function.Bijective (fun x : F2n n => a * x) := by
    exact ⟨ mul_right_injective₀ ha, mul_left_surjective₀ ha ⟩;
  -- Since $\chi$ is a character, we have $\sum_{x \in F_{2^n}} \chi(ax) = \sum_{x \in F_{2^n}} \chi(x)$.
  have h_char_sum : ∑ x : F2n n, chi n (a * x) = ∑ x : F2n n, chi n x := by
    exact Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) _;
  -- Split the sum by trace value: exactly $2^{n-1}$ elements have trace $0$ (contributing $+1$ each) and $2^{n-1}$ have trace $1$ (contributing $-1$ each).
  have h_split_sum : ∑ x : F2n n, chi n x = ∑ x ∈ Finset.univ.filter (fun x => tr2 n x = 0), 1 + ∑ x ∈ Finset.univ.filter (fun x => tr2 n x = 1), (-1 : ℤ) := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; rcases h : tr2 n x with ( _ | _ | k ) <;> norm_num [ h, chi ] ;
    · rfl;
    · contradiction;
  simp_all +decide [ Finset.sum_ite ];
  linarith [ tr2_kernel_card hn, tr2_fiber_one_card hn ]

/-- The full orthogonality relation combining both cases. -/
theorem chi_sum {n : ℕ} (hn : n ≠ 0) (a : F2n n) :
    ∑ x : F2n n, chi n (a * x) = if a = 0 then (2 ^ n : ℤ) else 0 := by
  split
  · next h => subst h; exact chi_sum_zero hn
  · next h => exact chi_orthogonality hn a h

/-
Character inner product: `∑_x χ(ax)χ(bx) = 2^n · [a = b]`.
-/
theorem chi_inner_product {n : ℕ} (hn : n ≠ 0) (a b : F2n n) :
    ∑ x : F2n n, chi n (a * x) * chi n (b * x) =
    if a = b then (2 ^ n : ℤ) else 0 := by
  convert chi_sum hn ( a + b ) using 1;
  · simp +decide only [chi, ← neg_one_pow_val_add, add_mul];
    simp +decide [ ← map_add ];
  · simp +decide [ add_eq_zero_iff_eq_neg ]

/-! ### Trace-character equivalences -/

/-
`χ(x) = 1` iff `Tr(x) = 0`.
-/
theorem chi_eq_one_iff {n : ℕ} (x : F2n n) : chi n x = 1 ↔ tr2 n x = 0 := by
  unfold chi;
  cases' Fin.exists_fin_two.mp ⟨ ( tr2 n ) x, rfl ⟩ with h h <;> simp +decide [ h ]

/-
`χ(x) = -1` iff `Tr(x) = 1`.
-/
theorem chi_eq_neg_one_iff {n : ℕ} (x : F2n n) : chi n x = -1 ↔ tr2 n x = 1 := by
  cases Fin.exists_fin_two.mp ⟨ tr2 n x, rfl ⟩ <;> ( unfold chi at * ; aesop )

/-
Indicator via character: `(1 + χ(x)) / 2 = [Tr(x) = 0]`.
-/
theorem chi_indicator_kernel {n : ℕ} (x : F2n n) :
    (1 + chi n x) / 2 = if tr2 n x = 0 then 1 else 0 := by
  unfold chi;
  cases' Fin.exists_fin_two.mp ⟨ ( tr2 n ) x, rfl ⟩ with h h <;> simp +decide [ h ]

end
end WalshHadamardTheory