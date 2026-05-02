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
- `chi_orthogonality`: `∑_x χ(a*x) = 0` for `a ≠ 0`
- `chi_sum`: `∑_a χ(a*x) = 2^n` if `x = 0`, else `0`

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
  native_decide +revert

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

theorem chi_orthogonality {n : ℕ} (hn : n ≠ 0) (a : F2n n) (ha : a ≠ 0) :
    ∑ x : F2n n, chi n (a * x) = 0 := by
      -- Since multiplication by $a$ is a bijection on $F_{2^n}$, we can reindex the sum.
      have h_bij : ∑ x : F2n n, chi n (a * x) = ∑ y : F2n n, chi n y := by
        exact Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) _;
      -- Split the sum into two parts: one over the kernel of the trace map and one over the fiber over 1.
      have h_split : ∑ y : F2n n, chi n y = ∑ y ∈ Finset.univ.filter (fun y => tr2 n y = 0), 1 + ∑ y ∈ Finset.univ.filter (fun y => tr2 n y = 1), (-1 : ℤ) := by
        have h_split : ∑ y : F2n n, chi n y = ∑ y : F2n n, if tr2 n y = 0 then 1 else -1 := by
          exact Finset.sum_congr rfl fun x hx => by rcases Fin.exists_fin_two.mp ⟨ tr2 n x, rfl ⟩ with h | h <;> simp +decide [ h, chi ] ;
        simp_all +decide [ Finset.sum_ite ];
        congr with x ; have := Fin.exists_fin_two.mp ⟨ tr2 n x, rfl ⟩ ; aesop;
      simp_all +decide [ Finset.sum_add_distrib ];
      linarith [ tr2_kernel_card hn, tr2_fiber_one_card hn ]

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

/-- `χ(x) = 1` iff `Tr(x) = 0`. -/
theorem chi_eq_one_iff {n : ℕ} (x : F2n n) : chi n x = 1 ↔ tr2 n x = 0 := by
  unfold chi
  constructor
  · intro h
    have hv : (tr2 n x).val < 2 := ZMod.val_lt _
    have : (tr2 n x).val = 0 ∨ (tr2 n x).val = 1 := by omega
    rcases this with h0 | h1
    · rwa [ZMod.val_eq_zero] at h0
    · exfalso; simp [h1] at h
  · intro h; rw [h]; simp

/-- `χ(x) = -1` iff `Tr(x) = 1`. -/
theorem chi_eq_neg_one_iff {n : ℕ} (x : F2n n) : chi n x = -1 ↔ tr2 n x = 1 := by
  unfold chi
  constructor
  · intro h
    have hv : (tr2 n x).val < 2 := ZMod.val_lt _
    have : (tr2 n x).val = 0 ∨ (tr2 n x).val = 1 := by omega
    rcases this with h0 | h1
    · exfalso; simp [h0] at h
    · exact ZMod.val_injective 2 (by rw [h1]; decide)
  · intro h; rw [h]; decide

/-- Character inner product: `∑_x χ(ax)χ(bx) = 2^n · [a = b]`. -/
theorem chi_inner_product {n : ℕ} (hn : n ≠ 0) (a b : F2n n) :
    ∑ x : F2n n, chi n (a * x) * chi n (b * x) =
    if a = b then (2 ^ n : ℤ) else 0 := by
  have key : ∀ x : F2n n, chi n (a * x) * chi n (b * x) = chi n ((a + b) * x) := by
    intro x; rw [add_mul, ← chi_add]
  simp_rw [key]
  rw [chi_sum hn]
  simp [add_eq_zero_iff_eq_neg]

end
end Kasami