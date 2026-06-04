import Mathlib

/-!
# Exponent Arithmetic for Power-of-Two Cancellation

Pure ℕ/ℤ arithmetic: given `2ⁿ · κ = (2^{n-1})ᵐ`, deduce `κ = 2^{(m-1)n - m}`.

Standalone — no dependency on field theory or characters.

## Key results
- `exp_identity`: `m(n-1) - n = (m-1)n - m`
- `exp_cancel`: the ℕ cancellation
- `exp_cancel_int`: ℤ-lifted version
-/

namespace MTupleCount

/-- `m(n-1) - n = (m-1)n - m` for `n ≥ 3, m ≥ 2`. -/
lemma exp_identity (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m * (n - 1) - n = (m - 1) * n - m := by
  have h1 : m * (n - 1) = m * n - m := Nat.mul_sub_one m n
  have h2 : (m - 1) * n = m * n - n := by rw [Nat.sub_one_mul]
  omega

/-- `2ⁿ · κ = (2^{n-1})ᵐ ⟹ κ = 2^{(m-1)n - m}` in ℕ. -/
theorem exp_cancel (n m κ₀ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (h : 2 ^ n * κ₀ = (2 ^ (n - 1)) ^ m) : κ₀ = 2 ^ ((m - 1) * n - m) := by
  rw [show (2 ^ (n - 1)) ^ m = 2 ^ (m * (n - 1)) from by ring] at h
  have hmn : n ≤ m * (n - 1) := by
    calc n ≤ 2 * (n - 1) := by omega
      _ ≤ m * (n - 1) := Nat.mul_le_mul_right _ hm
  rw [show m * (n - 1) = n + (m * (n - 1) - n) from (Nat.add_sub_cancel' hmn).symm,
      pow_add] at h
  rw [← exp_identity n m hn hm]
  exact mul_left_cancel₀ (by positivity) h

/-- ℤ-lifted version of `exp_cancel`. -/
theorem exp_cancel_int (n m κ₀ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (h : (2 : ℤ) ^ n * (κ₀ : ℤ) = ((2 : ℤ) ^ (n - 1)) ^ m) :
    κ₀ = 2 ^ ((m - 1) * n - m) :=
  exp_cancel n m κ₀ hn hm (by exact_mod_cast h)

end MTupleCount
