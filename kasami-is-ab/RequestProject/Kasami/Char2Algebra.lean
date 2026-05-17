/-
# Characteristic 2 Algebraic Identities

Clean, modular collection of algebraic identities in characteristic 2 fields.
Each lemma addresses exactly one concept.

## Main results

* `char2_sq_add` : (a+b)² = a² + b² (Freshman's dream, degree 1)
* `char2_pow2k_add` : (a+b)^{2^k} = a^{2^k} + b^{2^k} (Freshman's dream, general)
* `char2_neg_one` : (-1 : F) = 1
* `char2_frobenius_fixed` : x^{2^n} = x in GF(2^n)
* `char2_gold_deriv` : Derivative of Gold function x^{2^m+1}
* `char2_gold_second_deriv` : Second derivative is z^{2^m} + z (independent of x)

## References

* Lidl, Niederreiter, *Finite Fields*, §1.3
* Canteaut, Charpin, Dobbertin (2000), §2
-/
import Mathlib

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### §1 Basic Char 2 Identities -/

/-- In char 2: -1 = 1. -/
theorem char2_neg_one_eq_one : (-1 : F) = 1 := CharTwo.neg_eq 1

/-- In char 2: x + x = 0. -/
theorem char2_self_add (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- In char 2: x - y = x + y. -/
theorem char2_sub_eq_add (x y : F) : x - y = x + y := CharTwo.sub_eq_add x y

/-- In char 2: -x = x. -/
theorem char2_neg_eq (x : F) : -x = x := CharTwo.neg_eq x

/-! ### §2 Freshman's Dream -/

/-- Freshman's dream: (a+b)^2 = a^2 + b^2 in char 2. -/
theorem char2_sq_add (a b : F) : (a + b) ^ 2 = a ^ 2 + b ^ 2 :=
  add_pow_char a b 2

/-- General Freshman's dream: (a+b)^{2^k} = a^{2^k} + b^{2^k} in char 2. -/
theorem char2_pow2k_add (a b : F) (k : ℕ) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_char_pow a b 2 k

/-! ### §3 Frobenius -/

/-- In GF(2^n), every element satisfies x^{2^n} = x. -/
theorem char2_frobenius_fixed (n : ℕ) (hn : 0 < n) (hcard : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
  rw [← hcard]; exact FiniteField.pow_card x

/-- Consequence: x^{2^(k+n)} = x^{2^k} in GF(2^n). -/
theorem char2_frobenius_shift (n k : ℕ) (hn : 0 < n) (hcard : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ (k + n)) = x ^ (2 ^ k) := by
  rw [pow_add, pow_mul, char2_frobenius_fixed n hn hcard]

/-! ### §4 Gold Function Derivative -/

/-
First derivative of the Gold function x^{2^m + 1} at direction z:
    D_z(x^{2^m+1}) = x^{2^m}·z + x·z^{2^m} + z^{2^m+1}.
-/
theorem char2_gold_first_deriv (x z : F) (m : ℕ) :
    (x + z) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1) =
    x ^ (2 ^ m) * z + x * z ^ (2 ^ m) + z ^ (2 ^ m + 1) := by
  have h_expansion : (x + z) ^ (2 ^ m + 1) = (x ^ (2 ^ m) + z ^ (2 ^ m)) * (x + z) := by
    rw [ pow_succ, char2_pow2k_add ];
  grind

/-
Second derivative of the Gold function at directions (z, 1):
    D_1 D_z(x^{2^m+1}) = z^{2^m} + z, independent of x.
-/
theorem char2_gold_second_deriv (x z : F) (m : ℕ) :
    ((x + z + 1) ^ (2 ^ m + 1) + (x + z) ^ (2 ^ m + 1)) +
    ((x + 1) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1)) =
    z ^ (2 ^ m) + z := by
  -- D_1(y^{2^m+1}) = y^{2^m} + y + 1 (applying first deriv with direction 1)
  -- D_z(D_1(y^{2^m+1})) = (y+z)^{2^m} + y^{2^m} + (y+z) + y = z^{2^m} + z
  -- By the first derivative formula, we have:
  have h1 : (x + z + 1) ^ (2 ^ m + 1) + (x + z) ^ (2 ^ m + 1) = (x + z) ^ (2 ^ m) + (x + z) + 1 := by
    convert char2_gold_first_deriv ( x + z ) 1 m using 1 ; ring
  have h2 : (x + 1) ^ (2 ^ m + 1) + x ^ (2 ^ m + 1) = x ^ (2 ^ m) + x + 1 := by
    convert char2_gold_first_deriv x 1 m using 1 ; ring;
  simp_all +decide [ add_pow_char_pow ];
  grind

/-! ### §5 Kasami Exponent Number Theory -/

/-- The Kasami exponent d = 4^k - 2^k + 1 satisfies d·(2^k + 1) = 2^{3k} + 1. -/
theorem kasami_mul_gold (k : ℕ) :
    (4 ^ k - 2 ^ k + 1) * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  have h2k : 2 ^ k ≤ 4 ^ k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-- 4^k ≥ 2^k for all k. -/
theorem four_pow_ge_two_pow' (k : ℕ) : 2 ^ k ≤ 4 ^ k := by
  calc 2 ^ k ≤ (2 ^ 2) ^ k := Nat.pow_le_pow_left (by norm_num) k
    _ = 4 ^ k := by ring_nf

end