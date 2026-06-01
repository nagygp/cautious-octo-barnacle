import Mathlib
import RequestProject.Foundations.DicksonPoly

/-!
# Layer T3: Exponent Arithmetic for the Adjoint Transfer

Modular exponent arithmetic connecting the G-function to the M-function.

## Key definitions

- `expG k n = 2^n - 2 - 2^k` : the G-function exponent (y^{-(q+1)})
- `expM k n = 2^n - 1 - 2^k` : the M-function exponent (y^{-q})
- `halfExp k n = 2^{n-1} - 2^{k-1} - 1` : satisfies `2 * halfExp = expG`
-/

namespace AdjointTransfer.ExpArith

open Finset BigOperators

/-- The G-function exponent: `a_G = 2^n - 2 - 2^k`. -/
def expG (k n : ℕ) : ℕ := 2 ^ n - 2 - 2 ^ k

/-- The M-function exponent: `a_M = 2^n - 1 - 2^k`. -/
def expM (k n : ℕ) : ℕ := 2 ^ n - 1 - 2 ^ k

/-- The "half" exponent: `halfExp k n = 2^{n-1} - 2^{k-1} - 1`.
    Satisfies `2 * halfExp = expG k n`.
    This is the exponent k from Theorem 3.2: k = 2^{n-1} - 2^{k-1} - 1. -/
def halfExp (k n : ℕ) : ℕ := 2 ^ (n - 1) - 2 ^ (k - 1) - 1

/-- `y^{-(q+1)} = y^{expG k n}` for `y ∈ F*` with `|F| = 2^n`. -/
lemma inv_pow_qp1_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (hcard : Fintype.card F = 2 ^ n)
    {y : F} (hy : y ≠ 0) :
    (y ^ (2 ^ k + 1))⁻¹ = y ^ expG k n := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [← pow_add, Nat.add_comm, expG]
  rw [tsub_add_eq_add_tsub, tsub_eq_of_eq_add]
  rw [FiniteField.pow_card_sub_one_eq_one y hy]
  · grind
  · refine Nat.le_sub_of_add_le ?_
    rw [show 2 ^ n = 2 ^ k * 2 ^ (n - k) by rw [← pow_add, Nat.add_sub_of_le hkn.le]]
    nlinarith [pow_le_pow_right₀ (show 1 ≤ 2 by decide) hk,
               pow_le_pow_right₀ (show 1 ≤ 2 by decide) (show n - k ≥ 1 by exact Nat.sub_pos_of_lt hkn)]

/-- `y^{-q} = y^{expM k n}` for `y ∈ F*`. -/
lemma inv_pow_q_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (hcard : Fintype.card F = 2 ^ n)
    {y : F} (hy : y ≠ 0) :
    (y ^ (2 ^ k))⁻¹ = y ^ expM k n := by
  have h1 : expM k n + 2 ^ k = 2 ^ n - 1 :=
    Nat.sub_add_cancel (Nat.le_sub_one_of_lt (pow_lt_pow_right₀ (by decide) hkn))
  have h2 : y ^ (expM k n + 2 ^ k) = 1 := by
    rw [h1, ← hcard, FiniteField.pow_card_sub_one_eq_one y hy]
  exact inv_eq_of_mul_eq_one_left (by rw [← h2, pow_add])

/-- `expG k n + (2^k + 1) = 2^n - 1`. -/
lemma expG_add_qp1 {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    expG k n + (2 ^ k + 1) = 2 ^ n - 1 := by
  unfold expG
  rw [tsub_tsub, tsub_add_eq_add_tsub]
  · omega
  · rw [show 2 ^ n = 2 ^ k * 2 ^ (n - k) by rw [← pow_add, Nat.add_sub_of_le hkn.le]]
    nlinarith [Nat.pow_le_pow_right two_pos (show n - k ≥ 1 by exact Nat.sub_pos_of_lt hkn),
               Nat.pow_le_pow_right two_pos hk]

/-- `expM k n + 2^k = 2^n - 1`. -/
lemma expM_add_q {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    expM k n + 2 ^ k = 2 ^ n - 1 :=
  Nat.sub_add_cancel (Nat.le_sub_one_of_lt (pow_lt_pow_right₀ (by decide) hkn))

/-
The doubling identity: `2 * halfExp k n = expG k n` (= 2^n - 2 - 2^k).
-/
lemma two_mul_halfExp {k n : ℕ} (hk : 1 < k) (hkn : k < n) :
    2 * halfExp k n = expG k n := by
  obtain ⟨ m, rfl ⟩ := Nat.exists_eq_add_of_lt hkn;
  unfold halfExp expG;
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_sub_left_distrib ] ; ring;
  grind

/-- `halfExp` is exactly the exponent from Theorem 3.2. -/
lemma halfExp_eq {k n : ℕ} (hk : 1 < k) (hkn : k < n) :
    halfExp k n = 2 ^ (n - 1) - 2 ^ (k - 1) - 1 := rfl

/-
The G-function equals the Dickson polynomial at y⁻¹:
    `S_k(y)² · y^{expG k n} = f_k(y⁻¹)`.

    Proof: Apply `S_sq_mul_eq_dicksonF` with `x = y⁻¹`:
    `S_k(y)² · (y⁻¹)^{q+1} = f_k(y⁻¹)`.
    Then `(y⁻¹)^{q+1} = y^{-(q+1)} = y^{expG}`.
-/
lemma G_eq_dicksonF_inv {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (hcard : Fintype.card F = 2 ^ n)
    {y : F} (hy : y ≠ 0) :
    (∑ i ∈ Finset.range k, y ^ (2 ^ i)) ^ 2 * y ^ expG k n =
    DicksonKasami.dicksonF k y⁻¹ := by
  convert DicksonKasami.S_sq_mul_eq_dicksonF k ( inv_ne_zero hy ) using 1;
  simp +zetaDelta at *;
  rw [ inv_pow_qp1_eq hk hkn hcard hy ] ; aesop

end AdjointTransfer.ExpArith