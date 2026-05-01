import Mathlib

/-!
# CCD Counting Argument — Frobenius-GCD and Kernel Bounds

Proves the Frobenius-GCD theorem and foundational kernel bound results.
-/

open scoped BigOperators

set_option maxHeartbeats 1600000

/-! ## Frobenius Fixed-Point Algebra -/

section FrobeniusGCD

variable {M : Type*} [Monoid M]

lemma frobenius_iter (z : M) (b : ℕ) (h : z ^ (2 ^ b) = z) (q : ℕ) :
    z ^ (2 ^ (b * q)) = z := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

lemma frobenius_mod_step (z : M) (a b : ℕ)
    (ha : z ^ (2 ^ a) = z) (hb : z ^ (2 ^ b) = z) :
    z ^ (2 ^ (a % b)) = z := by
  rcases b.eq_zero_or_pos with rfl | _
  · simpa using ha
  · have hab : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
    have : z ^ (2 ^ a) = z ^ (2 ^ (a % b)) := by
      conv_lhs => rw [hab, pow_add, pow_mul, frobenius_iter z b hb (a / b)]
    rw [ha] at this; exact this.symm

/-- **Frobenius-GCD theorem.** -/
theorem frobenius_gcd_fixed (z : M) (a b : ℕ)
    (ha : z ^ (2 ^ a) = z) (hb : z ^ (2 ^ b) = z) :
    z ^ (2 ^ (Nat.gcd a b)) = z := by
  induction a, b using Nat.gcd.induction with
  | H0 b => simp; exact hb
  | H1 a b _ ih =>
    rw [Nat.gcd_rec]
    exact ih (frobenius_mod_step z b a hb ha) ha

end FrobeniusGCD

/-- In any field, `z ^ 2 = z` forces `z = 0` or `z = 1`. -/
theorem sq_frob_eq_zero_or_one {F : Type*} [Field F] (z : F)
    (h : z ^ 2 = z) : z = 0 ∨ z = 1 := by
  have h1 : z * (z - 1) = 0 := by
    have : z * z = z := by rwa [sq] at h
    have : z * (z - 1) = z * z - z := by ring
    rw [this, ‹z * z = z›, sub_self]
  exact mul_eq_zero.mp h1 |>.imp id sub_eq_zero.mp

/-- `gcd(k, 2k+1) = 1` for all `k`. -/
lemma gcd_k_2k1_eq_one (k : ℕ) : Nat.gcd k (2 * k + 1) = 1 := by
  have : Nat.gcd k (2 * k + 1) ∣ 1 := by
    have h1 : Nat.gcd k (2 * k + 1) ∣ 2 * k :=
      dvd_trans (Nat.gcd_dvd_left k (2 * k + 1)) ⟨2, by ring⟩
    have h2 : Nat.gcd k (2 * k + 1) ∣ (2 * k + 1) :=
      Nat.gcd_dvd_right k (2 * k + 1)
    have h3 := Nat.dvd_sub h2 h1
    rw [show 2 * k + 1 - 2 * k = 1 from by omega] at h3
    exact h3
  exact Nat.eq_one_of_dvd_one this

/-- **CCD kernel bound.**
    If `z^(2^a) = z` and `z^(2^b) = z` and `gcd(a,b) = 1`,
    then `z = 0 ∨ z = 1`. -/
theorem ccd_kernel_bound {F : Type*} [Field F] (z : F)
    (a b : ℕ) (hgcd : Nat.gcd a b = 1)
    (ha : z ^ (2 ^ a) = z) (hb : z ^ (2 ^ b) = z) :
    z = 0 ∨ z = 1 := by
  have h := frobenius_gcd_fixed z a b ha hb
  rw [hgcd] at h
  exact sq_frob_eq_zero_or_one z (by simpa using h)
