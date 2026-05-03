/-
  MersenneGCD.lean
  
  Proves the Mersenne GCD identity:
    gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1
  
  And the corollary: Nat.Coprime k n → Nat.Coprime (2^k - 1) (2^n - 1)
-/
import Mathlib

set_option maxHeartbeats 800000

open Nat

/-! ### Mersenne GCD identity -/

/-
If `m ∣ k`, then `2^m - 1 ∣ 2^k - 1`.
-/
lemma two_pow_sub_one_dvd_of_dvd {m k : ℕ} (h : m ∣ k) :
    2 ^ m - 1 ∣ 2 ^ k - 1 := by
  obtain ⟨ k, rfl ⟩ := h;
  simpa only [ one_pow, pow_mul ] using nat_sub_dvd_pow_sub_pow _ 1 k

/-
`gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1` for natural numbers.
-/
theorem mersenne_gcd (a b : ℕ) :
    Nat.gcd (2 ^ a - 1) (2 ^ b - 1) = 2 ^ (Nat.gcd a b) - 1 := by
  exact?

/-- If `gcd(k, n) = 1`, then `gcd(2^k - 1, 2^n - 1) = 1`. -/
theorem coprime_mersenne_of_coprime {k n : ℕ} (hc : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ n - 1) := by
  unfold Nat.Coprime at *
  rw [mersenne_gcd]
  rw [hc]
  simp