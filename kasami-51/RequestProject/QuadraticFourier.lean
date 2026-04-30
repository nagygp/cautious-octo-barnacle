import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-!
# Walsh Spectrum of Quadratic Boolean Functions (Kasami-50)

For a quadratic Boolean function Q on GF(2^n) with n odd, the Walsh–Hadamard
transform W_Q takes values in {0, ±2^((n+1)/2)}.

The key steps are:
1. Each nonzero Walsh value satisfies W² = 2^(n+1).
2. Since n is odd, n+1 is even, so 2^((n+1)/2) is an integer.
3. An integer whose square equals 2^(n+1) must be ±2^((n+1)/2).
-/

section IntSquareRoot

/-! ### Integer square-root lemma for powers of two -/

/-- Auxiliary: if `W.natAbs = k` then `W = k` or `W = -k`. -/
lemma int_eq_or_neg_of_natAbs_eq (W : ℤ) (k : ℕ) (h : W.natAbs = k) :
    W = (k : ℤ) ∨ W = -(k : ℤ) := by
  sorry

/-- Auxiliary: if `a ^ 2 = b ^ 2` for natural numbers then `a = b`. -/
lemma nat_sq_inj (a b : ℕ) (h : a ^ 2 = b ^ 2) : a = b := by
  sorry

/-- Auxiliary: `W.natAbs ^ 2 = (2 ^ k) ^ 2 → W.natAbs = 2 ^ k`,
    obtained by lifting `W ^ 2 = 2 ^ (2 * k)` through `Int.natAbs_sq`. -/
lemma natAbs_eq_of_sq_eq_pow (W : ℤ) (k : ℕ)
    (hW : W ^ 2 = (2 : ℤ) ^ (2 * k)) :
    W.natAbs = 2 ^ k := by
  sorry

/-- **Key lemma**: If `W ^ 2 = 2 ^ (n + 1)` and `n` is odd, then
    `W = 2 ^ ((n + 1) / 2)` or `W = -(2 ^ ((n + 1) / 2))`. -/
theorem walsh_int_values (W : ℤ) (n : ℕ) (hn : Odd n)
    (hW : W ^ 2 = (2 : ℤ) ^ (n + 1)) :
    W = (2 : ℤ) ^ ((n + 1) / 2) ∨ W = -(2 : ℤ) ^ ((n + 1) / 2) := by
  obtain ⟨k, hk⟩ := hn
  have heven : n + 1 = 2 * ((n + 1) / 2) := by omega
  have hnat : W.natAbs = 2 ^ ((n + 1) / 2) := by
    apply natAbs_eq_of_sq_eq_pow
    rwa [heven] at hW
  exact int_eq_or_neg_of_natAbs_eq W _ hnat

end IntSquareRoot

section WalshSpectrum

/-! ### Walsh Spectrum Theorem -/

/-- The Walsh spectrum of a quadratic Boolean function on GF(2^n), n odd,
    takes values in {0, 2^((n+1)/2), -2^((n+1)/2)}.

    We model this as: for every Walsh value `W`, either `W = 0` or
    `W ^ 2 = 2 ^ (n+1)`, and in the latter case `W ∈ {±2^((n+1)/2)}`. -/
theorem walsh_spectrum_values (n : ℕ) (hn : Odd n) (W : ℤ)
    (hW : W = 0 ∨ W ^ 2 = (2 : ℤ) ^ (n + 1)) :
    W ∈ ({0, (2 : ℤ) ^ ((n + 1) / 2), -(2 : ℤ) ^ ((n + 1) / 2)} : Set ℤ) := by
  rcases hW with h0 | hsq
  · left; exact h0
  · right
    exact walsh_int_values W n hn hsq

end WalshSpectrum
