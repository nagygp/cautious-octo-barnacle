import Mathlib

/-!
# Coprimality and invertibility of Mersenne numbers

Pure number theory, independent of any field: the Mersenne numbers `2^k − 1` and
`2ⁿ − 1` are coprime exactly when `k` and `n` are, because
`gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`.

* `mersenne_coprime` — `gcd(k,n) = 1 ⟹ gcd(2^k − 1, 2ⁿ − 1) = 1`;
* `inv_mod_exists`   — hence `2^k − 1` is invertible modulo `2ⁿ − 1`.

This is the arithmetic behind the exponent `k'` with `k·k' ≡ 1 (mod n)` used to
recover `x` from `x^{2^k}` on `𝔽_{2ⁿ}`.
-/

namespace Kasami.NumberTheory

/-- Since `gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`, coprimality of `k` and `n`
makes `2^k − 1` and `2ⁿ − 1` coprime. -/
theorem mersenne_coprime {k n : ℕ} (h : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ n - 1) := by
  unfold Nat.Coprime at *
  rw [Nat.pow_sub_one_gcd_pow_sub_one]
  simp [h]

/-- The multiplicative inverse of `2^k − 1` modulo `2ⁿ − 1` exists whenever
`gcd(k, n) = 1` (and `1 < 2ⁿ − 1`). -/
theorem inv_mod_exists {k n : ℕ} (h : Nat.Coprime k n) (hn : 1 < 2 ^ n - 1) :
    ∃ b, (2 ^ k - 1) * b % (2 ^ n - 1) = 1 := by
  obtain ⟨b, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime (mersenne_coprime h) hn
  exact ⟨b, hb.2⟩

end Kasami.NumberTheory
