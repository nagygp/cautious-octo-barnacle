/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Core Definitions for Kasami Power Functions

This file defines the Kasami exponent, the power function on `GF(2^n)`,
and the associated difference set.
-/
import Mathlib

open scoped BigOperators
noncomputable section

namespace Kasami

/-- The Kasami exponent: `e(k) = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`.
This is defined as a natural number; the subtraction is valid because
`4^k = (2^k)^2 ≥ 2^k` for all `k`. -/
def kasamiExponent (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

@[simp]
theorem kasamiExponent_zero : kasamiExponent 0 = 1 := by
  simp [kasamiExponent]

theorem two_pow_k_le_four_pow_k (k : ℕ) : 2 ^ k ≤ 2 ^ (2 * k) := by
  apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
  omega

theorem kasamiExponent_pos (k : ℕ) : 0 < kasamiExponent k := by
  unfold kasamiExponent
  have := two_pow_k_le_four_pow_k k
  omega

/-- The Kasami power function `F(x) = x^{e(k)}` on `GF(2^n)`. -/
def powerFun {n : ℕ} [NeZero n] (k : ℕ) (x : GaloisField 2 n) :
    GaloisField 2 n :=
  x ^ kasamiExponent k

@[simp]
theorem powerFun_zero {n : ℕ} [NeZero n] (k : ℕ) :
    powerFun k (0 : GaloisField 2 n) = 0 := by
  exact zero_pow (kasamiExponent_pos k).ne'

/-- The difference set `Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2^n)}`. -/
def deltaSet {n : ℕ} [NeZero n] (k : ℕ) : Set (GaloisField 2 n) :=
  { x | ∃ b : GaloisField 2 n, x = powerFun k b + powerFun k (b + 1) + 1 }

end Kasami

end
