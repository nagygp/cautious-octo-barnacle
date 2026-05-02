/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Bent (AB) Functions

A function `f : F_{2^n} → F_{2^n}` is **almost bent** (AB) if its Walsh–Hadamard
spectrum takes only the values `{0, ±2^{(n+1)/2}}`.

## Main definitions
- `IsAlmostBent f` — spectral characterization

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.2
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000], SIAM J. Discrete Math.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.WalshHadamard

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### Definition -/

/-- A function `f : F_{2^n} → F_{2^n}` is **almost bent** if the square of each
    Walsh–Hadamard coefficient is either `0` or `2^(n+1)`.
    This is equivalent to `W_f(a) ∈ {0, ±2^{(n+1)/2}}` when `n` is odd. -/
def IsAlmostBent {n : ℕ} (f : F2n n → F2n n) : Prop :=
  ∀ a : F2n n, wht f a ^ 2 = 0 ∨ wht f a ^ 2 = (2 ^ (n + 1) : ℤ)

/-- Alternative characterization using zero vs nonzero. -/
theorem isAlmostBent_iff_abs {n : ℕ} (f : F2n n → F2n n) :
    IsAlmostBent f ↔ ∀ a : F2n n, wht f a = 0 ∨ (wht f a) ^ 2 = 2 ^ (n + 1) := by
  constructor
  · intro h a
    rcases h a with h1 | h1
    · left; exact sq_eq_zero_iff.mp h1
    · right; exact h1
  · intro h a
    rcases h a with h1 | h1
    · left; simp [h1]
    · right; exact h1

/-! ### Fourth moment of AB functions -/

/-
For an AB function, the number of `a` with `W_f(a) ≠ 0` is `2^{n-1}`.
-/
theorem ab_nonzero_count {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    (Finset.univ.filter fun a : F2n n => wht f a ≠ 0).card = 2 ^ (n - 1) := by
  have h_count : ∑ a : F2n n, wht f a ^ 2 = 2 ^ (n + 1) * (Finset.card (Finset.filter (fun a => wht f a ≠ 0) Finset.univ)) := by
    have h_count : ∀ a : F2n n, wht f a ^ 2 = if wht f a = 0 then 0 else 2 ^ (n + 1) := by
      grind +suggestions;
    simp +decide [ h_count, Finset.sum_ite, mul_comm ];
  have h_parseval : ∑ a : F2n n, wht f a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    exact?;
  cases n <;> simp_all +decide [ pow_succ' ] ; nlinarith [ pow_pos ( zero_lt_two' ℤ ) ‹_› ]

/-
**Fourth moment identity for AB functions**:
    `∑_a W_f(a)^4 = 2 · (2^n)^3`.
-/
theorem ab_fourth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, wht f a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  -- Since $wht f a ^ 2$ is either $0$ or $2^{n+1}$, we know that $wht f a ^ 4$ is either $0$ or $(2^{n+1})^2 = 2^{2(n+1)}$.
  have h_wht_sq : ∀ a : F2n n, wht f a ^ 4 = if wht f a = 0 then 0 else ((2 : ℤ) ^ (n + 1)) ^ 2 := by
    intro x; specialize hf x; split_ifs <;> simp_all +decide [ pow_succ, mul_assoc ] ;
  have := ab_nonzero_count hn f hf; simp_all +decide [ Finset.sum_ite ] ; ring;
  cases n <;> simp_all +decide [ pow_succ', pow_mul ] ; ring

end
end Kasami