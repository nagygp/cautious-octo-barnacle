/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Bent (AB) Functions

A function `f : F_{2^n} → F_{2^n}` is **almost bent** (AB) if its Walsh–Hadamard
spectrum takes only the values `{0, ±2^{(n+1)/2}}`.

## Main definitions
- `IsAlmostBent f` — spectral characterization

## Main results
- Fourth moment of AB functions: `∑_a W_f(a)^4 = 2 · (2^n)^3`

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

/-- Alternative characterization using absolute values. -/
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
  have := wht_parseval hn f;
  -- From Parseval, ∑_a W_f(a)^2 = (2^n)^2 = 4^n. For AB functions, W_f(a)^2 ∈ {0, 2^{n+1}}.
  have h_sum : ∑ a : F2n n, (wht f a) ^ 2 = ∑ a ∈ Finset.univ.filter (fun a => wht f a ≠ 0), (2 ^ (n + 1) : ℤ) := by
    rw [ Finset.sum_filter, Finset.sum_congr rfl ];
    grind +suggestions;
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
  norm_cast at h_sum; nlinarith [ pow_pos ( zero_lt_two' ℕ ) n ] ;

/-
**Fourth moment identity for AB functions**:
    `∑_a W_f(a)^4 = 2 · (2^n)^3`.
-/
theorem ab_fourth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, wht f a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  -- Split the sum into two parts: where `wht f a = 0` and where `wht f a ≠ 0`.
  have h_split : ∑ a : F2n n, (wht f a) ^ 4 = ∑ a ∈ Finset.univ.filter (fun a => wht f a ≠ 0), (wht f a) ^ 4 := by
    rw [ Finset.sum_filter_of_ne ] ; aesop;
  -- For each nonzero value of `wht f a`, we have `(wht f a) ^ 4 = (2 ^ (n + 1)) ^ 2`.
  have h_nonzero : ∀ a : F2n n, wht f a ≠ 0 → (wht f a) ^ 4 = (2 ^ (n + 1)) ^ 2 := by
    intro a ha; specialize hf a; rcases hf with h | h <;> simp_all +decide [ pow_succ ] ;
    linear_combination' h * 2 ^ n * 2;
  rw [ h_split, Finset.sum_congr rfl fun x hx => h_nonzero x <| Finset.mem_filter.mp hx |>.2 ];
  norm_num [ ab_nonzero_count hn f hf ] ; ring;
  cases n <;> simp_all +decide [ pow_succ, pow_mul ] ; ring

/-! ### AB implies APN (almost perfect nonlinear) -/

/-- An AB function is also APN (almost perfect nonlinear). -/
theorem ab_implies_apn {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2 := by
  sorry

end
end Kasami