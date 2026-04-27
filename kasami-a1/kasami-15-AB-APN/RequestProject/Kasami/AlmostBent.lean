/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Bent (AB) Functions

A function `f : F_{2^n} → F_{2^n}` is **almost bent** (AB) if its Walsh–Hadamard
spectrum takes only the values `{0, ±2^{(n+1)/2}}`.

## Main definitions
- `IsAlmostBent f` — spectral characterization

## Main results
- Equivalence of AB characterizations
- Fourth moment of AB functions: `∑_a W_f(a)^4 = 2 · (2^n)^3`

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.2
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000], SIAM J. Discrete Math.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.ABImpliesAPN

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
For an AB function, the number of `a` with `W_f(a) ≠ 0` is `(2^n - 1) · 2^{n-1} / ...`.
    More precisely, from Parseval: the number of nonzero WHT values times `2^{n+1}` equals `4^n`.
    So the count is `4^n / 2^{n+1} = 2^{n-1}`.
-/
theorem ab_nonzero_count {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    (Finset.univ.filter fun a : F2n n => wht f a ≠ 0).card = 2 ^ (n - 1) := by
  have h_parseval : ∑ a : F2n n, (wht f a) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    exact?;
  -- Since $W_f(a)^2 \in \{0, 2^{n+1}\}$ for all $a$, we can split the sum into two parts: the terms where $W_f(a) = 0$ and the terms where $W_f(a) \neq 0$.
  have h_split_sum : ∑ a : F2n n, (wht f a) ^ 2 = ∑ a ∈ Finset.univ.filter (fun a => wht f a ≠ 0), (2 ^ (n + 1) : ℤ) := by
    rw [ Finset.sum_filter ];
    refine' Finset.sum_congr rfl fun x hx => _;
    have := hf x; split_ifs <;> simp_all +decide ;
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
  norm_cast at h_split_sum; nlinarith [ pow_pos ( zero_lt_two' ℕ ) n ] ;

/-
**Fourth moment identity for AB functions**:
    `∑_a W_f(a)^4 = 2 · (2^n)^3`.
    Proof: Each nonzero `W_f(a)^2 = 2^{n+1}`, so `W_f(a)^4 = 2^{2(n+1)} = 4^{n+1}`.
    Count of nonzero values is `2^{n-1}`.
    So `∑ W_f(a)^4 = 2^{n-1} · 4^{n+1} = 2^{n-1} · 2^{2n+2} = 2^{3n+1} = 2 · 8^n = 2 · (2^n)^3`.
-/
theorem ab_fourth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, wht f a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  have h_fourth_moment : ∑ a : F2n n, wht f a ^ 4 = ∑ a ∈ Finset.univ.filter fun a : F2n n => wht f a ≠ 0, (2 ^ (n + 1) : ℤ) ^ 2 := by
    rw [ Finset.sum_filter, Finset.sum_congr rfl ];
    intro a ha; specialize hf a; split_ifs <;> simp_all +decide [ pow_succ, mul_assoc ] ;
  simp_all +decide [ Finset.sum_ite ];
  rw [ ab_nonzero_count hn f hf ] ; ring;
  cases n <;> norm_num [ pow_succ, pow_mul ] at * ; ring

/-! ### AB implies APN (almost perfect nonlinear) -/

/-- An AB function (in the full two-argument sense) is also APN (almost perfect nonlinear).
    This means: for any `a ≠ 0` and `b`, the equation `f(x+a) + f(x) = b`
    has at most 2 solutions.

    **Note**: The hypothesis was changed from `IsAlmostBent f` (one-argument WHT spectrum)
    to `IsAB f` (two-argument WHT spectrum, the standard cryptographic definition).
    The one-argument condition alone does not imply APN for general functions;
    for power functions, use `power_ab_all_components` from FourthMoment.lean
    to upgrade `IsAlmostBent` to `IsAB`.

    Proof ported from kasami-11 (GF(2)^n framework) to GaloisField 2 n. -/
theorem ab_implies_apn {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAB f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2 := by
  intro a ha b
  exact isAB_implies_apn hn f hf a ha b

end
end Kasami