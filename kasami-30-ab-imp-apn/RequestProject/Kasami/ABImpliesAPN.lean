/-
# Decomposition of `ab_implies_apn`

This file decomposes `ab_implies_apn` — "every Almost Bent function is APN" —
into small, independently provable lemmas.

## Proof outline

For a fixed `a ≠ 0`, let `N(b) := |{x : f(x+a) + f(x) = b}|`. We need `N(b) ≤ 2` for all `b`.

1. `N(b)` is always even (solutions come in pairs `{x, x+a}`). — **Proved** as `derivCount_even`
2. `∑_b N(b) = 2^n`. — **Proved** as `derivCount_sum_int`
3. `∑_b N(b)² ≤ 2^{n+1}`. — **Key inequality** (see `ab_deriv_sum_sq_le` below)
4. Steps 1–3 together imply `N(b) ≤ 2` by `even_sum_sq_bound`. — **Proved** in `FourthMoment.lean`

For step 3, we use the Parseval identity for derivatives (`deriv_parseval`):
  `2^n · ∑_b N(b)² = ∑_c S(c,a)²`
where `S(c,a) = ∑_x χ(c · (f(x+a) + f(x)))`.

So step 3 reduces to bounding `∑_c S(c,a)² ≤ 2^{2n+1}`.

Splitting into `c = 0` and `c ≠ 0`:
  - `S(0,a) = 2^n`, contributing `2^{2n}` to the sum. — **Proved** below
  - We need `∑_{c≠0} S(c,a)² ≤ 2^{2n}`. — **Sorry'd** (hard core inequality)

## Status of sub-lemmas

| Lemma | Status | Source |
|-------|--------|--------|
| `derivCount_even` | ✅ Proved | `FourthMoment.lean` |
| `derivCount_sum_int` | ✅ Proved | `FourthMoment.lean` |
| `even_sum_sq_bound` | ✅ Proved | `FourthMoment.lean` |
| `deriv_parseval` | ✅ Proved | `APNFromAB.lean` |
| `deriv_char_sum_zero` | ✅ Proved | below |
| `deriv_char_sum_sq_split` | ✅ Proved | below |
| `ab_deriv_char_sum_sq_nonzero_le` | ❌ Sorry | below (hard core inequality) |
| `ab_deriv_sum_sq_le` | ✅ Proved | below (from above lemmas) |
| `ab_implies_apn` | ✅ Proved | below (from above lemmas) |
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.APNFromAB

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Lemma 1: The c = 0 term -/

/-- When `c = 0`, the character sum `S(0, a) = 2^n`. -/
theorem deriv_char_sum_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    ∑ x : F2n n, chi n (0 * (f (x + a) + f x)) = (2 ^ n : ℤ) := by
  simp [chi_zero, F2n.card n hn]

/-! ### Lemma 2: Split the sum of squares into c = 0 and c ≠ 0 -/

/-- The sum `∑_c S(c,a)²` splits into the `c = 0` contribution and the `c ≠ 0` part. -/
theorem deriv_char_sum_sq_split {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    ∑ c : F2n n, (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 =
    (2 ^ n : ℤ) ^ 2 +
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2n n))]
  congr 1
  · rw [deriv_char_sum_zero hn]
  · apply Finset.sum_congr
    · ext x; simp [Finset.mem_erase]
    · intros; rfl

/-! ### Lemma 3: The hard core inequality (sorry'd) -/

/-
**Core inequality** (sorry'd): For an AB function and `a ≠ 0`,
    `∑_{c ≠ 0} S(c,a)² ≤ 2^{2n}`.

    This is the key step that connects the AB spectrum condition
    to the derivative distribution. A proof would require showing
    that the AB property of `f` constrains the character sums
    `∑_x χ(c · D_a f(x))` for all nonzero `c`.

    **Remark**: For power functions `f(x) = x^d`, this follows because
    multiplying `f` by a nonzero scalar `c` preserves the Walsh spectrum
    (via the substitution `x ↦ c^{1/d} x`), so all component functions
    inherit the AB property. For general functions, this may require
    additional hypotheses.
-/
theorem ab_deriv_char_sum_sq_nonzero_le {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAlmostBent f) (a : F2n n) (ha : a ≠ 0) :
    ∑ c ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 ≤ (2 ^ n : ℤ) ^ 2 := by
  sorry

/-! ### Lemma 4: Total character-sum-square bound -/

/-- From Lemmas 2 and 3: `∑_c S(c,a)² ≤ 2^{2n+1}`. -/
theorem ab_deriv_char_sum_sq_le {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAlmostBent f) (a : F2n n) (ha : a ≠ 0) :
    ∑ c : F2n n, (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 ≤
    2 * (2 ^ n : ℤ) ^ 2 := by
  rw [deriv_char_sum_sq_split hn]
  linarith [ab_deriv_char_sum_sq_nonzero_le hn f hf a ha]

/-! ### Lemma 5: Derivative distribution sum-of-squares bound -/

/-- For AB functions and `a ≠ 0`: `∑_b N_a(b)² ≤ 2^{n+1}`.
    Uses `deriv_parseval` + Lemma 4. -/
theorem ab_deriv_sum_sq_le {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAlmostBent f) (a : F2n n) (ha : a ≠ 0) :
    ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 ≤ 2 ^ (n + 1) := by
  have h_parseval := deriv_parseval hn f a
  have h_bound := ab_deriv_char_sum_sq_le hn f hf a ha
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  -- From parseval: 2^n · ∑_b N(b)² = ∑_c S(c,a)² ≤ 2 · (2^n)²
  -- So ∑_b N(b)² ≤ 2 · (2^n)² / 2^n = 2 · 2^n = 2^{n+1}
  have : (2 ^ n : ℤ) * ∑ b, (derivCount f a b : ℤ) ^ 2 ≤ 2 * (2 ^ n : ℤ) ^ 2 := by
    linarith
  have : ∑ b, (derivCount f a b : ℤ) ^ 2 ≤ 2 * 2 ^ n := by
    nlinarith
  linarith [show (2 : ℤ) * 2 ^ n = 2 ^ (n + 1) by ring]

/-! ### Lemma 6: Natural number version of sum-of-squares bound -/

/-- Cast the sum-of-squares bound to ℕ. -/
theorem ab_deriv_sum_sq_le_nat {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAlmostBent f) (a : F2n n) (ha : a ≠ 0) :
    ∑ b : F2n n, (derivCount f a b) ^ 2 ≤ 2 ^ (n + 1) := by
  have h := ab_deriv_sum_sq_le hn f hf a ha
  have : ∀ b : F2n n, (derivCount f a b : ℤ) ^ 2 = ((derivCount f a b) ^ 2 : ℕ) := by
    intro b; push_cast; ring
  simp only [this] at h
  exact_mod_cast h

/-! ### Main theorem: AB implies APN -/

/-- **AB implies APN**: assembles all the pieces.
    Uses `derivCount_even`, `derivCount_sum`, `ab_deriv_sum_sq_le_nat`,
    and `even_sum_sq_bound`. -/
theorem ab_implies_apn' {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2 := by
  intro a ha b
  have h_even : ∀ b', Even (derivCount f a b') := derivCount_even f a ha
  have h_sum : ∑ b', derivCount f a b' = 2 ^ n := by
    have := derivCount_sum f a
    rwa [F2n.card n hn] at this
  have h_sq : ∑ b', (derivCount f a b') ^ 2 ≤ 2 ^ (n + 1) :=
    ab_deriv_sum_sq_le_nat hn f hf a ha
  exact even_sum_sq_bound hn (derivCount f a) h_even h_sum h_sq b

end
end Kasami