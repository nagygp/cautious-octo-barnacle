/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import Mathlib

/-!
# Krawtchouk polynomials

> Intended Mathlib target path:
> `Mathlib/Combinatorics/Krawtchouk.lean` (or alongside the coding-theory layer at
> `Mathlib/InformationTheory/Krawtchouk.lean`, since they are the transform kernel
> for the MacWilliams identity).
>
> For the actual pull request the blanket `import Mathlib` pulled in transitively
> should be minimised (e.g. with `shake`) to the relevant modules.

This file introduces the **Krawtchouk polynomials** `K_k(x; n, q)`, the discrete
orthogonal polynomials underlying the additive-character / Fourier transform that
turns a weight enumerator into its dual (MacWilliams–Sloane, *The Theory of
Error-Correcting Codes*, Ch. 5, §2).  For nonnegative integers `n, q, k` and an
integer evaluation point `x`,

`K_k(x; n, q) = Σ_{j=0}^{k} (-1)^j (q-1)^{k-j} C(x, j) C(n-x, k-j)`.

Their single most important property — and the bridge to the MacWilliams
identity — is the **generating function**

`Σ_k K_k(x) z^k = (1 + (q-1) z)^{n-x} (1 - z)^x`,

obtained by reading off the coefficient of `z^k` in the product of the two
binomial expansions.

## Main definitions

* `LinearCode.krawtchouk q n k x` — the value `K_k(x; n, q) : ℤ`.

## Main results

* `LinearCode.krawtchouk_zero` — `K_0(x) = 1`.
* `LinearCode.krawtchouk_eval_zero` — `K_k(0) = C(n, k) (q-1)^k`.
* `LinearCode.krawtchouk_eq_zero_of_lt` — `K_k(x) = 0` for `k > n` (with `x ≤ n`).
* `LinearCode.coeff_linear_pow` — the coefficient of a power of a linear
  polynomial, `((C b + C a · X)^m).coeff k = C(m, k) a^k b^{m-k}`.
* `LinearCode.krawtchouk_eq_coeff` — `K_k(x)` is the `k`-th coefficient of
  `(1 + (q-1) X)^{n-x} (1 - X)^x`.
* `LinearCode.krawtchouk_generating_function` —
  `Σ_{k=0}^{n} K_k(x) X^k = (1 + (q-1) X)^{n-x} (1 - X)^x`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 5.)

## Tags

Krawtchouk polynomial, coding theory, MacWilliams identity, weight enumerator
-/

open Finset Polynomial

namespace LinearCode

/-- The `k`-th **Krawtchouk polynomial** evaluated at `x`, with parameters `n`
(length) and `q` (alphabet size):
`K_k(x; n, q) = Σ_{j=0}^{k} (-1)^j (q-1)^{k-j} C(x, j) C(n-x, k-j)`. -/
def krawtchouk (q n k x : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1) ^ j * ((q : ℤ) - 1) ^ (k - j) *
      (x.choose j : ℤ) * ((n - x).choose (k - j) : ℤ)

/-- `K_0(x) = 1`. -/
theorem krawtchouk_zero (q n x : ℕ) : krawtchouk q n 0 x = 1 := by
  simp [krawtchouk]

/-- `K_k(0) = C(n, k) (q-1)^k`. -/
theorem krawtchouk_eval_zero (q n k : ℕ) :
    krawtchouk q n k 0 = (n.choose k : ℤ) * ((q : ℤ) - 1) ^ k := by
  unfold krawtchouk
  simp +decide [Finset.sum_range_succ', mul_comm]

/-- The coefficient of a power of a linear polynomial:
`((C b + C a · X)^m).coeff k = C(m, k) a^k b^{m-k}`. -/
theorem coeff_linear_pow (a b : ℤ) (m k : ℕ) :
    ((Polynomial.C b + Polynomial.C a * Polynomial.X) ^ m).coeff k =
      (m.choose k : ℤ) * a ^ k * b ^ (m - k) := by
  by_cases h : k ≤ m <;> simp_all +decide [Polynomial.coeff_eq_zero_of_natDegree_lt]
  · rw [add_comm, add_pow]
    simp +decide [mul_pow, mul_assoc, mul_comm, mul_left_comm, Polynomial.coeff_mul]
    simp +decide [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Polynomial.coeff_eq_zero_of_natDegree_lt]
    simp +decide [Finset.sum_range_succ', Polynomial.coeff_eq_zero_of_natDegree_lt]
    norm_num [Polynomial.coeff_zero_eq_eval_zero, h]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp +decide [Nat.choose_eq_zero_of_lt h]
    · refine lt_of_le_of_lt ?_ h
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
        simp +decide [ha, hb, Polynomial.natDegree_add_eq_right_of_natDegree_lt]

/-- **The Krawtchouk value as a polynomial coefficient.** `K_k(x)` is the `k`-th
coefficient of the product of binomial expansions
`(1 + (q-1) X)^{n-x} (1 - X)^x`. -/
theorem krawtchouk_eq_coeff (q n k x : ℕ) :
    (krawtchouk q n k x : ℤ) =
      (((1 + ((q : ℤ) - 1) • Polynomial.X) ^ (n - x) *
          (1 - Polynomial.X) ^ x : Polynomial ℤ)).coeff k := by
  rw [Polynomial.coeff_mul]
  convert Finset.sum_congr rfl fun j hj => ?_ using 2
  rotate_left
  use fun j => (Polynomial.coeff ((1 + (q - 1 : ℤ) • X) ^ (n - x)) (k - j)) *
    (Polynomial.coeff ((1 - X) ^ x) j)
  · rw [show (1 - X : Polynomial ℤ) ^ x = (Polynomial.C 1 + Polynomial.C (-1) * Polynomial.X) ^ x by
        simp +decide [sub_eq_add_neg],
      show (1 + (q - 1 : ℤ) • X : Polynomial ℤ) ^ (n - x)
          = (Polynomial.C 1 + Polynomial.C (q - 1 : ℤ) * Polynomial.X) ^ (n - x) by
        simp +decide [Polynomial.smul_eq_C_mul]]
    rw [coeff_linear_pow, coeff_linear_pow]; norm_num; ring
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_flip]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hi)]

/-- `K_k(x) = 0` whenever `k > n` (for an evaluation point `x ≤ n`): the product
`(1 + (q-1) X)^{n-x} (1 - X)^x` has degree at most `n`. -/
theorem krawtchouk_eq_zero_of_lt (q n k x : ℕ) (hx : x ≤ n) (hk : n < k) :
    krawtchouk q n k x = 0 := by
  by_contra h_contra
  convert krawtchouk_eq_coeff q n k x |> fun h => h.symm ▸ Polynomial.coeff_eq_zero_of_natDegree_lt _
  · aesop
  · refine lt_of_le_of_lt (Polynomial.natDegree_mul_le ..) ?_
    refine lt_of_le_of_lt ?_ hk
    refine le_trans (add_le_add (Polynomial.natDegree_pow_le) (Polynomial.natDegree_pow_le)) ?_
    norm_num [Polynomial.smul_eq_C_mul]
    erw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> norm_num
    · erw [Polynomial.natDegree_mul'] <;> norm_num [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
      · erw [Polynomial.natDegree_sub_C]; norm_num; linarith [Nat.sub_add_cancel hx]
      · rcases q with (_ | _ | q) <;> norm_num at *
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt] at h <;> norm_num at *
          · contradiction
          · erw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;> norm_num; linarith
        · norm_cast
    · by_cases hq : q = 1 <;> simp_all +decide [Polynomial.smul_eq_C_mul]
      · exact h_contra <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by
          erw [Polynomial.natDegree_pow, Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;>
            norm_num; linarith
      · rw [Polynomial.natDegree_mul'] <;>
          norm_num [Polynomial.natDegree_sub_eq_right_of_natDegree_lt, hq]
        exact sub_ne_zero_of_ne (mod_cast hq)

/-- **The Krawtchouk generating function** (MacWilliams–Sloane, Ch. 5, §2):
`Σ_{k=0}^{n} K_k(x) X^k = (1 + (q-1) X)^{n-x} (1 - X)^x`.
This is the identity that turns the weight enumerator into its MacWilliams dual. -/
theorem krawtchouk_generating_function (q n x : ℕ) (hx : x ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (krawtchouk q n k x) * Polynomial.X ^ k =
      (1 + ((q : ℤ) - 1) • Polynomial.X) ^ (n - x) *
        (1 - Polynomial.X) ^ x := by
  convert Polynomial.as_sum_range' _ (n + 1) _ |> Eq.symm using 1
  · simp +decide [← Polynomial.C_mul_X_pow_eq_monomial, krawtchouk_eq_coeff q n _ x]
  · refine lt_of_le_of_lt (Polynomial.natDegree_mul_le ..) ?_; norm_num
    rcases q with (_ | _ | q) <;>
      norm_num [Polynomial.natDegree_add_eq_right_of_natDegree_lt,
        Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · rw [Nat.sub_add_cancel hx]
    · linarith
    · erw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> norm_num
      · erw [Polynomial.natDegree_mul'] <;> norm_num
        · erw [Polynomial.natDegree_add_C]; norm_num; linarith [Nat.sub_add_cancel hx]
        · norm_cast
      · erw [Polynomial.natDegree_mul_X] <;> norm_cast; norm_num

end LinearCode
