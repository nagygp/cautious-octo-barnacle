import Mathlib

/-!
# Foundations, Layer AK1 — the Ax–Katz / McEliece weight-divisibility route, base layer

This module implements the **first layer of the Ax–Katz / McEliece sub-path for
input (A)** laid out in `Docs/VanishFutureDirections.md` §6.

Input **(A)** is the weight divisibility `2^{(n+1)/2} ∣ R(s)` of the Kasami
cross-correlation.  The project already discharges it *unconditionally for the
quadratic Kasami exponents* `k ≤ 2` through the radical/valuation route of Layers
A1–A2 (`QuadraticGaussSum.lean`, `KasamiTwoAdicValuation.lean`).  For the
genuinely non-quadratic exponents `k ≥ 3` the derivative form has algebraic degree
`> 2`, so the radical route no longer applies and `(A)` becomes the
**Ax–Katz / McEliece weight-divisibility theorem** — a `2`-adic estimate of a
character / solution-count sum.

This module transcribes the **two elementary foundations** on which that theorem
rests, both provable from Mathlib (no new axioms):

## 1. The base divisibility — Chevalley–Warning in characteristic 2

The bottom of the Ax–Katz tower is the **Chevalley–Warning theorem**: for a
finite family of multivariate polynomials over a finite field of characteristic
`p` whose total degrees sum to less than the number of variables, the number of
common zeros is divisible by `p`.  Ax–Katz strengthens the divisor `p` to
`p^μ` with `μ = ⌈(N − ∑ dᵢ)/max dᵢ⌉`.  Mathlib has Chevalley–Warning
(`char_dvd_card_solutions_of_sum_lt`); here we record its characteristic-2
specialization `charTwo_two_dvd_card_solutions`, the `μ = 1` base case of the
divisibility tower (Ax 1964; McEliece 1972).

## 2. The combinatorial engine — base-2 digit sums (Legendre / Kummer)

The Ax–Katz exponent and the McEliece weight congruences are governed by the
**base-`p` digit-sum function** through Stickelberger's congruence for Gauss
sums.  In characteristic 2 the relevant facts are Legendre's formula
`v₂(n!) = n − s₂(n)` and Kummer's theorem
`v₂(C(n,k)) = s₂(k) + s₂(n−k) − s₂(n)`, where `s₂(n) = (Nat.digits 2 n).sum`
is the binary digit sum (= number of `1`-bits of `n`).  These are the elementary
inputs from which the Stickelberger/McEliece `2`-adic valuation bound is built.
Mathlib provides them via `sub_one_mul_padicValNat_factorial` and
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits`; here we specialize to `p = 2`
(where `p − 1 = 1`), giving the clean valuation identities directly.

## Scope

This layer is sorry-free and supplies the two elementary foundations of the
Ax–Katz/McEliece route.  The route's *deep* steps — the Stickelberger congruence
for Gauss sums, the full Ax–Katz `p^μ`-divisibility, and the
Canteaut–Charpin–Dobbertin specialization to the Kasami exponent `d k` — are the
later layers of the sub-path (AK2–AK4 in §6); they remain open and are
deliberately not axiomatized.

## Sources

Ax, *Zeroes of polynomials over finite fields* (Amer. J. Math., 1964);
Katz, *On a theorem of Ax* (1971); McEliece, *Weight congruences for p-ary cyclic
codes* (Discrete Math., 1972); Canteaut–Charpin–Dobbertin, *Weight divisibility
of cyclic codes …* (SIAM J. Discrete Math., 2000); Lidl–Niederreiter,
*Finite Fields*, Ch. 6 (digit sums and Gauss-sum valuations).
-/

namespace Vanish.Foundations

open Finset BigOperators MvPolynomial

/-! ## 1. The base divisibility — Chevalley–Warning in characteristic 2 -/

/-
**Chevalley–Warning in characteristic 2 (the Ax–Katz base case).**  For a
finite family `f : ι → MvPolynomial σ K` over a finite field `K` of
characteristic `2`, if the sum of the total degrees of the `f i` (over `i ∈ s`)
is strictly less than the number of variables `#σ`, then the number of common
zeros is **even**.  This is the `μ = 1` base of the Ax–Katz divisibility tower:
Ax–Katz strengthens `2 ∣ N` to `2^μ ∣ N`.
-/
theorem charTwo_two_dvd_card_solutions
    {σ ι K : Type*} [Fintype σ] [DecidableEq σ] [Fintype K] [Field K]
    [DecidableEq K] [CharP K 2] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    2 ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } :=
  char_dvd_card_solutions_of_sum_lt 2 h

/-! ## 2. The combinatorial engine — base-2 digit sums (Legendre / Kummer) -/

/-- The **binary digit sum** `s₂(n) = (Nat.digits 2 n).sum`, i.e. the number of
`1`-bits in the base-`2` expansion of `n`.  This is the combinatorial quantity
governing the `2`-adic valuations in the Stickelberger / McEliece estimates. -/
def binDigitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/--
**Legendre's formula in base 2.**  The `2`-adic valuation of `n!` is
`n − s₂(n)`.  (Since `p − 1 = 1` at `p = 2`, the general Legendre formula
`(p−1)·v_p(n!) = n − s_p(n)` collapses to this identity.)
-/
theorem padicValNat_two_factorial (n : ℕ) :
    padicValNat 2 (Nat.factorial n) = n - binDigitSum n := by
  have h := @sub_one_mul_padicValNat_factorial 2;
  simpa [ binDigitSum ] using h n

/--
**Kummer's theorem in base 2.**  For `k ≤ n`, the `2`-adic valuation of the
binomial coefficient `C(n, k)` is `s₂(k) + s₂(n−k) − s₂(n)`, i.e. the number of
carries when adding `k` and `n − k` in base `2`.  (Again `p − 1 = 1` at `p = 2`.)
-/
theorem padicValNat_two_choose {k n : ℕ} (h : k ≤ n) :
    padicValNat 2 (n.choose k) = binDigitSum k + binDigitSum (n - k) - binDigitSum n := by
  convert sub_one_mul_padicValNat_choose_eq_sub_sum_digits ( p := 2 ) h using 1;
  norm_num

end Vanish.Foundations