import RequestProject.Foundations.KasamiAxKatzAK3d
import RequestProject.Foundations.KasamiDigitSumComplement
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-10: the McEliece bound on `2`-cyclotomic cosets

This module is a **further from-scratch foundational rung of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on the digit-sum doubling-invariance of `KasamiAxKatzAK3d.lean`
(`binDigitSum_two_pow_mul_mod`) and the complement balance of
`KasamiDigitSumComplement.lean` (`binDigitSum_add_compl`).

The McEliece / Canteaut–Charpin–Dobbertin core of (A) is the digit-sum lower bound
`(n+1)/2 ≤ s₂(e s)`.  This module records two **structural reductions** of that
bound, both Mathlib-close and sorry-free, that constrain exactly what the deep core
must establish:

* **Coset invariance.**  Since the binary digit sum is constant on `2`-cyclotomic
  cosets modulo `2ⁿ − 1` (`binDigitSum_two_pow_mul_mod`), the McEliece bound holds
  for an exponent iff it holds for *every* element of its Frobenius orbit
  `{2^j · s mod (2ⁿ − 1)}`.  So the bound need only be verified on **one
  representative per coset** — the standard reduction underlying the
  cyclotomic-coset formulation of McEliece's theorem.

* **Complement form.**  For `n` *odd* and `a ≤ 2ⁿ − 1`, the complement balance
  `s₂(a) + s₂(2ⁿ − 1 − a) = n` turns the lower bound `(n+1)/2 ≤ s₂(a)` into the
  equivalent upper bound `s₂(2ⁿ − 1 − a) ≤ (n−1)/2` on the complementary exponent
  (the conjugate Gauss-sum index) — the combinatorial shadow of the Gauss-sum
  magnitude relation `g(χ)·g(χ̄) = ±q`.

## Results

* `mcEliece_bound_coset_invariant` — the bound is invariant along a `2`-cyclotomic
  coset.
* `mcEliece_bound_iff_complement` — for `n` odd, the bound is equivalent to the
  complementary upper bound.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure `Nat` digit arithmetic; it
introduces no new hypotheses.  The remaining content — the *value* of the digit sum
itself for the Kasami coset exponents (the McEliece weight congruence), and the
Gross–Koblitz `p`-adic Γ valuation — are the carried cores of (A).

## Sources

McEliece, *Weight congruences for p-ary cyclic codes* (1972); Canteaut–Charpin–
Dobbertin (IEEE-IT 2000); Ireland–Rosen, Ch. 14; Lidl–Niederreiter, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

/-- **Coset invariance of the McEliece bound.**  Because the binary digit sum is
constant on `2`-cyclotomic cosets modulo `2ⁿ − 1`
(`binDigitSum_two_pow_mul_mod`), the lower bound `(n+1)/2 ≤ s₂(·)` holds for the
orbit element `2^j · s` iff it holds for `s` (both reduced modulo `2ⁿ − 1`).  Thus
the McEliece bound need only be checked on one representative per coset. -/
theorem mcEliece_bound_coset_invariant {n : ℕ} (hn : 1 ≤ n) (j s : ℕ) :
    ((n + 1) / 2 ≤ binDigitSum ((2 ^ j * s) % (2 ^ n - 1)))
      ↔ ((n + 1) / 2 ≤ binDigitSum (s % (2 ^ n - 1))) := by
  rw [binDigitSum_two_pow_mul_mod hn]

/-- **Complement form of the McEliece bound.**  For `n` odd and `a ≤ 2ⁿ − 1`, the
complement balance `s₂(a) + s₂(2ⁿ − 1 − a) = n` (`binDigitSum_add_compl`) makes the
McEliece lower bound `(n+1)/2 ≤ s₂(a)` equivalent to the upper bound
`s₂(2ⁿ − 1 − a) ≤ (n−1)/2` on the complementary (conjugate Gauss-sum) exponent. -/
theorem mcEliece_bound_iff_complement {n : ℕ} (hn : Odd n) (a : ℕ) (ha : a ≤ 2 ^ n - 1) :
    ((n + 1) / 2 ≤ binDigitSum a) ↔ (binDigitSum (2 ^ n - 1 - a) ≤ (n - 1) / 2) := by
  have hbal := binDigitSum_add_compl n a ha
  obtain ⟨m, rfl⟩ := hn
  omega

end Vanish.Foundations
