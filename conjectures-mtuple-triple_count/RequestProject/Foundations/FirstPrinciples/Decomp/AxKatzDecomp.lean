import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.KasamiAxKatz
import RequestProject.Foundations.KasamiAxKatzAK2
import Mathlib

/-!
# Decomposition library — Core (A·fp·s4): Ax–Katz / McEliece divisibility, bottom-up

This module **expands the deep core** `FPMcEliece` (`axKatz_two_pow_dvd`,
`kasami_exp_factorial_bound` (`hfact`), `kasami_exp_ge` (`hle`)) into a bottom-up
skeleton.  The McEliece specializations are reduced to a **single number-theoretic
leaf** — the digit-sum lower bound `binDigitSum(e(s)) ≥ (n+1)/2` — plus elementary
arithmetic (Legendre's base-2 formula `padicValNat_two_factorial`, already proven,
and `binDigitSum_le_self`).  The digit-sum bound is the output of the iterated
Ax–Katz divisibility (the genuine classical leaf), specialized to the Kasami/BCH
code system.

## The chain

* `axKatz_two_pow_dvd` — the iterated `2^μ`-divisibility (the classical Ax–Katz
  theorem absent from Mathlib).  Its `μ ≤ 1` base cases are real (`charTwo_…`).
* `kasami_exp_digitSum_lower_bound` — the McEliece/Ax-Katz output leaf:
  `binDigitSum(e(s)) ≥ (n+1)/2` for non-trivial frequencies.
* `kasami_exp_ge` — **real proof** from the digit-sum bound and the project's
  `Vanish.Foundations.binDigitSum_le_self`.
* `kasami_exp_factorial_bound` — **real proof** from the digit-sum bound and
  Legendre's base-2 factorial formula `padicValNat_two_factorial`.

## Sources

Ax (1964); Katz (1971); McEliece (1972); Canteaut–Charpin–Dobbertin (SIAM 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

/-- **Iterated Ax–Katz `2^μ`-divisibility (the classical leaf).**  For a finite
char-2 polynomial system with `μ·d + ∑ deg fᵢ ≤ #variables`, the number of common
zeros is divisible by `2^μ`.  The `μ = 1` case is the project's proved
`charTwo_two_dvd_card_solutions`; the iterated statement is the deep Ax–Katz input. -/
theorem axKatz_two_pow_dvd {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (d μ : ℕ) (hd1 : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    (hμ : μ * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ) :
    (2 : ℕ) ^ μ ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  sorry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The McEliece/Ax–Katz digit-sum lower bound (the specialization leaf).**  For a
non-trivial Kasami frequency, the binary digit sum of the Teichmüller exponent is at
least `(n+1)/2`.  This is the output of `axKatz_two_pow_dvd` applied to the dual
Kasami/BCH code system (the McEliece weight-congruence). -/
theorem kasami_exp_digitSum_lower_bound {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (kasamiExp k a s) := by
  sorry

/-- **The exponent size condition (`hle`), assembled.**  From the digit-sum bound and
`binDigitSum_le_self`, the Teichmüller exponent is at least `(n+1)/2`.  Real wiring. -/
theorem kasami_exp_ge {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ kasamiExp k a s := by
  intro s hs
  exact le_trans (kasami_exp_digitSum_lower_bound hcard hk hkn hcop hnodd a ha s hs)
    (Vanish.Foundations.binDigitSum_le_self _)

/-- **The McEliece factorial-valuation bound (`hfact`), assembled.**  From the
digit-sum bound and Legendre's base-2 formula `v₂(m!) = m − s₂(m)`
(`padicValNat_two_factorial`), the factorial valuation satisfies
`v₂((e s)!) ≤ e s − (n+1)/2`.  Real wiring. -/
theorem kasami_exp_factorial_bound {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValNat 2 (Nat.factorial (kasamiExp k a s)) ≤ kasamiExp k a s - (n + 1) / 2 := by
  intro s hs
  rw [padicValNat_two_factorial]
  have hdig := kasami_exp_digitSum_lower_bound hcard hk hkn hcop hnodd a ha s hs
  omega

end Vanish.Foundations.FirstPrinciples.Decomp