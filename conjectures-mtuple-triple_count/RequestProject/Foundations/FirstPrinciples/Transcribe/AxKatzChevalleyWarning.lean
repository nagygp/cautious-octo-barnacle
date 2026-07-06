import Mathlib

/-!
# Transcription — Leaf L4, module 1: Ax–Katz from Chevalley–Warning

This is the **first rung** of the from-scratch transcription of the iterated
Ax–Katz `2^μ`-divisibility `AxKatzDecomp.axKatz_two_pow_dvd` (leaf **L4** in
`FirstPrinciplesTranscriptionRoadmap.md`).

Mathlib already contains the `μ = 1` Chevalley–Warning theorem
(`char_dvd_card_solutions_of_fintype_sum_lt`).  This module:

* proves the **base case** `chevalleyWarning_two_dvd` (char 2, strict-degree form)
  as a **real proof**, repackaged into the `Nat.card`/`{x : σ → K // …}` shape used
  by the project's `AxKatzDecomp.axKatz_two_pow_dvd`;
* proves the trivial `μ = 0` case `axKatz_two_pow_zero`;
* re-states the genuinely deep **iterated** Ax–Katz divisibility as the single
  classical leaf `axKatz_two_pow_dvd_iterated`, faithful to the `AxKatzDecomp`
  statement, with a docstring pointing at the Moreno–Moreno reformulation that is
  the cleanest transcription target.

The remaining work for L4 (modules `AxKatzReduction`, `AxKatzIterated` in the
roadmap) is the inductive/`p`-adic argument that lifts the base case to general
`μ`; that argument is the genuine classical input absent from Mathlib.

## Sources

* J. Ax, "Zeroes of polynomials over finite fields," *Amer. J. Math.* 86 (1964).
* N. Katz, "On a theorem of Ax," *Amer. J. Math.* 93 (1971).
* O. Moreno, C. J. Moreno, "Improvements of the Chevalley–Warning and the Ax–Katz
  theorems," *Amer. J. Math.* 117 (1995).
* Mathlib: `Mathlib/FieldTheory/ChevalleyWarning.lean`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open MvPolynomial

/-- **Chevalley–Warning, char-2, repackaged (the `μ = 1` base case).**  For a finite
family of polynomials over a finite field of characteristic `2` whose total degrees
sum to strictly less than the number of variables, the number of common zeros is
even.  Real proof, specializing Mathlib's `char_dvd_card_solutions_of_fintype_sum_lt`
to `p = 2` and to the `Nat.card` subtype shape used by `AxKatzDecomp`. -/
theorem chevalleyWarning_two_dvd {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K)
    (hlt : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    (2 : ℕ) ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  classical
  have h := char_dvd_card_solutions_of_fintype_sum_lt (K := K) (σ := σ) (p := 2) hlt
  rw [Nat.card_eq_fintype_card]
  simpa using h

/-- **The `μ = 0` case of Ax–Katz is trivial:** `2 ^ 0 = 1` divides everything. -/
theorem axKatz_two_pow_zero {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) :
    (2 : ℕ) ^ 0 ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  simp

/-- **The `μ = 1` case of the iterated statement**, derived from the base case.
With a degree budget `1·d + ∑ deg fᵢ ≤ #σ` and `d ≥ 1` (so the sum is *strictly*
below `#σ`), the number of common zeros is even. -/
theorem axKatz_two_pow_one {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (d : ℕ) (hd1 : 1 ≤ d)
    (hμ : 1 * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ) :
    (2 : ℕ) ^ 1 ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  have hlt : (∑ i, (f i).totalDegree) < Fintype.card σ := by omega
  simpa using chevalleyWarning_two_dvd f hlt

/-- **Iterated Ax–Katz `2^μ`-divisibility (the genuine classical leaf).**  For a
char-2 polynomial system with `μ·d + ∑ deg fᵢ ≤ #σ` and `1 ≤ d`, the number of
common zeros is divisible by `2^μ`.  The base cases `μ ≤ 1` are the real proofs
above; lifting to general `μ` is the Ax–Katz / Moreno–Moreno `p`-adic argument
(absent from Mathlib).  `1 ≤ d` rules out the degenerate `d = 0` regime where the
unbounded statement fails (e.g. `σ` empty, all `fᵢ = 0`). -/
theorem axKatz_two_pow_dvd_iterated {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (d μ : ℕ) (hd1 : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    (hμ : μ * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ) :
    (2 : ℕ) ^ μ ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  sorry

end Vanish.Foundations.FirstPrinciples.Transcribe
