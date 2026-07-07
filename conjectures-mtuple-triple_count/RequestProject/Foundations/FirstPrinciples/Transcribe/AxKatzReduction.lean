import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzChevalleyWarning

/-!
# Transcription — Leaf L4, module 2: the Ax–Katz inductive reduction step

This is the **second rung** of the iterated Ax–Katz `2^μ`-divisibility (leaf **L4**
in `FirstPrinciplesTranscriptionRoadmap.md`), continuing
`Transcribe/AxKatzChevalleyWarning.lean` (module 1, the `μ ≤ 1` base from
Chevalley–Warning).

It isolates the genuine deep classical input of Ax–Katz as a **single reduction
lemma** `axKatz_two_pow_dvd_step`: the `μ → μ+1` inductive step.  Following
Ax (1964) / Katz (1971) in the Moreno–Moreno (1995) reformulation, the step is
phrased so that the assembly (module 3, `AxKatzIterated`) is a clean induction on
`μ`: given the whole `2^μ`-divisibility statement for **all** char-2 systems of
degree bound `d` (the induction hypothesis `IH`, quantified over all finite variable
/ index sets), the `2^{μ+1}`-divisibility follows for any system with the tighter
budget `(μ+1)·d + ∑ deg fᵢ ≤ #σ`.

Classically the step passes to an auxiliary polynomial system (over the same field,
with the degree budget lowered by `d`) whose common-zero count is congruent, modulo
`2^{μ+1}`, to a `2·`(count of the original system); the `μ`-level divisibility for
that auxiliary system then yields the `μ+1` level for the original.  This auxiliary
construction is the classical Ax–Katz content absent from Mathlib; it is carried
here as the single `sorry` leaf, faithful to the statement so module 3's induction
is a real proof.

## Sources

* J. Ax, "Zeroes of polynomials over finite fields," *Amer. J. Math.* 86 (1964).
* N. Katz, "On a theorem of Ax," *Amer. J. Math.* 93 (1971).
* O. Moreno, C. J. Moreno, "Improvements of the Chevalley–Warning and the Ax–Katz
  theorems," *Amer. J. Math.* 117 (1995).
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open MvPolynomial

/-
**The Ax–Katz inductive step (the genuine classical leaf).**  Fix a finite field
`K` of characteristic `2` and a degree bound `d ≥ 1`.  Suppose the `2^m`-divisibility
of the common-zero count holds for **every** char-2 polynomial system of degree
bound `d` with budget `m·d + ∑ deg fᵢ ≤ #variables` (the induction hypothesis `IH`,
quantified over all finite variable and index sets).  Then, for any system with the
tighter budget `(m+1)·d + ∑ deg fᵢ ≤ #variables`, the common-zero count is divisible
by `2^{m+1}`.  This single reduction — the Ax / Katz / Moreno–Moreno auxiliary-system
argument — is the deep leaf of L4; module 3 assembles it into the full iterated
theorem by induction on `μ`.
-/
theorem axKatz_two_pow_dvd_step {K : Type} [Field K] [Fintype K] [CharP K 2]
    (d m : ℕ) (hd1 : 1 ≤ d)
    (IH : ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (f : ι → MvPolynomial σ K),
        (∀ i, (f i).totalDegree ≤ d) →
        m * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ →
        (2 : ℕ) ^ m ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0}) :
    ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (f : ι → MvPolynomial σ K),
        (∀ i, (f i).totalDegree ≤ d) →
        (m + 1) * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ →
        (2 : ℕ) ^ (m + 1) ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  sorry

end Vanish.Foundations.FirstPrinciples.Transcribe