import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzReduction

/-!
# Transcription — Leaf L4, module 3: assembling the iterated Ax–Katz divisibility

This is the **third and final rung** of the iterated Ax–Katz `2^μ`-divisibility
(leaf **L4** in `FirstPrinciplesTranscriptionRoadmap.md`), assembling
`Transcribe/AxKatzChevalleyWarning.lean` (module 1, the `μ = 0/1` base) and
`Transcribe/AxKatzReduction.lean` (module 2, the inductive step
`axKatz_two_pow_dvd_step`).

The assembly is a **real proof** by induction on `μ`:

* `axKatz_two_pow_dvd_forall` — for a fixed char-2 field `K` and degree bound
  `d ≥ 1`, the `2^μ`-divisibility holds for **all** finite variable / index sets and
  all systems of degree bound `d` with budget `μ·d + ∑ deg fᵢ ≤ #σ`.  The base
  `μ = 0` is `2^0 = 1 ∣ _`; the step is module 2's `axKatz_two_pow_dvd_step`, applied
  with the induction hypothesis as its `IH`.
* `axKatz_two_pow_dvd_iterated` — the fixed-variable corollary, matching the shape of
  the `Decomp` leaf `AxKatzDecomp.axKatz_two_pow_dvd` (over `Type`).

The only remaining `sorry` behind these is module 2's single classical step leaf; the
induction here introduces none.

## Sources

* J. Ax, "Zeroes of polynomials over finite fields," *Amer. J. Math.* 86 (1964).
* N. Katz, "On a theorem of Ax," *Amer. J. Math.* 93 (1971).
* O. Moreno, C. J. Moreno, "Improvements of the Chevalley–Warning and the Ax–Katz
  theorems," *Amer. J. Math.* 117 (1995).
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open MvPolynomial

/-- **Iterated Ax–Katz `2^μ`-divisibility, over all finite variable sets (real
induction).**  For a fixed char-2 field `K` and degree bound `d ≥ 1`, the
`2^μ`-divisibility of the common-zero count holds for every finite variable set `σ`,
index set `ι`, and system `f` of degree bound `d` with budget
`μ·d + ∑ deg fᵢ ≤ #σ`.  Proved by induction on `μ`: the base `μ = 0` is `1 ∣ _`, and
the step is the module-2 reduction `axKatz_two_pow_dvd_step`. -/
theorem axKatz_two_pow_dvd_forall {K : Type} [Field K] [Fintype K] [CharP K 2]
    (d : ℕ) (hd1 : 1 ≤ d) (μ : ℕ) :
    ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (f : ι → MvPolynomial σ K),
        (∀ i, (f i).totalDegree ≤ d) →
        μ * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ →
        (2 : ℕ) ^ μ ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  induction μ with
  | zero => intro σ ι _ _ f _ _; simp
  | succ m ih => exact axKatz_two_pow_dvd_step d m hd1 ih

/-- **Iterated Ax–Katz `2^μ`-divisibility, fixed-variable form (real proof).**  For a
char-2 polynomial system with `μ·d + ∑ deg fᵢ ≤ #σ`, degree bound `d ≥ 1`, the number
of common zeros is divisible by `2^μ`.  This matches the shape of the `Decomp` leaf
`AxKatzDecomp.axKatz_two_pow_dvd` (over `Type`); it is a direct specialization of
`axKatz_two_pow_dvd_forall`.  (Named with a prime to avoid the module-1 leaf
`axKatz_two_pow_dvd_iterated`, which carries the same statement over arbitrary
universes as an isolated `sorry`; this version, over `Type`, is `sorry`-free modulo
the module-2 reduction leaf.) -/
theorem axKatz_two_pow_dvd_iterated' {K : Type} [Field K] [Fintype K] [CharP K 2]
    {σ ι : Type} [Fintype σ] [Fintype ι] (f : ι → MvPolynomial σ K) (d μ : ℕ)
    (hd1 : 1 ≤ d) (hd : ∀ i, (f i).totalDegree ≤ d)
    (hμ : μ * d + ∑ i, (f i).totalDegree ≤ Fintype.card σ) :
    (2 : ℕ) ^ μ ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} :=
  axKatz_two_pow_dvd_forall d hd1 μ σ ι f hd hμ

end Vanish.Foundations.FirstPrinciples.Transcribe
