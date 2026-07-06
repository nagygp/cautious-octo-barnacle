import RequestProject.Foundations.KasamiEq12Average
import RequestProject.Foundations.KasamiEvenMCubing
import Mathlib

/-!
# Foundations — DD eq. (12): pinning the GF(4)*-coset-average value set

This module **transcribes the next step of the Dillon–Dobbertin equation-(12)
route**: combining the equation-(12) realization
`3·R(s) = ∑_{μ ∈ GF(4)*} Q̂^λ_{aμ}(0)`
(`three_mul_kasamiWalsh_terms_spectrum`, the GF(4)*-coset average) with the **rank
evaluation** of each term to *pin the value set*.

The GF(4)* index set `{μ : μ³ = 1}` has exactly three elements
(`card_cubeRootsOne`, for `n` even), and the rank evaluation pins each
quadratic-form Gauss sum `Q̂^λ_{aμ}(0)` to `{0, ±A}` with `A = 2^{(n+1)/2}`
(rank `n−1`).  Therefore the coset-average sum `3·R(s)` is a sum of three terms
each in `{0, ±A}`, so it lies in the discrete set `{ j·A : −3 ≤ j ≤ 3 }`
(`gf4_cosetAverage_value`, `eq12_three_mul_value`).  Dividing by `3` (the literal
`1/3` of equation (12)) then pins `R(s)` itself, completing the value-set
derivation through the DD route.

## Scope

The combinatorial value-set pinning (`gf4_cosetAverage_value`) and its eq.(12)
specialization (`eq12_three_mul_value`) are sorry-free.  The equation-(12) field
substitution `x = u^{2^k+1}` realizing the average (the hypothesis `h12`) and the
rank evaluation pinning each term to `{0, ±A}` (the hypothesis `hrank`) remain the
deep cores, carried as named hypotheses rather than axioms or `sorry`.

## Sources

Dillon–Dobbertin (FFA 2004), §7 (eq. (12)) and Appendix A.4.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The coset-average value set (general combinatorial lemma) -/

/-
**Sum of three `{0, ±A}` terms lies in `{ j·A : −3 ≤ j ≤ 3 }`.**  If each term
of a sum over a three-element index set is `0`, `A`, or `−A`, then the sum is an
integer multiple `j·A` of `A` with `|j| ≤ 3`.  This is the abstract form of the
GF(4)*-coset-average value set produced by equation (12) after the rank
evaluation.
-/
theorem gf4_cosetAverage_value {ι : Type*} (S : Finset ι) (hcard : S.card = 3)
    (A : ℤ) (g : ι → ℤ)
    (hmem : ∀ μ ∈ S, g μ = 0 ∨ g μ = A ∨ g μ = -A) :
    ∃ j : ℤ, -3 ≤ j ∧ j ≤ 3 ∧ ∑ μ ∈ S, g μ = j * A := by
  by_contra h_contra;
  push_neg at h_contra;
  specialize h_contra ( ( ∑ μ ∈ S, g μ ) / A ) ?_ ?_ ?_ <;> rcases eq_or_ne A 0 with rfl | hA <;> simp_all +decide;
  · have h_sum_bound : |∑ μ ∈ S, g μ| ≤ 3 * |A| := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun x hx => show |g x| ≤ |A| by rcases hmem x hx with ( h | h | h ) <;> simp +decide [ h ] ) ( by simp +decide [ hcard ] ) );
    cases abs_cases A <;> cases abs_cases ( ∑ μ ∈ S, g μ ) <;> cases lt_or_gt_of_ne hA <;> nlinarith [ Int.mul_ediv_add_emod ( ∑ μ ∈ S, g μ ) A, Int.emod_nonneg ( ∑ μ ∈ S, g μ ) hA, Int.emod_lt_abs ( ∑ μ ∈ S, g μ ) hA ];
  · have h_sum_bound : |∑ μ ∈ S, g μ| ≤ 3 * |A| := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun x hx => show |g x| ≤ |A| by rcases hmem x hx with ( h | h | h ) <;> simp +decide [ h ] ) ( by simp +decide [ hcard ] ) );
    cases abs_cases ( ∑ μ ∈ S, g μ ) <;> cases abs_cases A <;> cases lt_or_gt_of_ne hA <;> nlinarith [ Int.mul_ediv_add_emod ( ∑ μ ∈ S, g μ ) A, Int.emod_nonneg ( ∑ μ ∈ S, g μ ) hA, Int.emod_lt_abs ( ∑ μ ∈ S, g μ ) hA ];
  · rw [ Int.ediv_mul_cancel ];
    exact Finset.dvd_sum fun x hx => by rcases hmem x hx with ( h | h | h ) <;> simp +decide [ h ] ;

/-! ## 2. The equation-(12) specialization -/

section CharTwo

variable [CharP F 2]

/-- **Equation (12): the coset-average value set.**  Given the equation-(12)
realization `h12` (`3·R(s) = ∑_{μ ∈ GF(4)*} Q̂^λ_{aμ}(0)`) and the rank evaluation
`hrank` pinning each term to `{0, ±A}` with `A = 2^{(n+1)/2}`, the coset average
`3·R(s)` lies in `{ j·A : −3 ≤ j ≤ 3 }`.  Combined with the `1/3` of equation (12)
this pins `R(s)` to the Kasami value set. -/
theorem eq12_three_mul_value {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (k : ℕ) (lam a : F) (W : ℤ)
    (h12 : 3 * W = ∑ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
      quadGaussSum (fun x : F =>
        lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)))
    (hrank : ∀ μ ∈ univ.filter (fun g : Fˣ => g ^ 3 = 1),
        quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1)) = 0
        ∨ quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))
              = 2 ^ ((n + 1) / 2)
        ∨ quadGaussSum (fun x : F =>
            lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))
              = -2 ^ ((n + 1) / 2)) :
    ∃ j : ℤ, -3 ≤ j ∧ j ≤ 3 ∧ 3 * W = j * 2 ^ ((n + 1) / 2) := by
  have hcard3 : (univ.filter (fun g : Fˣ => g ^ 3 = 1)).card = 3 :=
    Vanish.Foundations.card_cubeRootsOne hcard hn
  obtain ⟨j, hj1, hj2, hj3⟩ :=
    gf4_cosetAverage_value (univ.filter (fun g : Fˣ => g ^ 3 = 1)) hcard3
      (2 ^ ((n + 1) / 2))
      (fun μ => quadGaussSum (fun x : F =>
        lam * x ^ (2 ^ (3 * k) + 1) + (a * (μ : F)) * x ^ (2 ^ k + 1))) hrank
  exact ⟨j, hj1, hj2, by rw [h12, hj3]⟩

end CharTwo

end Vanish.Foundations