import Mathlib

/-!
# Transcription — Leaf L4, module 0b: the affine counting congruence atom

This is the **next rung above** the finite-field power-sum atom
(`FiniteFieldPowerSum.lean`) in the from-scratch transcription of the iterated
Ax–Katz `2^μ`-divisibility.  Per the foundation-first methodology
(`FoundationFirstMethodology.md`), we isolate and fully prove the *smallest true
statement whose proof needs only Mathlib* before attempting the deep Ax–Katz
inductive step (`AxKatzChevalleyWarning.axKatz_two_pow_dvd_iterated`).

The entry point of Ax's / Warning's counting proof is the **exact affine counting
congruence**: the number `N` of common zeros of a finite polynomial family, cast
into the field `K`, equals the affine sum of the `q`-power indicator
`∏ᵢ (1 - fᵢ(x)^{q-1})`.  This is the identity that turns a *counting* problem into a
*character/power-sum* problem; feeding the expanded product into the monomial
power-sum atom `sum_monomial_whole_field` recovers Chevalley–Warning, and its
`p`-adic refinement is the deep Ax–Katz content one further level up.

Both results below are **real, `sorry`-free, axiom-clean** proofs
(`propext, Classical.choice, Quot.sound`).  They introduce no new definitions,
standing entirely on Mathlib objects, so there is nothing to poison.

## Results

* `prod_qpow_indicator` — for a fixed point `x`, `∏ᵢ (1 - fᵢ(x)^{q-1})` is `1` if `x`
  is a common zero and `0` otherwise (the finite-field `q`-power indicator).
* `card_solutions_eq_affine_sum` — `(N : K) = ∑_{x : σ→K} ∏ᵢ (1 - fᵢ(x)^{q-1})`, the
  exact affine counting congruence.
* `chevalleyWarning_from_atoms` — the **counting proof of Chevalley–Warning**
  assembled from the congruence: when `∑ᵢ deg fᵢ < #σ`, the indicator polynomial
  `∏ᵢ (1 - fᵢ^{q-1})` has total degree `< (q-1)·#σ`, so its affine sum vanishes
  (`MvPolynomial.sum_eval_eq_zero`), forcing `(N : K) = 0`, i.e. `p ∣ N`.

## Sources

* J. Ax, "Zeroes of polynomials over finite fields," *Amer. J. Math.* 86 (1964).
* E. Warning, "Bemerkung zur vorstehenden Arbeit von Herrn Chevalley,"
  *Abh. Math. Sem. Univ. Hamburg* 11 (1935).
* R. Lidl, H. Niederreiter, *Finite Fields*, §6.
* Mathlib: `FiniteField.pow_card_sub_one_eq_one`, `Fintype.card_subtype`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open MvPolynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]

omit [Fintype σ] [DecidableEq σ] in
/-- **The finite-field `q`-power indicator.**  For a family `f : ι → MvPolynomial σ K`
and a point `x : σ → K`, the product `∏ᵢ (1 - fᵢ(x)^{q-1})` equals `1` when `x` is a
common zero of the family and `0` otherwise.  This is the elementary Fermat-style
indicator underlying Ax's counting proof: for `y ≠ 0` in a finite field of order `q`,
`y^{q-1} = 1`, so the factor vanishes, and for `y = 0` the factor is `1`. -/
theorem prod_qpow_indicator (f : ι → MvPolynomial σ K) (x : σ → K) :
    (∏ i, (1 - (MvPolynomial.eval x (f i)) ^ (Fintype.card K - 1)))
      = if (∀ i, MvPolynomial.eval x (f i) = 0) then (1 : K) else 0 := by
  classical
  have hq : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  by_cases h : ∀ i, MvPolynomial.eval x (f i) = 0
  · rw [if_pos h, Finset.prod_eq_one]
    intro i _
    rw [h i, zero_pow hq, sub_zero]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [FiniteField.pow_card_sub_one_eq_one _ hj]
    ring

/-- **The affine counting congruence.**  For a finite family of multivariate
polynomials over a finite field `K` of order `q`, the number of common zeros, cast
into `K`, equals the affine sum of the `q`-power indicator:
`(N : K) = ∑_{x : σ→K} ∏ᵢ (1 - fᵢ(x)^{q-1})`.

This is the exact algebraic entry point of Ax's / Warning's counting proof of
Chevalley–Warning and its Ax–Katz refinement.  Real proof: the indicator
`prod_qpow_indicator` collapses each summand to `1`/`0`, so the affine sum counts
the solutions, and the count is `(N : K)` by `Fintype.card_subtype`. -/
theorem card_solutions_eq_affine_sum (f : ι → MvPolynomial σ K) :
    (Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} : K)
      = ∑ x : σ → K, ∏ i, (1 - (MvPolynomial.eval x (f i)) ^ (Fintype.card K - 1)) := by
  classical
  simp_rw [prod_qpow_indicator]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [nsmul_eq_mul]

/-- **Chevalley–Warning, counting proof from the affine congruence.**  If the total
degrees of the family sum to strictly less than the number of variables, then the
number of common zeros is divisible by the characteristic `p`.  Real proof rooted in
the atoms of this tower: `card_solutions_eq_affine_sum` writes `(N : K)` as the
affine sum of the indicator polynomial `G = ∏ᵢ (1 - fᵢ^{q-1})`, whose total degree is
bounded by `(q-1)·∑ᵢ deg fᵢ < (q-1)·#σ`; `MvPolynomial.sum_eval_eq_zero` (the
degree-`< (q-1)·#σ` affine-sum vanishing, itself the power-sum atom of
`FiniteFieldPowerSum`) then gives `(N : K) = 0`, and `CharP.cast_eq_zero_iff`
converts this to `p ∣ N`.  This is the `μ = 1` base of Ax–Katz obtained *by counting*,
validating that the counting-congruence atom composes as intended; the `p`-adic lift
to general `μ` is the deep Ax–Katz content one level up. -/
theorem chevalleyWarning_from_atoms (p : ℕ) [CharP K p] (f : ι → MvPolynomial σ K)
    (hlt : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} := by
  classical
  set G : MvPolynomial σ K := ∏ i, (1 - (f i) ^ (Fintype.card K - 1)) with hG
  have hdeg : G.totalDegree < (Fintype.card K - 1) * Fintype.card σ := by
    have hfac : ∀ i ∈ Finset.univ,
        (1 - (f i) ^ (Fintype.card K -1)).totalDegree ≤ (Fintype.card K -1) * (f i).totalDegree := by
      intro i _
      calc (1 - (f i) ^ (Fintype.card K -1)).totalDegree
          ≤ max (1 : MvPolynomial σ K).totalDegree ((f i)^(Fintype.card K -1)).totalDegree :=
            MvPolynomial.totalDegree_sub _ _
        _ ≤ (Fintype.card K -1) * (f i).totalDegree := by
            rw [MvPolynomial.totalDegree_one]
            simp only [max_le_iff]
            exact ⟨Nat.zero_le _, MvPolynomial.totalDegree_pow _ _⟩
    have hprod : G.totalDegree ≤ ∑ i, (Fintype.card K -1) * (f i).totalDegree :=
      le_trans (MvPolynomial.totalDegree_finset_prod _ _) (Finset.sum_le_sum hfac)
    rw [← Finset.mul_sum] at hprod
    have hq1 : 0 < Fintype.card K - 1 := by have := Fintype.one_lt_card (α := K); omega
    calc G.totalDegree ≤ (Fintype.card K -1) * ∑ i, (f i).totalDegree := hprod
      _ ≤ (Fintype.card K -1) * (Fintype.card σ - 1) := Nat.mul_le_mul_left _ (by omega)
      _ < (Fintype.card K -1) * Fintype.card σ := (Nat.mul_lt_mul_left hq1).mpr (by omega)
  have hzero : (Nat.card {x : σ → K // ∀ i, MvPolynomial.eval x (f i) = 0} : K) = 0 := by
    rw [card_solutions_eq_affine_sum]
    have hpt : ∀ x : σ → K, (∏ i, (1 - (MvPolynomial.eval x (f i)) ^ (Fintype.card K - 1)))
        = MvPolynomial.eval x G := by
      intro x
      rw [hG, MvPolynomial.eval_prod]
      exact Finset.prod_congr rfl (fun i _ => by rw [map_sub, map_one, map_pow])
    simp_rw [hpt]
    exact MvPolynomial.sum_eval_eq_zero G hdeg
  exact (CharP.cast_eq_zero_iff K p _).mp hzero

end Vanish.Foundations.FirstPrinciples.Transcribe
