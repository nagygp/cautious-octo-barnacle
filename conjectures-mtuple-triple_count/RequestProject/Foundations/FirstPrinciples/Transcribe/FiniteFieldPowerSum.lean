import Mathlib

/-!
# Transcription — Leaf L4, module 0: the finite-field power-sum atom

This is the **bottom rung** (the leaf nearest to Mathlib) of the from-scratch
transcription of the iterated Ax–Katz `2^μ`-divisibility.  Per the foundation-first
methodology (`FoundationFirstMethodology.md`), before attempting the deep Ax–Katz
inductive step (`AxKatzChevalleyWarning.axKatz_two_pow_dvd_iterated`) we isolate and
fully prove the *smallest true statement whose proof needs only Mathlib*.

The combinatorial heart of Ax's counting proof is the **power sum of a finite field**:
for the additive count of common zeros, one expands the `q`-power indicator
`1 - g(x)^{q-1}` into monomials and uses that a monomial `∏ⱼ xⱼ^{uⱼ}` sums, over the
whole affine space, to `0` unless every exponent `uⱼ` is a *positive* multiple of
`q-1`.  Mathlib supplies the sum over the multiplicative group
(`FiniteField.sum_pow_units`); this module lifts it to the *whole field* (including
`0`) and to *monomials over any finite index set*.  Both results are proved as **real,
`sorry`-free, axiom-clean** proofs.

Everything above this leaf in the Ax–Katz subtree (the `q`-power indicator expansion,
the degree/weight budget bookkeeping, and the `p`-adic inductive lift) consumes these
two lemmas; per the methodology we do not attempt those until this leaf is green.

## Results

* `sum_pow_whole_field` — `∑_{x∈K} xᵘ = -1` if `(q-1) ∣ u` and `u ≠ 0`, else `0`.
* `sum_monomial_whole_field` — `∑_{x : σ→K} ∏ⱼ xⱼ^{uⱼ}` is `(-1)^{#σ}` if every
  `uⱼ` is a positive multiple of `q-1`, and `0` otherwise.

## Sources

* J. Ax, "Zeroes of polynomials over finite fields," *Amer. J. Math.* 86 (1964).
* R. Lidl, H. Niederreiter, *Finite Fields*, §6 (character/power sums).
* Mathlib: `FiniteField.sum_pow_units`, `Finset.prod_univ_sum`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset

/-- **Power sum over the whole finite field.**  For a finite field `K` of cardinality
`q` and an exponent `u`, `∑_{x∈K} xᵘ = -1` when `(q-1) ∣ u` and `u ≠ 0`, and `0`
otherwise (in particular for `u = 0`, since `0⁰ = 1` contributes `1` and the units
contribute `q-1 = -1`).  Real proof, lifting `FiniteField.sum_pow_units` from the
unit group to the whole field by splitting off `x = 0`. -/
theorem sum_pow_whole_field (K : Type*) [Field K] [Fintype K] [DecidableEq K] (u : ℕ) :
    ∑ x : K, x ^ u = if (Fintype.card K - 1 ∣ u ∧ u ≠ 0) then -1 else 0 := by
  classical
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    simp only [pow_zero, sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [if_neg (by simp)]
    exact_mod_cast FiniteField.cast_card_eq_zero K
  · have hsplit : ∑ x : K, x ^ u = ∑ x : Kˣ, (x : K) ^ u := by
      rw [← Finset.sum_subset (Finset.subset_univ ((univ : Finset Kˣ).image (Units.val)))]
      · rw [Finset.sum_image]; exact fun x _ y _ h => Units.ext h
      · intro x _ hx
        simp only [mem_image, mem_univ, true_and, not_exists] at hx
        have hx0 : x = 0 := by by_contra h; exact hx (Units.mk0 x h) rfl
        rw [hx0, zero_pow hu]
    rw [hsplit, FiniteField.sum_pow_units K u]
    by_cases h : Fintype.card K - 1 ∣ u <;> simp [h, hu]

/-- **Power sum of a monomial over affine space.**  For a finite field `K` of
cardinality `q`, a finite index set `σ`, and an exponent vector `u : σ → ℕ`,
`∑_{x : σ→K} ∏ⱼ xⱼ^{uⱼ} = (-1)^{#σ}` when every `uⱼ` is a positive multiple of
`q-1`, and `0` otherwise.  This is the exact monomial-summation fact used in the
counting proof of Chevalley–Warning / Ax–Katz.  Real proof, factoring the affine
sum into a product of whole-field power sums via `Finset.prod_univ_sum`. -/
theorem sum_monomial_whole_field (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] [DecidableEq σ] (u : σ → ℕ) :
    (∑ x : σ → K, ∏ j, x j ^ u j)
      = if (∀ j, Fintype.card K - 1 ∣ u j ∧ u j ≠ 0) then (-1 : K) ^ Fintype.card σ else 0 := by
  classical
  have h1 : (∑ x : σ → K, ∏ j, x j ^ u j) = ∏ j, ∑ y : K, y ^ u j := by
    rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]
  rw [h1]
  simp_rw [sum_pow_whole_field K]
  by_cases h : ∀ j, Fintype.card K - 1 ∣ u j ∧ u j ≠ 0
  · rw [if_pos h, Finset.prod_congr rfl (fun j _ => if_pos (h j)),
      Finset.prod_const, card_univ]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg (by tauto)])

end Vanish.Foundations.FirstPrinciples.Transcribe
