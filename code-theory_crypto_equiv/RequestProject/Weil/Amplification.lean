import RequestProject.Weil.CharSum

/-!
# Extension-field amplification and the power-sum (eigenvalue) descent

The two-sided point-count bound `|#C_f(𝔽_q) - q| ≤ (d-1)(p-1)√q` directly controls only the *sum*
of the `p-1` nontrivial character sums attached to `f`.  To extract the sharp bound
`‖∑ₓ ψ(f x)‖ ≤ (d-1)√q` for a *single* nontrivial character one runs the classical
**extension-field amplification** ("tensor-power trick" / L-function eigenvalue argument):

* the character sum `S_k = ∑_{x∈𝔽_{q^k}} ψ_k(f(x))` over the degree-`k` extension is, by rationality
  of the Artin–Schreier L-function, a **power sum** `S_k = -∑_{i} α_iᵏ` of at most `d-1` complex
  "reciprocal roots" `α_i` (`exists_charSum_eigenvalues`);
* the point-count bound over every `𝔽_{q^k}` forces `‖∑_i α_iᵏ‖ ≤ C·(√q)ᵏ` for all `k`, and a
  power-sum/dominant-root estimate then gives `‖α_i‖ ≤ √q` for each `i`
  (`norm_le_of_powerSum_bound`);
* therefore `‖S_1‖ = ‖∑_i α_i‖ ≤ (d-1)√q` (`norm_sum_le_of_powerSum_bound`).

This module isolates the purely analytic engine (the power-sum estimates, which are real, provable
content) and records the one deep input — rationality of the L-function — as a clearly-labelled
skeleton.

## Main statements (skeletons)
* `Weil.Amplification.norm_le_of_powerSum_bound` — bounded power sums ⇒ each `‖α i‖ ≤ R`.
* `Weil.Amplification.norm_sum_le_of_powerSum_bound` — hence `‖∑ α i‖ ≤ r·R`.
* `Weil.Amplification.exists_powerSum_repn` — L-function rationality: char sums over extensions are a
  power sum of `≤ d-1` roots (deep core of this module).
* `Weil.Amplification.charSum_single_le_of_extension_bound` — the assembled single-character descent.
-/

open scoped BigOperators

namespace Weil
namespace Amplification

/-- **Power-sum (dominant-root) estimate.**  If the power sums `∑_i (α i)ᵏ` are bounded by `C·Rᵏ`
for *all* `k ≥ 1` with a fixed constant `C`, then every `‖α i‖ ≤ R`.  (If some `‖α i‖ > R` the
`k`-th power sum would grow faster than `Rᵏ`.) -/
lemma norm_le_of_powerSum_bound {r : ℕ} (α : Fin r → ℂ) (R C : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (h : ∀ k : ℕ, 1 ≤ k → ‖∑ i, (α i) ^ k‖ ≤ C * R ^ k) (i : Fin r) :
    ‖α i‖ ≤ R := by
  by_contra h_contra
  have h_max : ∃ j, ‖α j‖ > R := ⟨ i, not_le.mp h_contra ⟩
  obtain ⟨j, hj⟩ : ∃ j, ‖α j‖ > R ∧ ∀ i, ‖α i‖ ≤ ‖α j‖ := by
    obtain ⟨j, hj⟩ : ∃ j, ∀ i, ‖α i‖ ≤ ‖α j‖ := by
      simpa using Finset.exists_max_image Finset.univ ( fun i => ‖α i‖ ) ⟨ i, Finset.mem_univ i ⟩;
    exact ⟨ j, by obtain ⟨ k, hk ⟩ := h_max; linarith [ hj k ], hj ⟩;
  -- Consider the Cesàro average $A_N = \frac{1}{N} \sum_{k=1}^N \frac{S_k}{\alpha_j^k}$.
  set A : ℕ → ℂ := fun N => (1 / (N : ℂ)) * ∑ k ∈ Finset.Icc 1 N, (∑ i, α i ^ k) / (α j) ^ k;
  have hA : Filter.Tendsto (fun N : ℕ => A N) Filter.atTop (nhds (∑ i ∈ Finset.univ.filter (fun i => α i = α j), 1)) := by
    have hA : ∀ i, Filter.Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ k ∈ Finset.Icc 1 N, (α i / α j) ^ k) Filter.atTop (nhds (if α i = α j then 1 else 0)) := by
      intro i
      by_cases hi : α i = α j;
      · by_cases hj : α j = 0 <;> simp_all +decide [ div_eq_mul_inv ];
        · linarith;
        · exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with N hN; simp +decide [ hN ] );
      · by_cases hi' : α j = 0 <;> simp_all +decide [ div_eq_mul_inv ];
        have h_geo_series : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, (α i * (α j)⁻¹) ^ k = (α i * (α j)⁻¹) * ((α i * (α j)⁻¹) ^ N - 1) / ((α i * (α j)⁻¹) - 1) := by
          intro N; erw [ geom_sum_Ico ] <;> norm_num ; ring;
          exact div_ne_one_of_ne hi;
        have h_geo_series_bound : ∀ N : ℕ, ‖(α i * (α j)⁻¹) ^ N - 1‖ ≤ 2 := by
          intro N
          have h_geo_series_bound : ‖(α i * (α j)⁻¹) ^ N‖ ≤ 1 := by
            simp +zetaDelta at *;
            exact pow_le_one₀ ( by positivity ) ( div_le_one_of_le₀ ( hj.2 i ) ( by positivity ) );
          exact le_trans ( norm_sub_le _ _ ) ( by norm_num at *; linarith );
        rw [ tendsto_zero_iff_norm_tendsto_zero ];
        simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        exact squeeze_zero ( fun _ => by positivity ) ( fun N => mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( h_geo_series_bound N ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) ( by simpa [ mul_comm, mul_left_comm, mul_assoc ] using tendsto_inv_atTop_nhds_zero_nat.mul_const ( ‖α i‖ * ( ‖α j‖⁻¹ * ( ‖α i * ( α j ) ⁻¹ - 1‖⁻¹ * 2 ) ) ) );
    convert tendsto_finset_sum _ fun i _ => hA i using 2;
    any_goals exact Finset.univ;
    · simp +zetaDelta at *;
      simp +decide [ div_pow, Finset.mul_sum _ _ _, Finset.sum_div ];
      exact Finset.sum_comm;
    · rw [ Finset.sum_filter ];
  have hA_pt : ∀ N : ℕ, N ≥ 1 → ‖A N‖ ≤ (C / N) * (∑ k ∈ Finset.Icc 1 N, (R / ‖α j‖) ^ k) := by
    intros N hN
    have hA_bound_step : ∀ k ∈ Finset.Icc 1 N, ‖(∑ i, α i ^ k) / (α j) ^ k‖ ≤ C * (R / ‖α j‖) ^ k := by
      simp_all +decide [ div_pow, mul_div_assoc ];
      exact fun k hk₁ hk₂ => by rw [ mul_div ] ; exact div_le_div_of_nonneg_right ( h k hk₁ ) ( by positivity ) ;
    simp +zetaDelta at *;
    refine' le_trans ( mul_le_mul_of_nonneg_left ( norm_sum_le _ _ ) ( by positivity ) ) _;
    rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( hA_bound_step x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ) ( by positivity : 0 ≤ ( N : ℝ ) ⁻¹ ) ;
  have hA_bound : Filter.Tendsto (fun N : ℕ => (C / N) * (∑ k ∈ Finset.Icc 1 N, (R / ‖α j‖) ^ k)) Filter.atTop (nhds 0) := by
    have hA_bound : Filter.Tendsto (fun N : ℕ => (C / N) * (∑ k ∈ Finset.range N, (R / ‖α j‖) ^ (k + 1))) Filter.atTop (nhds 0) := by
      have hA_bound : Filter.Tendsto (fun N : ℕ => (C / N) * (∑ k ∈ Finset.range N, (R / ‖α j‖) ^ k)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat ) |> Filter.Tendsto.mul <| hasSum_geometric_of_lt_one ( by exact div_nonneg hR <| norm_nonneg _ ) ( by rw [ div_lt_iff₀ ] <;> linarith ) |> HasSum.tendsto_sum_nat;
      convert hA_bound.const_mul ( R / ‖α j‖ ) using 2 <;> norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact hA_bound.congr fun N => by erw [ Finset.sum_Ico_eq_sum_range ] ; ac_rfl;
  have hnorm := hA.norm;
  exact absurd ( le_of_tendsto_of_tendsto hnorm hA_bound <| Filter.eventually_atTop.mpr ⟨ 1, fun N hN => hA_pt N hN ⟩ ) ( by norm_num [ show ( Finset.card ( Finset.filter ( fun i => α i = α j ) Finset.univ ) : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ j, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, rfl ⟩ ⟩ ] )

/-- **Single-power consequence.**  Under the same hypotheses, the first power sum is bounded by
`r·R`.  This is the step that turns `‖α i‖ ≤ √q` into `‖∑ α i‖ ≤ (d-1)√q`. -/
lemma norm_sum_le_of_powerSum_bound {r : ℕ} (α : Fin r → ℂ) (R C : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (h : ∀ k : ℕ, 1 ≤ k → ‖∑ i, (α i) ^ k‖ ≤ C * R ^ k) :
    ‖∑ i, α i‖ ≤ r * R := by
  have h_triangle : ‖∑ i, α i‖ ≤ ∑ i, ‖α i‖ := norm_sum_le _ _
  convert h_triangle.trans ( Finset.sum_le_sum fun i _ => norm_le_of_powerSum_bound α R C hC hR h i ) using 1 ; norm_num

/-
**L-function rationality (deep input).**

*CORRECTION (commented out — false as originally stated).*  The skeleton stated this as

```
lemma exists_powerSum_repn (Sk : ℕ → ℂ) (d : ℕ) (hS0 : Sk 0 = 0) :
    ∃ (r : ℕ) (α : Fin r → ℂ), r ≤ d - 1 ∧ ∀ k, 1 ≤ k → Sk k = - ∑ i, (α i) ^ k
```

i.e. that **every** sequence `Sk` with `Sk 0 = 0` is (up to sign) the power-sum sequence of at most
`d-1` complex numbers.  This is *false*: a generic sequence is not a finite power sum at all.  For
example with `d = 1` the conclusion forces `r = 0`, hence `Sk k = -∑_{i ∈ ∅} … = 0` for all `k ≥ 1`;
but `Sk` was arbitrary (e.g. `Sk = fun k => k`), so the statement fails.  The hypothesis `Sk 0 = 0`
does not tie `Sk` to a power sum in any way.

The genuine content — rationality of the Artin–Schreier L-function, i.e. that the *actual* family of
extension character sums is a power sum of `≤ d-1` reciprocal roots — is a real theorem, but it can
only be stated for the specific `Sk` arising from `extCharSum`.  It is recorded faithfully (with the
correct hypotheses, as a true deep `sorry`) in `Weil.Extensions.exists_charSum_eigenvalues_le` and
`Weil.Extensions.exists_combined_eigenvalues`, not as a property of an arbitrary sequence.
-/

/-- **Assembled single-character descent.**  If the character sums `Sk` over all extensions admit a
power-sum representation by `≤ d-1` roots, and the extension point-count bound gives
`‖Sk k‖ ≤ (d-1)·(√q)ᵏ` for all `k`, then the base sum satisfies `‖Sk 1‖ ≤ (d-1)·√q`. -/
lemma charSum_single_le_of_extension_bound (Sk : ℕ → ℂ) (d : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hrepn : ∃ (r : ℕ) (α : Fin r → ℂ), r ≤ d - 1 ∧
      (∀ k, 1 ≤ k → Sk k = - ∑ i, (α i) ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → ‖∑ i, (α i) ^ k‖ ≤ (d - 1 : ℝ) * (Real.sqrt q) ^ k)) :
    ‖Sk 1‖ ≤ (d - 1 : ℝ) * Real.sqrt q := by
  obtain ⟨r, α, hr, hrepn, hbound⟩ := hrepn
  have h1 : Sk 1 = - ∑ i, α i := by simpa using hrepn 1 le_rfl
  have hb := hbound 1 le_rfl
  rw [h1]
  simpa using hb

end Amplification
end Weil
