import Mathlib
import RequestProject.Foundations.FirstPrinciples.Decomp.GaussWilson

/-!
# Decomposition library — Core (A·fp·s2): Morita's `p`-adic Γ, bottom-up

This module **expands the deep core** `FPPadicGamma.padicGamma` (and its seven
carried properties) into an exhaustive bottom-up skeleton.

The construction is the classical one (Morita 1975; Robert, *A Course in p-adic
Analysis* VII.1):

```
   padicFactorialTrunc n  =  (-1)ⁿ · ∏_{0 < j < n, p ∤ j} j           (a real ℤ_[p] value)
   Γ_p(x)  =  lim_{n → x in ℤ_[p]} padicFactorialTrunc n              (continuous extension)
```

The convergence is now **proved**: the analytic heart is the *window congruence*
`f(a + pᴹ) ≡ f(a) (mod pᴹ)` (`padicFactorialTrunc_window_congr`), which is derived
from Gauss's prime-power generalization of Wilson's theorem
(`GaussWilson.prod_units_zmod_prime_pow_odd`, `prod_units_zmod_two_pow`).  From the
congruence we obtain the metric Cauchy estimate
(`padicFactorialTrunc_dist_le`) and hence the limit
(`padicFactorialTrunc_converges`).

## Sources

Morita (1975); Robert, *A Course in p-adic Analysis*, Ch. VII; Gross–Koblitz
(Ann. Math. 1979).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open scoped BigOperators
open Filter Topology Finset

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **The truncated factorial** `(-1)ⁿ · ∏_{0<j<n, p∤j} j` in `ℤ_[p]`.  A genuine
definition (no `sorry`): the index set `(range n).filter (¬ p ∣ ·)` automatically
excludes `j = 0` (since `p ∣ 0`). -/
noncomputable def padicFactorialTrunc (n : ℕ) : ℤ_[p] :=
  (-1) ^ n * ∏ j ∈ (Finset.range n).filter (fun j => ¬ p ∣ j), (j : ℤ_[p])

/-- **Value at `0`.**  Empty product, sign `(-1)⁰ = 1`. -/
theorem padicFactorialTrunc_zero : padicFactorialTrunc (p := p) 0 = 1 := by
  simp [padicFactorialTrunc]

/-
**Recurrence step, coprime case.**  When `p ∤ n`, the new factor `n` enters the
product, so `padicFactorialTrunc (n+1) = -n · padicFactorialTrunc n`.
-/
theorem padicFactorialTrunc_succ_unit_step (n : ℕ) (hn : ¬ p ∣ n) :
    padicFactorialTrunc (p := p) (n + 1) = (-(n : ℤ_[p])) * padicFactorialTrunc n := by
  unfold padicFactorialTrunc; simp +decide [ Finset.prod_filter, Finset.prod_range_succ, hn ] ; ring;

/-
**Recurrence step, divisible case.**  When `p ∣ n`, no new factor enters, so
`padicFactorialTrunc (n+1) = -padicFactorialTrunc n`.
-/
theorem padicFactorialTrunc_succ_nonunit_step (n : ℕ) (hn : p ∣ n) :
    padicFactorialTrunc (p := p) (n + 1) = (-1) * padicFactorialTrunc n := by
  unfold padicFactorialTrunc;
  simp +decide [ Finset.prod_filter, Finset.prod_range_succ, pow_succ', mul_comm, hn ]

/-
**Each truncated factorial is a unit.**  The product runs over integers coprime
to `p`, all of which are `p`-adic units, and `(-1)ⁿ` is a unit.
-/
theorem padicFactorialTrunc_isUnit (n : ℕ) : IsUnit (padicFactorialTrunc (p := p) n) := by
  refine' IsUnit.mul _ _;
  · exact IsUnit.pow _ ( isUnit_one.neg );
  · refine' IsUnit.prod_iff.mpr _;
    intro a ha; rw [ PadicInt.isUnit_iff ] ; norm_cast; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp.1 ] ;
    exact ha.2

/-! ### The convergence core, via Gauss–Wilson -/

/-
**Window factorization.**  Splitting the range `[0, a+pᴹ)` at `a`, the truncated
factorial factors as the sign times `f(a)` times the product over the coprime
residues in the window `[a, a+pᴹ)`.
-/
theorem padicFactorialTrunc_window_factor (M a : ℕ) :
    padicFactorialTrunc (p := p) (a + p ^ M)
      = (-1) ^ (p ^ M) * padicFactorialTrunc a *
          ∏ j ∈ (Finset.Ico a (a + p ^ M)).filter (fun j => ¬ p ∣ j), (j : ℤ_[p]) := by
  unfold padicFactorialTrunc;
  rw [ Finset.prod_filter, Finset.prod_filter, Finset.prod_filter ];
  rw [ ← Finset.prod_range_mul_prod_Ico _ ( by linarith [ pow_pos hp.1.pos M ] : a ≤ a + p ^ M ) ] ; ring;

/-
**The window coprime-residue product is a complete unit product.**  Reducing
mod `pᴹ`, the residues `j` in a length-`pᴹ` window with `p ∤ j` biject onto the units
of `ZMod (pᴹ)`, so their product equals the product of all units.
-/
theorem window_filter_prod_eq_units (M a : ℕ) (hM : 1 ≤ M) :
    ∏ j ∈ (Finset.Ico a (a + p ^ M)).filter (fun j => ¬ p ∣ j), ((j : ZMod (p ^ M)))
      = ∏ x : (ZMod (p ^ M))ˣ, (x : ZMod (p ^ M)) := by
  refine' Finset.prod_bij ?_ _ _ _ _ <;> try simp_all +decide [ Nat.ModEq ];
  use fun x hx => Units.mkOfMulEqOne ( x : ZMod ( p ^ M ) ) ( ( x : ZMod ( p ^ M ) ) ⁻¹ ) ( by
    rw [ ZMod.mul_inv_of_unit ];
    rw [ ZMod.isUnit_iff_coprime ];
    exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hp.1.coprime_iff_not_dvd.mpr <| by aesop; );
  · all_goals generalize_proofs at *;
    simp_all +decide [ Units.ext_iff ];
    intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ h; rw [ ZMod.natCast_eq_natCast_iff ] at h; simp_all +decide [ Nat.modEq_iff_dvd ] ;
    obtain ⟨ k, hk ⟩ := h; nlinarith [ show k = 0 by nlinarith ] ;
  · all_goals generalize_proofs at *;
    intro b
    obtain ⟨j, hj⟩ : ∃ j ∈ Finset.Ico a (a + p ^ M), (j : ZMod (p ^ M)) = b := by
      use a + ((b.val.val + (p ^ M - a % p ^ M)) % p ^ M);
      simp +decide [ ZMod.natCast_eq_natCast_iff' ];
      exact ⟨ Nat.mod_lt _ ( pow_pos hp.1.pos _ ), by simp +decide [ Nat.cast_sub ( show a % p ^ M ≤ p ^ M from Nat.le_of_lt ( Nat.mod_lt _ ( pow_pos hp.1.pos _ ) ) ) ] ⟩
    generalize_proofs at *;
    refine' ⟨ j, ⟨ Finset.mem_Ico.mp hj.1, _ ⟩, _ ⟩ <;> simp_all +decide [ Units.ext_iff ];
    intro h; have := b.isUnit; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
    have := b.isUnit; rw [ ZMod.natCast_eq_zero_iff ] at h; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp.1 ] ;
    have := ZMod.isUnit_iff_coprime ( j : ℕ ) ( p ^ M ) ; simp_all +decide [ Nat.coprime_pow_right_iff, hp.1.coprime_iff_not_dvd ] ;
    exact absurd ( Nat.dvd_gcd h ( dvd_pow_self p ( by linarith : M ≠ 0 ) ) ) ( by rw [ this.gcd_eq_one ] ; exact Nat.Prime.not_dvd_one hp.1 );
  · aesop

/-
**Sign × Wilson value = 1 mod pᴹ.**  By Gauss's generalization of Wilson's
theorem: for `p` odd both factors are `-1`, and for `p = 2` (with `M ≥ 3`) both are
`1`.
-/
theorem neg_one_pow_mul_units_prod (M : ℕ) (hM : 3 ≤ M) :
    ((-1) ^ (p ^ M) : ZMod (p ^ M)) * ∏ x : (ZMod (p ^ M))ˣ, (x : ZMod (p ^ M)) = 1 := by
  by_cases h : p = 2;
  · subst h;
    convert prod_units_zmod_two_pow M hM using 1;
    rcases M with ( _ | _ | M ) <;> simp_all +decide [ Nat.pow_succ', parity_simps ];
  · rw [ Vanish.Foundations.FirstPrinciples.Decomp.prod_units_zmod_prime_pow_odd p M ( hp.1.odd_of_ne_two h ) ( by linarith ), Odd.neg_one_pow ( Nat.Prime.odd_of_ne_two hp.1 h |> Odd.pow ) ] ; ring

/-
**The window congruence (the analytic heart).**  `f(a + pᴹ) ≡ f(a) (mod pᴹ)`.
-/
theorem padicFactorialTrunc_window_congr (M : ℕ) (hM : 3 ≤ M) (a : ℕ) :
    PadicInt.toZModPow M (padicFactorialTrunc (p := p) (a + p ^ M))
      = PadicInt.toZModPow M (padicFactorialTrunc a) := by
  -- distributing over the product (map_mul, map_pow, map_neg, map_one, map_prod).
  have h_distribute : (PadicInt.toZModPow M) (padicFactorialTrunc (a + p ^ M)) = ((-1) ^ (p ^ M) : ZMod (p ^ M)) * (PadicInt.toZModPow M (padicFactorialTrunc a)) * (∏ j ∈ (Finset.Ico a (a + p ^ M)).filter (fun j => ¬ p ∣ j), ((j : ZMod (p ^ M)))) := by
    rw [ padicFactorialTrunc_window_factor ];
    simp +decide [ map_mul, map_pow, map_neg, map_one, map_prod ];
  rw [ h_distribute, mul_right_comm ];
  rw [ window_filter_prod_eq_units M a ( by linarith ), neg_one_pow_mul_units_prod M hM, one_mul ]

/-
**Telescoped periodicity.**  `f(a + k·pᴹ) ≡ f(a) (mod pᴹ)`.
-/
theorem padicFactorialTrunc_toZModPow_add_mul (M : ℕ) (hM : 3 ≤ M) (a k : ℕ) :
    PadicInt.toZModPow M (padicFactorialTrunc (p := p) (a + k * p ^ M))
      = PadicInt.toZModPow M (padicFactorialTrunc a) := by
  induction' k with k ih;
  · norm_num;
  · rw [ Nat.succ_mul, ← add_assoc, padicFactorialTrunc_window_congr M hM ( a + k * p ^ M ), ih ]

/-
**Congruence for `p`-adically close arguments.**  If `m ≡ n (mod pᴹ)` then
`f(m) ≡ f(n) (mod pᴹ)`.
-/
theorem padicFactorialTrunc_toZModPow_congr (M : ℕ) (hM : 3 ≤ M) (m n : ℕ)
    (h : (m : ZMod (p ^ M)) = (n : ZMod (p ^ M))) :
    PadicInt.toZModPow M (padicFactorialTrunc (p := p) m)
      = PadicInt.toZModPow M (padicFactorialTrunc n) := by
  obtain hmn | hnm := le_total m n;
  · -- Since $m \equiv n \pmod{p^M}$, we have $n = m + k \cdot p^M$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k * p ^ M := by
      exact ⟨ ( n - m ) / p ^ M, by rw [ Nat.div_mul_cancel ( show p ^ M ∣ n - m from by rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide [ Nat.cast_sub hmn ] ), add_tsub_cancel_of_le hmn ] ⟩;
    rw [ hk, padicFactorialTrunc_toZModPow_add_mul M hM m k ];
  · convert padicFactorialTrunc_toZModPow_add_mul M hM n ( m - n |> fun x => x / p ^ M ) using 1;
    rw [ Nat.div_mul_cancel, add_tsub_cancel_of_le hnm ];
    rw [ ← ZMod.natCast_eq_zero_iff ] ; cases le_iff_exists_add'.mp hnm ; aesop;

/-
**The metric Cauchy estimate.**  If `m ≡ n (mod pᴹ)` then
`‖f(m) − f(n)‖ ≤ p^(−M)`.
-/
theorem padicFactorialTrunc_dist_le (M : ℕ) (hM : 3 ≤ M) (m n : ℕ)
    (h : (m : ZMod (p ^ M)) = (n : ZMod (p ^ M))) :
    ‖padicFactorialTrunc (p := p) m - padicFactorialTrunc n‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
  convert PadicInt.norm_le_pow_iff_mem_span_pow _ _ |>.mpr _;
  rw [ ← PadicInt.ker_toZModPow ];
  convert sub_eq_zero.mpr ( padicFactorialTrunc_toZModPow_congr M hM m n h ) using 1;
  simp +decide [ RingHom.mem_ker ]

/-
**The comap filter is nontrivial.**  Since `ℕ` is dense in `ℤ_[p]`, the filter
pulling back `𝓝 x` through `Nat.cast` is `NeBot`.
-/
theorem comap_cast_neBot (x : ℤ_[p]) :
    (comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x)).NeBot := by
  refine' Filter.comap_neBot_iff.mpr _;
  intro t ht;
  -- Since $t$ is a neighborhood of $x$, there exists an $\epsilon > 0$ such that the ball $B(x, \epsilon)$ is contained in $t$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ t := by
    exact Metric.mem_nhds_iff.mp ht;
  -- Since ℕ is dense in ℤ_[p], there exists an n in ℕ such that ‖n - x‖ < ε.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(n : ℤ_[p]) - x‖ < ε := by
    have h_dense : DenseRange (Nat.cast : ℕ → ℤ_[p]) := by
      grind +suggestions;
    have := h_dense x;
    rw [ Metric.mem_closure_range_iff ] at this;
    simpa only [ dist_eq_norm', norm_sub_rev ] using this ε hε_pos;
  exact ⟨ n, hε <| mem_ball_iff_norm.mpr hn ⟩

/-
**The convergence core.**  Along the filter pulling back the `p`-adic
neighbourhoods of `x` through `ℕ ↪ ℤ_[p]`, the truncated factorial converges.  Now a
real proof: the metric Cauchy estimate `padicFactorialTrunc_dist_le` makes the image
filter Cauchy, and `ℤ_[p]` is complete.
-/
theorem padicFactorialTrunc_converges (x : ℤ_[p]) :
    ∃ y : ℤ_[p], Tendsto (fun n : ℕ => padicFactorialTrunc (p := p) n)
      (comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x)) (𝓝 y) := by
  refine' ( CompleteSpace.complete _ );
  refine' Metric.cauchy_iff.2 _;
  refine' ⟨ Filter.neBot_iff.mpr _, _ ⟩;
  · exact Filter.neBot_iff.mp ( comap_cast_neBot x |> fun h => h.map _ );
  · intro ε hε
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 3 ≤ M ∧ (p : ℝ) ^ (-(M : ℤ)) < ε := by
      have h_lim : Filter.Tendsto (fun M : ℕ => (p : ℝ) ^ (-(M : ℤ))) Filter.atTop (nhds 0) := by
        simpa using tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt ( show ( p : ℝ ) > 1 from mod_cast hp.1.one_lt ) );
      exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds hε ) ) |> fun ⟨ M, hM ⟩ => ⟨ M + 3, by linarith, hM _ <| by linarith ⟩;
    refine' ⟨ _, Filter.image_mem_map ( Filter.preimage_mem_comap <| Metric.ball_mem_nhds x <| show 0 < ( p : ℝ ) ^ ( -M : ℤ ) by exact zpow_pos ( Nat.cast_pos.mpr hp.1.pos ) _ ), _ ⟩;
    rintro _ ⟨ m, hm, rfl ⟩ _ ⟨ n, hn, rfl ⟩;
    -- By the ultrametric inequality, ‖(m:ℤ_[p]) - (n:ℤ_[p])‖ ≤ max (‖(m:ℤ_[p])-x‖) (‖(n:ℤ_[p])-x‖) < r = (p:ℝ)^(-(M:ℤ)).
    have h_ultrametric : ‖(m : ℤ_[p]) - (n : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
      have h_ultrametric : ‖(m : ℤ_[p]) - (n : ℤ_[p])‖ ≤ max ‖(m : ℤ_[p]) - x‖ ‖(n : ℤ_[p]) - x‖ := by
        grind +suggestions;
      exact h_ultrametric.trans ( max_le hm.out.le hn.out.le );
    -- Since ‖(m:ℤ_[p]) - (n:ℤ_[p])‖ ≤ (p:ℝ)^(-(M:ℤ)), we have (m : ZMod (p^M)) = (n : ZMod (p^M)).
    have h_cong : (m : ZMod (p ^ M)) = (n : ZMod (p ^ M)) := by
      have h_cong : (m : ℤ_[p]) - (n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
        convert PadicInt.norm_le_pow_iff_mem_span_pow _ _ |>.1 h_ultrametric using 1;
      rw [ Ideal.mem_span_singleton ] at h_cong;
      obtain ⟨ k, hk ⟩ := h_cong;
      replace hk := congr_arg ( PadicInt.toZModPow M ) hk ; simp_all +decide [ sub_eq_iff_eq_add ];
      norm_cast;
      erw [ ZMod.natCast_self ] ; norm_num;
    exact lt_of_le_of_lt ( padicFactorialTrunc_dist_le M hM.1 m n h_cong ) hM.2

/-- **Morita's `p`-adic Gamma function** as the limit-defined continuous extension
of the truncated factorial. -/
noncomputable def padicGamma (x : ℤ_[p]) : ℤ_[p] :=
  (padicFactorialTrunc_converges x).choose

/-- **Defining property of `Γ_p`.** -/
theorem padicGamma_spec (x : ℤ_[p]) :
    Tendsto (fun n : ℕ => padicFactorialTrunc (p := p) n)
      (comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x)) (𝓝 (padicGamma x)) :=
  (padicFactorialTrunc_converges x).choose_spec

/-! ### Limit-passing: deriving the `Γ_p` properties -/

/-
**Extensionality from high levels.**  Two `p`-adic integers agreeing modulo `pᴹ`
for every `M ≥ 3` are equal (lower levels factor through `M = 3`).
-/
theorem padicInt_ext_ge3 {a b : ℤ_[p]}
    (h : ∀ M : ℕ, 3 ≤ M → PadicInt.toZModPow M a = PadicInt.toZModPow M b) : a = b := by
  refine' PadicInt.ext_of_toZModPow.mp _;
  intro n;
  have := h ( n + 3 ) ( by linarith );
  convert congr_arg ( ZMod.castHom ( pow_dvd_pow p ( by linarith : n ≤ n + 3 ) ) ( ZMod ( p ^ n ) ) ) this using 1 <;> simp +decide [ PadicInt.zmod_cast_comp_toZModPow ]

/-
**The reduction `toZModPow M` is continuous** (it is locally constant: each
fibre is a closed ball, open in the ultrametric space `ℤ_[p]`).
-/
theorem continuous_toZModPow (M : ℕ) :
    Continuous (PadicInt.toZModPow M : ℤ_[p] → ZMod (p ^ M)) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x;
  refine' Continuous.tendsto' _ _ _ _;
  · refine' continuous_iff_continuousAt.mpr _;
    intro x;
    refine' tendsto_const_nhds.congr' _;
    filter_upwards [ Metric.closedBall_mem_nhds x ( show 0 < ( p : ℝ ) ^ ( - ( M : ℤ ) ) by exact zpow_pos ( Nat.cast_pos.mpr hp.1.pos ) _ ) ] with y hy;
    -- Since $y \in \text{Metric.closedBall } x (p^{-M})$, we have $x - y \in \text{Ideal.span } \{p^M\}$.
    have h_diff : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
      convert PadicInt.norm_le_pow_iff_mem_span_pow _ _ |>.1 _;
      simpa [ dist_eq_norm, norm_sub_rev ] using hy;
    rw [ ← sub_eq_zero, ← map_sub ];
    rw [ ← RingHom.mem_ker, PadicInt.ker_toZModPow ] ; aesop;
  · rfl

/-
**The master limit-passing lemma.**  If `x ≡ n (mod pᴹ)` then
`Γ_p(x) ≡ f(n) (mod pᴹ)`.  This is `padicGamma_spec` composed with the continuous
(locally constant) reduction `toZModPow M` and the congruence
`padicFactorialTrunc_toZModPow_congr`.
-/
theorem padicGamma_toZModPow_eq (M : ℕ) (hM : 3 ≤ M) (x : ℤ_[p]) (n : ℕ)
    (hn : PadicInt.toZModPow M x = (n : ZMod (p ^ M))) :
    PadicInt.toZModPow M (padicGamma x) = PadicInt.toZModPow M (padicFactorialTrunc n) := by
  have h_congr : ∀ᶠ m in comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x), PadicInt.toZModPow M (padicFactorialTrunc (p := p) m) = PadicInt.toZModPow M (padicFactorialTrunc n) := by
    have h_congr : ∀ m : ℕ, (m : ℤ_[p]) ∈ Metric.closedBall x ((p : ℝ) ^ (-(M : ℤ))) → (m : ZMod (p ^ M)) = (n : ZMod (p ^ M)) := by
      intro m hm
      have h_diff : (m : ℤ_[p]) - x ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
        rw [ Metric.mem_closedBall, dist_eq_norm ] at hm;
        rw [ PadicInt.norm_le_pow_iff_mem_span_pow ] at hm ; aesop;
      rw [ ← hn, ← sub_eq_zero ];
      rw [ ← PadicInt.ker_toZModPow ] at *;
      simpa using h_diff;
    refine' Filter.eventually_comap.mpr _;
    filter_upwards [ Metric.closedBall_mem_nhds x ( show 0 < ( p : ℝ ) ^ ( - ( M : ℤ ) ) by exact zpow_pos ( Nat.cast_pos.mpr hp.1.pos ) _ ) ] with y hy using fun a ha => by have := h_congr a ( by simpa [ ha ] using hy ) ; exact padicFactorialTrunc_toZModPow_congr M hM a n this;
  have h_tendsto : Tendsto (fun m : ℕ => PadicInt.toZModPow M (padicFactorialTrunc (p := p) m)) (comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x)) (𝓝 (PadicInt.toZModPow M (padicGamma x))) := by
    exact Filter.Tendsto.comp ( continuous_toZModPow M |> Continuous.continuousAt ) ( padicGamma_spec x );
  convert tendsto_nhds_unique h_tendsto _;
  · convert comap_cast_neBot x;
  · exact tendsto_nhds_of_eventually_eq h_congr

/-
**`Γ_p` preserves the `toZModPow`-fibres.**  If `x ≡ x' (mod pᴹ)` then
`Γ_p(x) ≡ Γ_p(x') (mod pᴹ)`.
-/
theorem padicGamma_toZModPow_congr (M : ℕ) (hM : 3 ≤ M) (x x' : ℤ_[p])
    (h : PadicInt.toZModPow M x = PadicInt.toZModPow M x') :
    PadicInt.toZModPow M (padicGamma x) = PadicInt.toZModPow M (padicGamma x') := by
  convert padicGamma_toZModPow_eq M hM x ( ( PadicInt.toZModPow M x ).val ) _ using 1;
  · rw [ h, padicGamma_toZModPow_eq ];
    · linarith;
    · cases p <;> aesop;
  · grind +suggestions

/-
**Agreement with the truncated factorial on `ℕ`.**
-/
theorem padicGamma_natCast (n : ℕ) :
    padicGamma (p := p) (n : ℤ_[p]) = padicFactorialTrunc n := by
  refine' padicInt_ext_ge3 fun M hM => _;
  convert padicGamma_toZModPow_eq M hM ( n : ℤ_[p] ) n _;
  convert map_natCast _ _;
  infer_instance

/-
**`Γ_p(0) = 1`.**  From `padicGamma_natCast 0` and `padicFactorialTrunc_zero`.
-/
theorem padicGamma_zero : padicGamma (0 : ℤ_[p]) = 1 := by
  convert padicGamma_natCast 0;
  simp [padicFactorialTrunc]

/-
**Continuity of `Γ_p`.**
-/
theorem padicGamma_continuous : Continuous (padicGamma (p := p)) := by
  rw [ Metric.continuous_iff ];
  intro x ε hε;
  -- Choose M such that (p : ℝ) ^ (-(M : ℤ)) < ε.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 3 ≤ M ∧ (p : ℝ) ^ (-(M : ℤ)) < ε := by
    have h_lim : Filter.Tendsto (fun M : ℕ => (p : ℝ) ^ (-(M : ℤ))) Filter.atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt ( show ( p : ℝ ) > 1 by exact_mod_cast hp.1.one_lt ) );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds hε ) ) |> fun ⟨ M, hM ⟩ => ⟨ M + 3, by linarith, hM _ <| by linarith ⟩;
  refine' ⟨ ( p : ℝ ) ^ ( -M : ℤ ), by exact zpow_pos ( Nat.cast_pos.mpr hp.1.pos ) _, fun y hy => _ ⟩;
  -- Since $‖y - x‖ < p^{-M}$, we have $y \equiv x \pmod{p^M}$.
  have h_cong : PadicInt.toZModPow M y = PadicInt.toZModPow M x := by
    have h_cong : y - x ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
      convert PadicInt.norm_le_pow_iff_mem_span_pow _ _ |>.1 _;
      exact le_of_lt hy;
    rw [ ← sub_eq_zero, ← map_sub ];
    rw [ ← RingHom.mem_ker, PadicInt.ker_toZModPow ] ; aesop;
  -- By the properties of the p-adic norm, we have that ‖padicGamma y - padicGamma x‖ ≤ p^(-M).
  have h_norm : ‖padicGamma y - padicGamma x‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    have h_norm : PadicInt.toZModPow M (padicGamma y - padicGamma x) = 0 := by
      have := padicGamma_toZModPow_congr M hM.1 y x h_cong; aesop;
    rw [ PadicInt.norm_le_pow_iff_mem_span_pow ];
    rw [ ← PadicInt.ker_toZModPow ] at * ; aesop;
  exact lt_of_le_of_lt h_norm hM.2

/-
**Functional equation, unit case.**  `Γ_p(x+1) = -x · Γ_p(x)` for `x` a unit.
-/
theorem padicGamma_succ_unit (x : ℤ_[p]) (hx : IsUnit x) :
    padicGamma (x + 1) = (-x) * padicGamma x := by
  apply padicInt_ext_ge3;
  intro M hM
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod (p ^ M)) = PadicInt.toZModPow M x ∧ ¬ p ∣ n := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod (p ^ M)) = PadicInt.toZModPow M x := by
      exact ⟨ _, ZMod.natCast_zmod_val _ ⟩;
    -- Since $x$ is a unit, $PadicInt.toZModPow M x$ is also a unit.
    have h_unit : IsUnit (PadicInt.toZModPow M x) := by
      exact hx.map _;
    rw [ ← hn, ZMod.isUnit_iff_coprime ] at h_unit;
    exact ⟨ n, hn, fun h => hp.1.not_dvd_one <| h_unit.gcd_eq_one ▸ Nat.dvd_gcd h ( dvd_pow_self _ <| by linarith ) ⟩;
  convert padicGamma_toZModPow_eq M hM ( x + 1 ) ( n + 1 ) _ using 1;
  · rw [ padicFactorialTrunc_succ_unit_step ];
    · have := padicGamma_toZModPow_eq M hM x n; aesop;
    · exact hn.2;
  · simp +decide [ hn.1 ]

/-
**Functional equation, non-unit case.**  `Γ_p(x+1) = -Γ_p(x)` for `x ∈ 𝔭`.
-/
theorem padicGamma_succ_nonunit (x : ℤ_[p]) (hx : ¬ IsUnit x) :
    padicGamma (x + 1) = (-1) * padicGamma x := by
  -- By padicInt_ext_ge3, fix M ≥ 3; show toZModPow M (padicGamma (x+1)) = toZModPow M ((-1) * padicGamma x).
  apply padicInt_ext_ge3
  intro M hM
  have h1 : PadicInt.toZModPow M (padicGamma (x + 1)) = PadicInt.toZModPow M ((-1 : ℤ_[p]) * (padicGamma x)) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod (p ^ M)) = PadicInt.toZModPow M x ∧ p ∣ n := by
      -- Since $x$ is not a unit, its $p$-adic norm is less than 1, which means that $x$ is divisible by $p$.
      have h_div : (p : ℤ_[p]) ∣ x := by
        grind +suggestions;
      obtain ⟨ y, rfl ⟩ := h_div;
      refine' ⟨ p * ( PadicInt.toZModPow M y |> ZMod.val ), _, _ ⟩ <;> norm_num;
    convert padicGamma_toZModPow_eq M hM ( x + 1 ) ( n + 1 ) _ using 1;
    · have := padicGamma_toZModPow_eq M hM x n hn.1.symm; simp_all +decide [ padicFactorialTrunc_succ_nonunit_step ] ;
    · aesop
  exact h1

/-
**`Γ_p` is everywhere a unit.**
-/
theorem padicGamma_unit (x : ℤ_[p]) : IsUnit (padicGamma x) := by
  -- By definition of $padicGamma$, we know that $padicGamma x$ is a unit if and only if $‖padicGamma x‖ = 1$.
  have h_norm : ‖padicGamma x‖ = 1 := by
    -- By definition of $padicGamma$, we know that $padicGamma x$ is a unit if and only if $‖padicGamma x‖ = 1$. Use this fact.
    have h_unit : ∀ n : ℕ, ‖padicFactorialTrunc (p := p) n‖ = 1 := by
      intro n;
      convert PadicInt.isUnit_iff.mp ( padicFactorialTrunc_isUnit n ) using 1;
    -- By definition of $padicGamma$, we know that $padicGamma x$ is the limit of $padicFactorialTrunc n$ as $n$ approaches $x$.
    have h_limit : Filter.Tendsto (fun n : ℕ => padicFactorialTrunc (p := p) n) (comap (Nat.cast : ℕ → ℤ_[p]) (𝓝 x)) (𝓝 (padicGamma x)) := by
      exact padicGamma_spec x;
    convert tendsto_nhds_unique ( h_limit.norm ) _;
    · convert comap_cast_neBot x;
    · simpa only [ h_unit ] using tendsto_const_nhds;
  grind +suggestions

/-
**The reflection formula.**  `Γ_p(x)·Γ_p(1-x) = ±1`.
-/
theorem padicGamma_reflection (x : ℤ_[p]) :
    padicGamma x * padicGamma (1 - x) = 1 ∨ padicGamma x * padicGamma (1 - x) = -1 := by
  -- Let R := fun x : ℤ_[p] => padicGamma x * padicGamma (1 - x). It suffices to show R x * R x = 1, then mul_self_eq_one_iff gives R x = 1 ∨ R x = -1 (the goal). Reduce R x * R x = 1 to S x = 1 where S := fun x => R x * R x.
  set R : ℤ_[p] → ℤ_[p] := fun x => padicGamma x * padicGamma (1 - x)
  set S : ℤ_[p] → ℤ_[p] := fun x => R x * R x
  have hrx_sq : R x * R x = 1 := by
    -- Step 1 (key recurrence) hsucc : ∀ x, S (x+1) = S x.
    have hsucc : ∀ x : ℤ_[p], S (x + 1) = S x := by
      intro x
      simp [R, S];
      by_cases hx : IsUnit x <;> simp_all +decide [ padicGamma_succ_unit, padicGamma_succ_nonunit ];
      · rw [ show 1 - x = -x + 1 by ring, padicGamma_succ_unit ] <;> ring;
        exact hx.neg;
      · rw [ show 1 - x = -x + 1 by ring, padicGamma_succ_nonunit ] ; aesop;
        aesop;
    -- Step 2 hnat : ∀ n : ℕ, S (n : ℤ_[p]) = 1, by induction on n.
    have hnat : ∀ n : ℕ, S (n : ℤ_[p]) = 1 := by
      intro n
      induction' n with n ih;
      · -- By definition of $R$, we have $R(0) = \Gamma_p(0) \cdot \Gamma_p(1)$.
        simp [R, S, padicGamma_zero, padicGamma_natCast];
        rw [ show padicGamma ( 1 : ℤ_[p] ) = -1 from ?_ ] ; norm_num;
        convert padicGamma_natCast 1 using 1;
        unfold padicFactorialTrunc; norm_num;
        rw [ Finset.prod_eq_one ] ; aesop;
      · simpa using hsucc n ▸ ih;
    -- Step 3 (density): S is continuous (padicGamma_continuous, continuity of x ↦ 1 - x, mul, and squaring). The constant function 1 is continuous. They agree on Set.range (Nat.cast : ℕ → ℤ_[p]), which is dense (PadicInt.denseRange_natCast). By Continuous.ext_on (with the dense range), S = fun _ => 1, so S x = 1 for the given x.
    have h_cont : Continuous S := by
      exact Continuous.mul ( Continuous.mul ( padicGamma_continuous ) ( padicGamma_continuous.comp ( continuous_const.sub continuous_id' ) ) ) ( Continuous.mul ( padicGamma_continuous ) ( padicGamma_continuous.comp ( continuous_const.sub continuous_id' ) ) );
    have h_dense : DenseRange (Nat.cast : ℕ → ℤ_[p]) := by
      grind +suggestions;
    have h_ext : S = fun _ => 1 := by
      apply Continuous.ext_on h_dense h_cont continuous_const;
      exact fun x hx => by obtain ⟨ n, rfl ⟩ := hx; exact hnat n;
    exact congr_fun h_ext x;
  exact mul_self_eq_one_iff.mp hrx_sq

end Vanish.Foundations.FirstPrinciples.Decomp