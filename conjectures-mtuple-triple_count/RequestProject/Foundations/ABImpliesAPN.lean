import RequestProject.Walsh.WalshAB

/-!
# Foundations — general almost-bent theory: AB ⟹ APN

This module establishes a genuinely *general* (not Kasami-specific) layer of
almost-bent theory: **every almost-bent permutation is APN**.

Together with the already-established `WalshAB.ab_from_moments` (the moment
method: an APN power permutation over `GF(2ⁿ)`, `n` odd, whose Walsh values are
`2^{(n+1)/2}`-divisible is AB), this closes the classical equivalence
**APN ⟺ AB** for power permutations in the odd-`n` regime, and the AB ⟹ APN
direction here needs neither the divisibility input nor `n` odd.

## Proof (Chabaud–Vaudenay / Carlet Ch. 6, the moment method)

Let `q = 2ⁿ = #F` and let `f` be a bijection with an AB spectrum, i.e.
`W(a,b)² ∈ {0, 2^{n+1}}` for every `a ≠ 0`.

* For `a ≠ 0`: since `W² ∈ {0, 2^{n+1}}` we have `W⁴ = 2^{n+1}·W²`, so by
  Parseval (`parseval_perm`, `∑_b W² = q²`) the fourth moment is
  `∑_b W(a,b)⁴ = 2^{n+1}·q² = 2·q³` (`walsh_fourth_of_ab`).
* For `a = 0`: since `f` is a bijection, `W(0,b) = q·[b = 0]`, so
  `∑_b W(0,b)⁴ = q⁴` (`walsh_fourth_a_zero`).
* Hence the double fourth moment is `∑_{a,b} W⁴ = q⁴ + (q−1)·2q³`.  Feeding this
  into `double_sum_fourth_moment` (`∑_{a,b} W⁴ = q²·∑_{a,b} N²`) gives
  `∑_{a,b} N(a,b)² = q² + (q−1)·2q`.
* For each `a ≠ 0` the differential count `N(a,·)` is **even** (`diffCount_even`,
  the fixed-point-free involution `x ↦ x + a`) and sums to `q` (`diffCount_sum`),
  so `∑_b N² ≥ 2q`, with equality iff `N(a,b) ∈ {0,2}`.  The `a = 0` row
  contributes exactly `q²` (`diffCount_zero_sq_sum`).  Since the total is exactly
  `q² + (q−1)·2q`, every `a ≠ 0` row is forced to its minimum `2q`, hence
  `N(a,b) ≤ 2`: `f` is **APN**.

## Main results

* `diffCount_even` — the differential count of any `f` at `a ≠ 0` is even.
* `walsh_fourth_of_ab` — AB permutation fourth moment `∑_b W(a,b)⁴ = 2q³`.
* `walsh_fourth_a_zero` — the `a = 0` fourth moment `∑_b W(0,b)⁴ = q⁴`.
* `ab_imp_apn` — **every AB permutation is APN**.
* `isAB_iff_three_valued` — the value-set characterization
  `IsAB ⟺ ∀ a ≠ 0, ∀ b, W(a,b) ∈ {0, ±2^{(n+1)/2}}` (`n` odd).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open WalshAB Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The differential count is even -/

/-
**Even differential count.**  For any `f` and any `a ≠ 0`, the number of
solutions of `f(x+a) + f(x) = b` is even: the map `x ↦ x + a` is a
fixed-point-free involution on the solution set (characteristic two).
-/
theorem diffCount_even (f : F → F) {a : F} (ha : a ≠ 0) (b : F) :
    Even (diffCount f a b) := by
  -- Let $S = \{x \in F \mid f(x + a) + f(x) = b\}$.
  set S := {x : F | f (x + a) + f x = b} with hS_def;
  -- The map $σ : x ↦ x + a$ restricts to a fixed-point-free involution on $S$.
  have h_inv : ∀ x ∈ S, x + a ∈ S ∧ x + a ≠ x := by
    grind +extAll;
  -- Since $σ$ is a fixed-point-free involution on $S$, $S$ can be partitioned into pairs $\{x, x + a\}$.
  have h_partition : ∃ T : Finset (Finset F), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ x ∈ t, x ∈ S) ∧ (∀ x ∈ S, ∃ t ∈ T, x ∈ t) ∧ (∀ t₁ t₂, t₁ ∈ T → t₂ ∈ T → t₁ ≠ t₂ → Disjoint t₁ t₂) := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.filter ( fun x => x ∈ S ) Finset.univ ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
    · grind;
  obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_partition;
  have h_card_S : Finset.card (Finset.filter (fun x => x ∈ S) Finset.univ) = Finset.sum T (fun t => t.card) := by
    rw [ ← Finset.card_biUnion ];
    · congr with x ; aesop;
    · exact fun t₁ ht₁ t₂ ht₂ h => hT₄ t₁ t₂ ht₁ ht₂ h;
  simp_all +decide [ diffCount ];
  rw [ Fintype.card_subtype ] ; exact h_card_S.symm ▸ even_iff_two_dvd.mpr ( dvd_mul_left _ _ ) ;

/-! ## Fourth moments -/

/-
**AB fourth moment.**  For an AB permutation, the fourth moment at any
`a ≠ 0` is `2q³`.  From `W² ∈ {0, 2^{n+1}}` (so `W⁴ = 2^{n+1}·W²`) and Parseval
`∑_b W² = q²`.
-/
theorem walsh_fourth_of_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f)
    (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
  convert congr_arg ( fun x : ℤ => 2 ^ ( n + 1 ) * x ) ( WalshAB.parseval_perm hcard f hf a ha ) using 1;
  · rw [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun b hb => _;
    cases hAB a ha b <;> simp_all +decide [ pow_succ, mul_assoc ];
  · rw [ hcard ] ; push_cast [ pow_succ ] ; ring

/-
**The `a = 0` fourth moment.**  For a bijection, `W(0,b) = q·[b=0]`, so the
fourth moment along `a = 0` is `q⁴`.
-/
theorem walsh_fourth_a_zero (f : F → F) (hf : Function.Bijective f) :
    ∑ b : F, walsh f 0 b ^ 4 = (Fintype.card F : ℤ) ^ 4 := by
  convert congr_arg ( fun x : ℤ => x ^ 4 ) ( WalshAB.walsh_zero_zero f ) using 1;
  rw [ Finset.sum_eq_single 0 ] <;> simp +contextual [ WalshAB.walsh_a_zero_perm ];
  exact fun b hb => WalshAB.walsh_a_zero_perm f hf b hb

/-! ## The differential second moment for an AB permutation -/

/-
**The total differential second moment of an AB permutation.**  Combining
the two fourth-moment computations through the double fourth-moment identity
`∑_{a,b} W⁴ = q²·∑_{a,b} N²`.
-/
theorem sum_diffCount_sq_of_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f) :
    ∑ a : F, ∑ b : F, (diffCount f a b : ℤ) ^ 2 =
      (Fintype.card F : ℤ) ^ 2
        + ((Fintype.card F : ℤ) - 1) * (2 * (Fintype.card F : ℤ)) := by
  have h_total : ∑ a, ∑ b, (walsh f a b : ℤ) ^ 4 = (Fintype.card F : ℤ) ^ 4 + (Fintype.card F - 1) * (2 * (Fintype.card F : ℤ) ^ 3) := by
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
    refine' congrArg₂ ( · + · ) _ _;
    · convert walsh_fourth_a_zero f hf using 1;
    · rw [ Finset.sum_congr rfl fun x hx => walsh_fourth_of_ab hcard hf hAB x ( Finset.mem_singleton.not.mp ( Finset.mem_sdiff.mp hx |>.2 ) ) ] ; simp +decide [ Finset.card_sdiff, * ];
  have := double_sum_fourth_moment hcard f;
  exact mul_left_cancel₀ ( pow_ne_zero 2 ( Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero ) ) ) ( by linarith )

/-! ## The headline: AB ⟹ APN -/

/-
**Every almost-bent permutation is APN.**  (Chabaud–Vaudenay; Carlet Ch. 6.)
No divisibility input and no parity hypothesis on `n` is needed for this
direction.
-/
theorem ab_imp_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f) :
    IsAPN f := by
  intro a ha b
  have h_row : ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
    have h_row : ∀ a : F, a ≠ 0 → ∑ b : F, (diffCount f a b : ℤ) ^ 2 ≥ 2 * (Fintype.card F : ℤ) := by
      intro a ha
      have h_row : ∑ b : F, (diffCount f a b : ℤ) ^ 2 ≥ 2 * ∑ b : F, (diffCount f a b : ℤ) := by
        have h_row : ∀ b : F, (diffCount f a b : ℤ) ^ 2 ≥ 2 * (diffCount f a b : ℤ) := by
          intro b
          by_cases h_even : Even (diffCount f a b);
          · rcases k : diffCount f a b with ( _ | _ | k ) <;> simp_all +decide [ sq, parity_simps ];
            nlinarith only [ h_even.two_dvd ];
          · exact False.elim ( h_even ( diffCount_even f ha b ) );
        simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun b _ => h_row b;
      convert h_row using 1;
      exact congr_arg _ ( mod_cast by rw [ WalshAB.diffCount_sum ] );
    have h_sum : ∑ a : F, ∑ b : F, (diffCount f a b : ℤ) ^ 2 = ∑ a ∈ Finset.univ.erase 0, ∑ b : F, (diffCount f a b : ℤ) ^ 2 + (Fintype.card F : ℤ) ^ 2 := by
      rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), add_comm ];
      rw [ add_comm, WalshAB.diffCount_zero_sq_sum ];
    have h_sum : ∑ a ∈ Finset.univ.erase 0, ∑ b : F, (diffCount f a b : ℤ) ^ 2 = ((Fintype.card F : ℤ) - 1) * (2 * (Fintype.card F : ℤ)) := by
      grind +suggestions;
    contrapose! h_sum;
    refine' ne_of_gt ( lt_of_le_of_lt _ ( Finset.sum_lt_sum ( fun x hx => h_row x ( Finset.ne_of_mem_erase hx ) ) ⟨ a, Finset.mem_erase_of_ne_of_mem ha ( Finset.mem_univ a ), lt_of_le_of_ne ( h_row a ha ) h_sum.symm ⟩ ) ) ; simp +decide [ hcard ];
  have h_row : ∑ b : F, (diffCount f a b : ℤ) * (diffCount f a b - 2) = 0 := by
    simp_all +decide [ mul_sub, ← sq ];
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
    rw [ show ( ∑ i : F, ( diffCount f a i : ℤ ) ) = Fintype.card F from mod_cast WalshAB.diffCount_sum f a ] ; simp +decide [ hcard ] ; ring;
  contrapose! h_row;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ b ) ) );
  · exact mul_pos ( Nat.cast_pos.mpr ( pos_of_gt h_row ) ) ( sub_pos.mpr ( Nat.cast_lt.mpr h_row ) );
  · by_cases h_even : Even (diffCount f a x);
    · rcases h_even with ⟨ k, hk ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +decide ; nlinarith;
    · exact False.elim ( h_even ( diffCount_even f ha x ) )

/-! ## The three-valued value-set characterization -/

/-
**AB ⟺ three-valued spectrum.**  For `n` odd, a function is AB exactly when
its Walsh spectrum at every nonzero frequency lies in `{0, ±2^{(n+1)/2}}`.
-/
omit [DecidableEq F] in
theorem isAB_iff_three_valued {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (f : F → F) :
    IsAB hcard f ↔
      ∀ a : F, a ≠ 0 → ∀ b : F,
        walsh f a b = 0 ∨ walsh f a b = 2 ^ ((n + 1) / 2)
          ∨ walsh f a b = -2 ^ ((n + 1) / 2) := by
  constructor;
  · intro hAB a ha b;
    cases' hAB a ha b with h h;
    · exact Or.inl <| sq_eq_zero_iff.mp h;
    · exact Or.inr ( eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ h, ← pow_mul', Nat.mul_div_cancel' <| even_iff_two_dvd.mp <| by simpa [ parity_simps ] using hodd ] );
  · intro h a ha b;
    rcases h a ha b with ( h | h | h ) <;> rw [ h ] <;> norm_num; all_goals rw [ ← pow_mul, Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hodd ) ) ]

end Vanish.Foundations