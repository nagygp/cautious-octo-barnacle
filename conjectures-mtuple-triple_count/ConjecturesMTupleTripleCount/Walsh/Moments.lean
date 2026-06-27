import ConjecturesMTupleTripleCount.Walsh.Transform

/-!
# Walsh Moments — Parseval, Differential Spectrum, Fourth Moment

## Definitions
- `IsAB`: Almost Bent property
- `IsAPN`: APN property (cardinality form)
- `diffCount`: Differential count N_f(a,b)
- `autocorrScaled`: Scaled autocorrelation R_b(u)

## Key results
- `parseval_perm`: Σ_b W(a,b)² = |F|² (Parseval/Plancherel)
- `fourth_moment_apn`: Σ_b W(a,b)⁴ = 2|F|³ for APN power permutations
- `double_sum_fourth_moment`: Σ_{a,b} W⁴ = |F|² · Σ_{a,b} N² (autocorrelation pipeline)
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Layer 4: AB and APN Definitions -/

/-- A function is **Almost Bent (AB)** if Walsh² values ∈ {0, 2^{n+1}}. -/
noncomputable def IsAB {n : ℕ} (_ : Fintype.card F = 2 ^ n) (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    walsh f a b ^ 2 = 0 ∨ walsh f a b ^ 2 = (2 ^ (n + 1) : ℤ)

/-- A function is **APN** if differential equation has ≤ 2 solutions. -/
def IsAPN (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    Fintype.card {x : F // f (x + a) + f x = b} ≤ 2

/-- Differential count N_f(a, b). -/
noncomputable def diffCount (f : F → F) (a b : F) : ℕ :=
  Fintype.card {x : F // f (x + a) + f x = b}

/-! ## Layer 5: Parseval Identity (Plancherel Theorem) -/

theorem parseval_perm {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : Function.Bijective f)
    (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  have := @χ_sum_eq F;
  have h_expand : ∑ b : F, (walsh f a b) ^ 2 = ∑ x : F, ∑ y : F, χ (a * (x + y)) * ∑ b : F, χ (b * (f x + f y)) := by
    have h_expand : ∀ b : F, (walsh f a b) ^ 2 = ∑ x : F, ∑ y : F, χ (a * x + b * f x) * χ (a * y + b * f y) := by
      intro b
      simp [walsh];
      simp +decide only [sq, ← Finset.mul_sum _ _ _, ← sum_mul];
    simp +decide only [h_expand, mul_add, Finset.mul_sum _ _ _, mul_comm];
    simp +decide only [← χ_mul, add_comm];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  have h_inner : ∀ x y : F, ∑ b : F, χ (b * (f x + f y)) = if f x + f y = 0 then (Fintype.card F : ℤ) else 0 := by
    exact fun x y => by simpa only [ mul_comm ] using this ( f x + f y ) ;
  have h_bijective : ∀ x y : F, f x + f y = 0 ↔ x = y := by
    simp +decide [ add_eq_zero_iff_eq_neg, hf.injective.eq_iff ];
    intro x y; rw [ show -f y = f y from _ ] ; rw [ hf.injective.eq_iff ] ;
    grind;
  simp_all +decide [ sq, Finset.sum_ite ];
  simp +decide [ ← hcard, two_mul, χ ];
  simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
  exact_mod_cast hcard

/-! ## Layer 6: Differential Spectrum -/

/-- Total differential count = |F|. -/
theorem diffCount_sum (f : F → F) (a : F) :
    ∑ b : F, diffCount f a b = Fintype.card F := by
  unfold diffCount; simp +decide [ Fintype.card_subtype ] ;
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ] ; aesop;

/-- For APN: Σ_b N(a,b)² = 2·|F|. -/
theorem diffCount_sq_sum_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
  have h_diffCount_range : ∀ b : F, diffCount f a b ≤ 2 := by
    exact fun b => hf a ha b;
  have h_diffCount_sq : ∀ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (diffCount f a b : ℤ) := by
    intro b
    by_cases h_diffCount_zero : diffCount f a b = 1;
    · obtain ⟨ x, hx ⟩ := Fintype.card_eq_one_iff.mp h_diffCount_zero;
      simp_all +decide [ Subtype.ext_iff ];
      grind;
    · have := h_diffCount_range b; interval_cases _ : diffCount f a b <;> simp_all +decide ;
  simp +decide only [h_diffCount_sq];
  rw_mod_cast [ ← Finset.mul_sum _ _ _, diffCount_sum ]

/-! ## Layer 6.5: Autocorrelation Infrastructure -/

/-- The scaled autocorrelation: `R_b(u) = ∑_x χ(b · (f(x+u) + f(x)))`. -/
noncomputable def autocorrScaled (f : F → F) (b u : F) : ℤ :=
  ∑ x : F, χ (b * (f (x + u) + f x))

/-- **Step 1**: W(a,b)² = ∑_u χ(a·u) · R_b(u). -/
theorem walsh_sq_eq_autocorr_sum (f : F → F) (a b : F) :
    walsh f a b ^ 2 = ∑ u : F, χ (a * u) * autocorrScaled f b u := by
  unfold walsh autocorrScaled; simp +decide [ Finset.sum_mul _ _ _, pow_two ] ;
  simp +decide only [χ_mul, Finset.mul_sum _ _ _, ← sum_product', mul_add];
  refine' Finset.sum_bij ( fun x _ => ( x.2 + x.1, x.2 ) ) _ _ _ _ <;> simp +decide [ mul_add, add_mul, χ_mul ];
  · aesop;
  · exact fun a b => ⟨ a - b, by ring ⟩;
  · intro x y; rw [ show y + ( y + x ) = x by ring_nf; simp +decide [ CharTwo.two_eq_zero ] ] ; ring;

/-- **Step 2 (Wiener-Khinchin)**: ∑_a W(a,b)⁴ = |F| · ∑_u R_b(u)². -/
theorem walsh_fourth_sum_a (f : F → F) (b : F) :
    ∑ a : F, walsh f a b ^ 4 =
      (Fintype.card F : ℤ) * ∑ u : F, autocorrScaled f b u ^ 2 := by
  have h_expand : ∀ a : F, (walsh f a b) ^ 4 = (∑ u : F, χ (a * u) * autocorrScaled f b u) ^ 2 := by
    exact fun a => by rw [ ← walsh_sq_eq_autocorr_sum ] ; ring;
  simp +decide only [h_expand, mul_comm, sq];
  have h_combine : ∀ a u v : F, χ (a * u) * χ (a * v) = χ (a * (u + v)) := by
    simp +decide [ mul_add, χ_mul ];
  have h_sum_a : ∀ u v : F, ∑ a : F, χ (a * (u + v)) = if u + v = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp +decide only [mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun u hu => _;
  rw [ Finset.sum_comm ];
  rw [ Finset.sum_eq_single u ] <;> simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  · simp +decide [ ← two_mul, CharTwo.two_eq_zero ] ; ring;
  · grind

/-- **Step 3 (Second Parseval)**: ∑_b R_b(u)² = |F| · ∑_c N(u,c)². -/
theorem autocorr_sq_sum_b (f : F → F) (u : F) :
    ∑ b : F, autocorrScaled f b u ^ 2 =
      (Fintype.card F : ℤ) * ∑ c : F, (diffCount f u c : ℤ) ^ 2 := by
  unfold autocorrScaled;
  simp +decide only [pow_two, sum_mul _ _ _];
  have h_fubini : ∑ x : F, ∑ i : F, ∑ j : F, χ (x * (f (i + u) + f i)) * χ (x * (f (j + u) + f j)) = ∑ i : F, ∑ j : F, ∑ x : F, χ (x * (f (i + u) + f i + f (j + u) + f j)) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro x hx; rw [ Finset.sum_comm ] ; congr; ext y; congr; ext z; rw [ ← χ_mul ] ; ring;
  have h_inner : ∀ i j : F, ∑ x : F, χ (x * (f (i + u) + f i + f (j + u) + f j)) = if f (i + u) + f i = f (j + u) + f j then (Fintype.card F : ℤ) else 0 := by
    intro i j; split_ifs with h; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
    · simp +decide [ add_assoc, add_left_comm, add_comm ];
      rw [ ← add_assoc, ← two_mul, ← two_mul ];
      rw [ show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ] ; simp +decide [ χ ] ;
    · convert χ_sum_eq ( f ( i + u ) + f i + f ( j + u ) + f j ) using 1 ; ring;
      · ac_rfl;
      · grind;
  simp_all +decide [ Finset.sum_ite ];
  convert h_fubini using 1;
  · simp +decide only [Finset.mul_sum _ _ _];
  · simp +decide only [diffCount, Fintype.card_subtype, mul_comm];
    simp +decide only [card_filter];
    simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite ];
    simp +decide only [eq_comm, mul_comm]

/-- N(0,0) = |F|. -/
theorem diffCount_zero_zero (f : F → F) :
    diffCount f 0 0 = Fintype.card F := by
  unfold diffCount; simp only [add_zero]
  rw [Fintype.card_subtype]; simp [CharTwo.add_self_eq_zero, Finset.card_univ]

/-- N(0,b) = 0 for b ≠ 0. -/
theorem diffCount_zero_ne (f : F → F) (b : F) (hb : b ≠ 0) :
    diffCount f 0 b = 0 := by
  unfold diffCount; rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨x, hx⟩ => by simp [CharTwo.add_self_eq_zero] at hx; exact hb hx.symm⟩

/-- ∑_b N(0,b)² = |F|². -/
theorem diffCount_zero_sq_sum (f : F → F) :
    ∑ b : F, (diffCount f 0 b : ℤ) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  rw [Finset.sum_eq_single (0 : F)]
  · simp [diffCount_zero_zero]
  · intro b _ hb; simp [diffCount_zero_ne f b hb]
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- Total ∑_{u,b} N(u,b)² for APN = q² + (q-1)·2q. -/
theorem diffCount_sq_total_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) :
    ∑ u : F, ∑ b : F, (diffCount f u b : ℤ) ^ 2 =
    (Fintype.card F : ℤ) ^ 2 +
      ((Fintype.card F : ℤ) - 1) * (2 * (Fintype.card F : ℤ)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  rw [diffCount_zero_sq_sum]; congr 1
  rw [Finset.sum_congr rfl (fun u hu => diffCount_sq_sum_apn hcard f hf u
    (Finset.ne_of_mem_erase hu))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [nsmul_eq_mul]; push_cast
  have hq : (1 : ℤ) ≤ Fintype.card F := by exact_mod_cast le_of_lt Fintype.one_lt_card
  rw [Nat.cast_sub (by exact_mod_cast hq)]; ring

/-! ## Layer 7: Fourth Moment (Caramello Bridge) -/

/-- **Double-sum fourth moment identity** (via autocorrelation pipeline):
    `∑_{a,b} W(a,b)⁴ = |F|² · ∑_{a,b} N(a,b)²`. -/
theorem double_sum_fourth_moment {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) :
    ∑ a : F, ∑ b : F, walsh f a b ^ 4 =
      (Fintype.card F : ℤ) ^ 2 * ∑ a : F, ∑ b : F, (diffCount f a b : ℤ) ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [walsh_fourth_sum_a]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [autocorr_sq_sum_b]
  rw [← Finset.mul_sum]; ring

/-- For power permutations: Σ_b W(a,b)⁴ is the same for all a ≠ 0. -/
theorem walsh_pow_fourth_uniform (d : ℕ) (a₁ a₂ : F)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    ∑ b : F, walsh (· ^ d) a₁ b ^ 4 = ∑ b : F, walsh (· ^ d) a₂ b ^ 4 := by
  have h_walsh_pow_scaling : ∀ (a b t : F), t ≠ 0 → walsh (fun x => x ^ d) (a * t) (b * t ^ d) = walsh (fun x => x ^ d) a b := by
    intros a b t ht_ne_zero
    simp (config := { decide := true }) only [walsh];
    convert ( Equiv.sum_comp ( Equiv.mulLeft₀ t ht_ne_zero ) fun x => χ ( a * x + b * x ^ d ) ) using 1 ; simp +decide [ mul_assoc, mul_left_comm ];
    simp +decide only [mul_pow];
  have h_scale : ∀ (b : F), walsh (fun x => x ^ d) a₂ b = walsh (fun x => x ^ d) a₁ (b * (a₁ / a₂) ^ d) := by
    intro b; specialize h_walsh_pow_scaling a₁ ( b * ( a₁ / a₂ ) ^ d ) ( a₂ / a₁ ) ; simp_all +decide [ mul_div_cancel₀ ] ;
    simp_all +decide [ mul_assoc, div_pow ];
  rw [ ← Equiv.sum_comp ( Equiv.mulRight₀ ( ( a₁ / a₂ ) ^ d ) ( by aesop ) ) ] ; simp +decide [ h_scale ]

/-- For APN power permutations: the fourth moment = 2·|F|³. -/
theorem fourth_moment_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (hbij : Function.Bijective (· ^ d : F → F))
    (hapn : IsAPN (· ^ d : F → F)) (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh (· ^ d : F → F) a b ^ 4 =
      2 * (Fintype.card F : ℤ) ^ 3 := by
  have := @double_sum_fourth_moment F;
  have := @diffCount_sq_total_apn F;
  have := @walsh_pow_fourth_uniform F;
  rename_i h₁ h₂;
  specialize h₁ hcard ( fun x => x ^ d );
  have h_uniform : ∑ a' : F, ∑ b : F, walsh (fun x => x ^ d) a' b ^ 4 = (Fintype.card F : ℤ) ^ 4 + (Fintype.card F - 1) * ∑ b : F, walsh (fun x => x ^ d) a b ^ 4 := by
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
    rw [ Finset.sum_congr rfl fun x hx => this d x a ( by aesop ) ha ];
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ *, Finset.card_sdiff ];
    · rw [ walsh_zero_zero ] ; aesop;
    · exact fun b hb => walsh_a_zero_perm _ hbij _ hb;
  rw [ h₂ hcard _ hapn ] at h₁;
  nlinarith [ show ( Fintype.card F : ) > 1 from mod_cast Fintype.one_lt_card ]

end WalshAB
