import RequestProject.BoolFun.Defs

/-!
# AB implies APN

This file proves that every Almost Bent (AB) function is Almost Perfect Nonlinear (APN).

## Proof outline

The proof uses the fourth-moment identity for the Walsh-Hadamard transform:

  ∑_{a,b} W_f(a,b)⁴ = 2^{2n} · ∑_{a,b} δ_f(a,b)²

Under the AB condition, the left-hand side can be computed explicitly:
- For b = 0: W_f(a,0) = 2^n if a = 0, else 0
- For b ≠ 0: W_f(a,b)² ∈ {0, 2^{n+1}}, so W_f(a,b)⁴ = 2^{n+1} · W_f(a,b)²

Using Parseval's identity ∑_a W_f(a,b)² = 2^{2n}, we get:
  ∑_{a,b} W_f(a,b)⁴ = 2^{4n} + (2^n - 1) · 2^{3n+1}

Combining with the fourth-moment identity:
  ∑_{a≠0,b} δ(a,b)² = (2^n - 1) · 2^{n+1} = 2 · ∑_{a≠0,b} δ(a,b)

Since δ(a,b) is always even for a ≠ 0, each term δ(δ-2) ≥ 0, and the sum is 0,
so δ(a,b) ∈ {0, 2} for all a ≠ 0, proving APN.
-/

open Finset BigOperators

set_option maxHeartbeats 800000

-- ============================================================================
-- Walsh at b = 0
-- ============================================================================

/-- W_f(a, 0) = ∑_x χ_a(x) -/
lemma walsh_zero_right {n : ℕ} (f : V n → V n) (a : V n) :
    walsh f a 0 = ∑ x : V n, chi a x := by
  simp [walsh, chi_zero_right]

/-
============================================================================
Parseval's identity
============================================================================

Parseval's identity: ∑_a W_f(a,b)² = (2^n)²
-/
lemma parseval {n : ℕ} (f : V n → V n) (b : V n) :
    ∑ a : V n, walsh f a b ^ 2 = ((2 : ℤ) ^ n) ^ 2 := by
  -- By definition of walsh, we can rewrite the left-hand side as a double sum.
  have h_double_sum : ∑ a : V n, (∑ y : V n, (chi a y) * (chi b (f y))) ^ 2 = ∑ x : V n, ∑ y : V n, (∑ a : V n, (chi a x) * (chi a y)) * (chi b (f x)) * (chi b (f y)) := by
    simp +decide only [sq, Finset.mul_sum _ _ _, sum_mul, mul_assoc];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By the orthogonality of the characters, we know that $\sum_{a} \chi_a(x) \chi_a(y) = 2^n$ if $x = y$ and $0$ otherwise.
  have h_orthogonality : ∀ x y : V n, ∑ a : V n, (chi a x) * (chi a y) = if x = y then (2 ^ n : ℤ) else 0 := by
    intros x y; exact (by
    convert chi_orthogonality x y using 1;
    simp +decide only [chi];
    simp +decide [ dot, mul_comm ]);
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  convert h_double_sum using 1;
  norm_num [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul, chi_sq ];
  norm_num [ ← sq, chi_sq ]

-- ============================================================================
-- Walsh squared as sum of chi * D
-- ============================================================================

/-- The equivalence (x, y) ↔ (x+y, x) on V n × V n -/
def pairEquiv (n : ℕ) : V n × V n ≃ V n × V n where
  toFun := fun ⟨x, y⟩ => ⟨x + y, x⟩
  invFun := fun ⟨d, x⟩ => ⟨x, x + d⟩
  left_inv := by
    intro ⟨x, y⟩; ext <;> simp <;> rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  right_inv := by
    intro ⟨d, x⟩; ext <;> simp <;> rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-
W_f(a,b)² = ∑_d χ_a(d) · D_f(d,b)
-/
lemma walsh_sq_eq {n : ℕ} (f : V n → V n) (a b : V n) :
    walsh f a b ^ 2 = ∑ d : V n, chi a d * D f d b := by
  -- Expand walsh^2 = (∑_x chi a x * chi b (f x))^2 = ∑_x ∑_y (chi a x * chi b (f x)) * (chi a y * chi b (f y)).
  have h_expand : walsh f a b ^ 2 = ∑ x : V n, ∑ y : V n, (chi a x * chi b (f x)) * (chi a y * chi b (f y)) := by
    simp +decide only [walsh, pow_two, sum_mul_sum];
  -- Use chi_mul_chi' to rewrite the product of chi terms.
  have h_rewrite : walsh f a b ^ 2 = ∑ x : V n, ∑ y : V n, (chi a (x + y)) * (chi b (f x + f y)) := by
    convert h_expand using 3;
    rw [ ← chi_mul_chi', ← chi_mul_chi' ];
    ring;
  -- Use Fintype.sum_equiv to change the variables in the double sum.
  have h_change_vars : ∑ x : V n, ∑ y : V n, (chi a (x + y)) * (chi b (f x + f y)) = ∑ d : V n, ∑ x : V n, (chi a d) * (chi b (f x + f (x + d))) := by
    rw [ ← Finset.sum_product' ];
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x.1 + x.2, x.1 ) ) _ _ _ _ <;> simp +decide;
    · aesop;
    · exact fun a b => ⟨ a - b, by simp +decide ⟩;
    · simp +decide [ ← add_assoc ];
  simp_all +decide [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, D ];
  convert h_expand.symm using 3 ; ring

/-
============================================================================
Fourth moment identity (per b)
============================================================================

Per-b fourth moment: ∑_a W_f(a,b)⁴ = 2^n · ∑_d D_f(d,b)²
-/
lemma fourth_moment_per_b {n : ℕ} (f : V n → V n) (b : V n) :
    ∑ a : V n, walsh f a b ^ 4 = (2 : ℤ) ^ n * ∑ d : V n, D f d b ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : V n, (∑ d : V n, chi a d * D f d b) ^ 2 = ∑ d : V n, ∑ d' : V n, (∑ a : V n, chi a d * chi a d') * D f d b * D f d' b := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, sum_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By the orthogonality of the characters, we have $\sum_{a} \chi_a(d) \chi_a(d') = 2^n \delta_{dd'}$.
  have h_orthog : ∀ d d' : V n, ∑ a : V n, chi a d * chi a d' = if d = d' then (2 : ℤ) ^ n else 0 := by
    intros d d'
    have h_orthog : ∑ a : V n, chi a (d + d') = if d = d' then (2 : ℤ) ^ n else 0 := by
      convert sum_chi ( d + d' ) using 1;
      · unfold chi;
        unfold dot; simp +decide [ mul_comm ] ;
      · simp +decide [ add_eq_zero_iff_eq_neg ];
    convert h_orthog using 2;
    exact chi_mul_chi' _ d d';
  convert h_fubini using 1;
  · exact Finset.sum_congr rfl fun _ _ => by rw [ ← walsh_sq_eq ] ; ring;
  · simp +decide [ h_orthog, Finset.mul_sum _ _ _, mul_assoc, sq ]

/-
============================================================================
D squared sum (per d)
============================================================================

∑_b D_f(d,b)² = 2^n · ∑_c δ_f(d,c)²
-/
lemma D_sq_sum {n : ℕ} (f : V n → V n) (d : V n) :
    ∑ b : V n, D f d b ^ 2 = (2 : ℤ) ^ n * ∑ c : V n, (deltaCount f d c : ℤ) ^ 2 := by
  have h_sum_sq : ∑ b : V n, (∑ x : V n, chi b (f (x + d) + f x)) ^ 2 = ∑ x : V n, ∑ y : V n, ∑ b : V n, chi b (f (x + d) + f x + f (y + d) + f y) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_comm.trans ( Finset.sum_congr rfl fun y hy => _ );
    simp +decide only [chi_mul_chi', add_assoc];
  have h_char_sum : ∀ x y : V n, ∑ b : V n, chi b (f (x + d) + f x + f (y + d) + f y) = if f (x + d) + f x = f (y + d) + f y then (2 : ℤ) ^ n else 0 := by
    intro x y
    have h_char_sum : ∀ z : V n, ∑ b : V n, chi b z = if z = 0 then (2 : ℤ) ^ n else 0 := by
      convert sum_chi using 1;
      unfold chi; simp +decide [ dot ] ;
      simp +decide only [mul_comm];
    convert h_char_sum ( f ( x + d ) + f x + f ( y + d ) + f y ) using 2 ; simp +decide [ add_eq_zero_iff_eq_neg ];
    simp +decide [ ← eq_sub_iff_add_eq ];
    simp +decide [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ];
  have h_group : ∑ x : V n, ∑ y : V n, (if f (x + d) + f x = f (y + d) + f y then (2 : ℤ) ^ n else 0) = ∑ c : V n, (Finset.card (Finset.filter (fun x => f (x + d) + f x = c) Finset.univ)) ^ 2 * (2 : ℤ) ^ n := by
    have h_group : ∀ x : V n, ∑ y : V n, (if f (x + d) + f x = f (y + d) + f y then (2 : ℤ) ^ n else 0) = ∑ c : V n, (if f (x + d) + f x = c then (Finset.card (Finset.filter (fun y => f (y + d) + f y = c) Finset.univ)) * (2 : ℤ) ^ n else 0) := by
      intro x; simp +decide [ Finset.sum_ite ] ;
      simp +decide only [eq_comm];
    rw [ Finset.sum_congr rfl fun x hx => h_group x ];
    rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite ];
    exact Finset.sum_congr rfl fun _ _ => by ring;
  simp_all +decide [ mul_comm, Finset.mul_sum _ _ _ ];
  convert h_sum_sq using 1

/-
============================================================================
Global fourth moment identity
============================================================================

Global fourth moment identity: ∑_{a,b} W_f(a,b)⁴ = 2^{2n} · ∑_{a,b} δ_f(a,b)²
-/
theorem global_fourth_moment {n : ℕ} (f : V n → V n) :
    ∑ a : V n, ∑ b : V n, walsh f a b ^ 4 =
    (2 : ℤ) ^ (2 * n) * ∑ a : V n, ∑ b : V n, (deltaCount f a b : ℤ) ^ 2 := by
  -- Apply the fourth moment identity to each term in the sum.
  have h_sum_fourth_moment : ∑ a : V n, ∑ b : V n, walsh f a b ^ 4 = 2 ^ n * ∑ b : V n, ∑ d : V n, D f d b ^ 2 := by
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => fourth_moment_per_b f _ );
  rw [ h_sum_fourth_moment, Finset.sum_comm ];
  simp +decide only [D_sq_sum, pow_mul'];
  simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_left_comm, mul_assoc]

/-
============================================================================
AB-specific computations
============================================================================

Under AB, W_f(a,b)⁴ = 2^{n+1} · W_f(a,b)² for b ≠ 0
-/
lemma ab_fourth_eq_sq {n : ℕ} (f : V n → V n) (hab : IsAB f)
    (a b : V n) (hb : b ≠ 0) :
    walsh f a b ^ 4 = (2 : ℤ) ^ (n + 1) * walsh f a b ^ 2 := by
  cases hab a b hb <;> simp_all +decide [ pow_succ, mul_assoc ]

/-
Under AB, ∑_a W_f(a,b)⁴ = 2^{n+1} · 2^{2n} for b ≠ 0
-/
lemma ab_fourth_moment_sum {n : ℕ} (f : V n → V n) (hab : IsAB f)
    (b : V n) (hb : b ≠ 0) :
    ∑ a : V n, walsh f a b ^ 4 = (2 : ℤ) ^ (n + 1) * (2 : ℤ) ^ (2 * n) := by
  rw [ Finset.sum_congr rfl fun a ha => ab_fourth_eq_sq f hab a b hb ];
  rw [ ← Finset.mul_sum _ _ _, parseval ] ; ring

/-
============================================================================
Combinatorial conclusion
============================================================================

Key combinatorial lemma: if δ is even and ∑δ² = 2·∑δ with δ ≥ 0, then δ ≤ 2
-/
lemma delta_le_two_of_sum_sq {n : ℕ} (f : V n → V n) (a : V n) (ha : a ≠ 0)
    (h_sum_sq : ∑ b : V n, (deltaCount f a b : ℤ) ^ 2 = (2 : ℤ) ^ (n + 1))
    (b : V n) : deltaCount f a b ≤ 2 := by
  have h_delta_le_two : ∑ b : V n, (deltaCount f a b : ℤ) * ((deltaCount f a b : ℤ) - 2) = 0 := by
    simp_all +decide [ mul_sub, ← sq, Finset.sum_mul _ _ _ ];
    rw [ sub_eq_zero, ← Finset.sum_mul _ _ _, sum_deltaCount ] ; ring;
  contrapose! h_delta_le_two;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ b ) ) );
  · nlinarith only [ h_delta_le_two ];
  · by_cases hx : deltaCount f a x ≥ 2;
    · exact mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg_of_le ( mod_cast hx ) );
    · interval_cases _ : deltaCount f a x <;> simp_all +decide;
      exact absurd ( deltaCount_even f a ha x ) ( by simp +decide [ * ] )

/-
============================================================================
The main theorem
============================================================================

**AB implies APN**: Every Almost Bent function is Almost Perfect Nonlinear.
-/
theorem ab_implies_apn {n : ℕ} (f : V n → V n) (hab : IsAB f) : IsAPN f := by
  have h_global_sum_sq : ∑ a : V n, ∑ b : V n, (deltaCount f a b : ℤ) ^ 2 = 2 ^ (2 * n) + (2 ^ n - 1) * 2 ^ (n + 1) := by
    have h_global_sum_sq : ∑ a : V n, ∑ b : V n, (walsh f a b : ℤ) ^ 4 = 2 ^ (4 * n) + (2 ^ n - 1) * 2 ^ (3 * n + 1) := by
      have h_global_fourth_moment : ∑ a : V n, ∑ b : V n, (walsh f a b : ℤ) ^ 4 = ∑ b : V n, (∑ a : V n, (walsh f a b : ℤ) ^ 4) := by
        exact Finset.sum_comm;
      rw [ h_global_fourth_moment, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
      congr 1;
      · rw [ Finset.sum_eq_single 0 ] <;> norm_num [ walsh_zero_right ];
        · ring;
        · exact fun b hb => by rw [ sum_chi ] ; aesop;
      · rw [ Finset.sum_congr rfl fun x hx => ab_fourth_moment_sum f hab x <| by aesop ] ; norm_num [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, card_V ] ; ring;
        norm_num;
    have h_global_sum_sq : ∑ a : V n, ∑ b : V n, (walsh f a b : ℤ) ^ 4 = 2 ^ (2 * n) * ∑ a : V n, ∑ b : V n, (deltaCount f a b : ℤ) ^ 2 := by
      convert global_fourth_moment f using 1;
    exact mul_left_cancel₀ ( pow_ne_zero ( 2 * n ) two_ne_zero ) ( by ring_nf at *; linarith );
  -- From deltaCount_zero_left, ∑_b δ(0,b)^2 = 2^{2n}
  have h_delta_zero_sum_sq : ∑ b : V n, (deltaCount f 0 b : ℤ) ^ 2 = 2 ^ (2 * n) := by
    -- By definition of deltaCount, we know that deltaCount f 0 b = 2^n if b = 0 and 0 otherwise.
    have h_delta_zero : ∀ b : V n, deltaCount f 0 b = if b = 0 then 2 ^ n else 0 := by
      exact fun b => deltaCount_zero_left f b;
    simp_all +decide [ pow_mul' ];
  -- So ∑_{a≠0,b} δ(a,b)^2 = (2^n - 1) * 2^{n+1} = 2 * ∑_{a≠0,b} δ(a,b)
  have h_sum_sq_eq_two_sum : ∑ a : V n, ∑ b : V n, (deltaCount f a b : ℤ) ^ 2 = ∑ b : V n, (deltaCount f 0 b : ℤ) ^ 2 + 2 * ∑ a : V n, ∑ b : V n, (if a = 0 then 0 else deltaCount f a b : ℤ) := by
    have h_sum_sq_eq_two_sum : ∑ a : V n, ∑ b : V n, (if a = 0 then 0 else deltaCount f a b : ℤ) = (2 ^ n - 1) * 2 ^ n := by
      have h_sum_sq_eq_two_sum : ∀ a : V n, a ≠ 0 → ∑ b : V n, (deltaCount f a b : ℤ) = 2 ^ n := by
        exact fun a _ => sum_deltaCount f a;
      simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
    grind;
  -- Since each δ is even and ≥ 0, ∑ δ*(δ-2) = 0 with each term ≥ 0.
  have h_sum_zero : ∑ a : V n, ∑ b : V n, (if a = 0 then 0 else (deltaCount f a b : ℤ) * ((deltaCount f a b : ℤ) - 2)) = 0 := by
    simp_all +decide [ mul_sub, ← sq ];
    simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.sum_add_distrib, ← Finset.sum_mul _ _ _ ];
    linarith;
  -- Since each term in the sum is non-negative, each term must be zero.
  have h_each_zero : ∀ a : V n, ∀ b : V n, a ≠ 0 → (deltaCount f a b : ℤ) * ((deltaCount f a b : ℤ) - 2) = 0 := by
    have h_each_zero : ∀ a : V n, ∀ b : V n, a ≠ 0 → (deltaCount f a b : ℤ) * ((deltaCount f a b : ℤ) - 2) ≥ 0 := by
      intros a b ha
      have h_even : Even (deltaCount f a b) := by
        exact deltaCount_even f a ha b;
      rcases h_even with ⟨ k, hk ⟩ ; norm_num [ hk ] ; ring_nf ;
      rcases k with ( _ | _ | k ) <;> norm_num ; nlinarith only [ ha ] ;
    rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero;
    · intro a b ha; specialize h_sum_zero a; rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero <;> aesop;
    · exact fun a _ => Finset.sum_nonneg fun b _ => by split_ifs <;> simp +decide [ * ] ;
  exact fun a ha b => by nlinarith only [ h_each_zero a b ha ] ;