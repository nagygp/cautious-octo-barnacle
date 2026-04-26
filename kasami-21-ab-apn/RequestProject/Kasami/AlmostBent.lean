/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Bent (AB) Functions

A function `f : F_{2^n} → F_{2^n}` is **almost bent** (AB) if for every nonzero
`b ∈ F_{2^n}`, the Walsh–Hadamard coefficient `W_f(a,b) = ∑_x χ(ax + b·f(x))`
satisfies `W_f(a,b) ∈ {0, ±2^{(n+1)/2}}` for all `a`.

## Main definitions
- `IsAlmostBent f` — full vectorial AB spectral characterization (all nonzero components)

## Main results
- Fourth moment of AB functions: `∑_a W_f(a)^4 = 2 · (2^n)^3`
- AB implies APN

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.2, Def. 6.26
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000], SIAM J. Discrete Math.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AdditiveCharacter

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### Definition -/

/-- A function `f : F_{2^n} → F_{2^n}` is **almost bent** if for every nonzero
    `b`, the squared Walsh–Hadamard coefficient `W_f(a,b)^2` is either `0` or
    `2^(n+1)`.  This is the standard vectorial AB definition (Carlet 2021, Def. 6.26). -/
def IsAlmostBent {n : ℕ} (f : F2n n → F2n n) : Prop :=
  ∀ (a b : F2n n), b ≠ 0 → wht2 f a b ^ 2 = 0 ∨ wht2 f a b ^ 2 = (2 ^ (n + 1) : ℤ)

/-- Extract the single-component (b=1) AB property. -/
theorem ab_single_component {n : ℕ} (f : F2n n → F2n n) (hf : IsAlmostBent f) (a : F2n n) :
    wht f a ^ 2 = 0 ∨ wht f a ^ 2 = (2 ^ (n + 1) : ℤ) := by
  have h := hf a 1 one_ne_zero
  rwa [wht2_one] at h

/-! ### Fourth moment of AB functions (b=1 component) -/

theorem ab_nonzero_count {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    (Finset.univ.filter fun a : F2n n => wht f a ≠ 0).card = 2 ^ (n - 1) := by
  have hf1 : ∀ a, wht f a ^ 2 = 0 ∨ wht f a ^ 2 = (2 ^ (n + 1) : ℤ) :=
    fun a => ab_single_component f hf a
  have h_parseval : ∑ a : F2n n, (wht f a) ^ 2 = (2 ^ n : ℤ) ^ 2 :=
    wht_parseval hn f
  have h_split_sum : ∑ a : F2n n, (wht f a) ^ 2 =
      ∑ a ∈ Finset.univ.filter (fun a => wht f a ≠ 0), (2 ^ (n + 1) : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hf1 x; split_ifs <;> simp_all +decide
  rcases n with (_ | n) <;> simp_all +decide [pow_succ']
  norm_cast at h_split_sum; nlinarith [pow_pos (zero_lt_two' ℕ) n]

theorem ab_fourth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, wht f a ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  have hf1 : ∀ a, wht f a ^ 2 = 0 ∨ wht f a ^ 2 = (2 ^ (n + 1) : ℤ) :=
    fun a => ab_single_component f hf a
  have h_fourth_moment : ∑ a : F2n n, wht f a ^ 4 =
      ∑ a ∈ Finset.univ.filter fun a : F2n n => wht f a ≠ 0, (2 ^ (n + 1) : ℤ) ^ 2 := by
    rw [Finset.sum_filter, Finset.sum_congr rfl]
    intro a _; specialize hf1 a; split_ifs <;> simp_all +decide [pow_succ, mul_assoc]
  simp_all +decide [Finset.sum_ite]
  rw [ab_nonzero_count hn f hf]; ring
  cases n <;> norm_num [pow_succ, pow_mul] at *; ring

/-! ### Parseval for wht2 components -/

/-
Parseval for each nonzero component: `∑_a W_f(a,b)^2 = (2^n)^2` for b ≠ 0.
-/
theorem wht2_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (b : F2n n) (hb : b ≠ 0) :
    ∑ a : F2n n, wht2 f a b ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  convert Kasami.wht_parseval hn ( fun x => b * f x ) using 1

/-
Nonzero count per component.
-/
theorem ab_nonzero_count_component {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (b : F2n n) (hb : b ≠ 0) :
    (Finset.univ.filter fun a : F2n n => wht2 f a b ≠ 0).card = 2 ^ (n - 1) := by
  have h_parseval : ∑ a : F2n n, (wht2 f a b) ^ 2 = (2 ^ n : ℤ) ^ 2 := by
    exact?;
  -- From the AB condition, each (wht2 f a b)^2 ∈ {0, 2^{n+1}}.
  have h_ab_cond : ∀ a : F2n n, (wht2 f a b) ^ 2 = 0 ∨ (wht2 f a b) ^ 2 = 2 ^ (n + 1) := by
    exact fun a => hf a b hb;
  -- By Parseval's identity, we have $\sum_{a} (wht2 f a b)^2 = (2^n)^2$.
  have h_parseval : (∑ a : F2n n, if wht2 f a b = 0 then 0 else 2 ^ (n + 1)) = (2 ^ n : ℤ) ^ 2 := by
    convert h_parseval using 2;
    cases h_ab_cond ‹_› <;> aesop;
  cases n <;> simp_all +decide [ pow_succ', Finset.sum_ite ];
  norm_cast at *; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ‹_› ] ;

/-
Fourth moment per component.
-/
theorem ab_fourth_moment_component {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (b : F2n n) (hb : b ≠ 0) :
    ∑ a : F2n n, wht2 f a b ^ 4 = 2 * (2 ^ n : ℤ) ^ 3 := by
  -- Each nonzero (wht2 f a b)^4 = (2^{n+1})^2, and the count of nonzero values is 2^{n-1}.
  have h_count : (Finset.univ.filter fun a : F2n n => wht2 f a b ≠ 0).card * (2 ^ (n + 1) : ℤ) ^ 2 = 2 * (2 ^ n : ℤ) ^ 3 := by
    rw [ ab_nonzero_count_component hn f hf b hb ] ; ring;
    cases n <;> norm_num [ pow_succ, pow_mul ] at * ; ring;
  rw [ ← h_count, Finset.sum_congr rfl fun x hx => ?_ ];
  any_goals exact fun x => if wht2 f x b = 0 then 0 else ( 2 ^ ( n + 1 ) ) ^ 2;
  · simp +decide [ Finset.sum_ite ];
  · cases hf x b hb <;> simp_all +decide [ pow_succ' ];
    grind

/-! ### Derivative distribution -/

/-- The derivative distribution: `N_f(a,b) = |{x : f(x+a) + f(x) = b}|`. -/
noncomputable def derivCount {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card

/-- The sum ∑_b N_f(a,b) = |F|. -/
theorem derivCount_sum {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, derivCount f a b = Fintype.card (F2n n) := by
  unfold derivCount
  simp only [Finset.card_filter]
  rw [← Finset.card_univ, Finset.sum_comm]
  simp

/-
Solutions of `f(x+a)+f(x)=b` come in pairs `{x, x+a}` when `a ≠ 0`.
-/
theorem derivCount_even {n : ℕ} (f : F2n n → F2n n) (a : F2n n) (ha : a ≠ 0)
    (b : F2n n) : Even (derivCount f a b) := by
  -- Consider the set S of solutions to f(x+a) + f(x) = b.
  set S := Finset.univ.filter (fun x => f (x + a) + f x = b) with hS_def
  have hS_card : derivCount f a b = Finset.card S := by
    rfl;
  -- The map $x \mapsto x + a$ is an involution on $S$, meaning it pairs elements in $S$.
  have h_inv : ∀ x ∈ S, x + a ∈ S := by
    grind
  have h_inv_inj : ∀ x ∈ S, x + a ≠ x := by
    aesop
  have h_inv_card : ∃ T : Finset (Finset (F2n n)), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ u ∈ T, t ≠ u → Disjoint t u) ∧ (S = Finset.biUnion T id) := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) S, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind +locals;
    · ext x; simp [Finset.mem_biUnion, Finset.mem_image];
      grind +locals;
  obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_inv_card; rw [ hS_card, hT₃, Finset.card_biUnion ] <;> aesop;

/-
For even N(b) with ∑ N(b) = 2^n, if ∑ N(b)² ≤ 2^{n+1} then each N(b) ≤ 2.
-/
theorem even_sum_sq_bound {n : ℕ} (hn : n ≠ 0)
    (N : F2n n → ℕ) (h_even : ∀ b, Even (N b))
    (h_sum : ∑ b : F2n n, N b = 2 ^ n)
    (h_sq : ∑ b : F2n n, (N b) ^ 2 ≤ 2 ^ (n + 1)) :
    ∀ b : F2n n, N b ≤ 2 := by
  contrapose! h_sq; simp_all +decide [ pow_succ', Finset.sum_add_distrib ] ;
  obtain ⟨ b, hb ⟩ := h_sq;
  have h_sq_ge : ∑ x, N x ^ 2 ≥ N b ^ 2 + ∑ x ∈ Finset.univ.erase b, 2 * N x := by
    rw [ ← Finset.add_sum_erase _ _ ( Finset.mem_univ b ) ];
    gcongr;
    rename_i x hx; specialize h_even x; rcases h_even with ⟨ k, hk ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ ] ; nlinarith;
  simp_all +decide [ ← sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ b ), add_comm ] at h_sum ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) n ]

/-! ### Wiener-Khinchin: autocorrelation ↔ Walsh spectrum -/

/-- R_a(c) = ∑_x χ(c · (f(x+a) + f(x))) is the derivative character sum. -/
noncomputable def derivCharSum {n : ℕ} (f : F2n n → F2n n) (a c : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (c * (f (x + a) + f x))

/-- R_a(0) = 2^n. -/
theorem derivCharSum_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    derivCharSum f a 0 = 2 ^ n := by
  simp [derivCharSum, chi_zero, F2n.card n hn]

/-
Parseval for derivative character sums:
    2^n · ∑_b N_a(b)^2 = ∑_c R_a(c)^2.
-/
theorem deriv_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    (2 ^ n : ℤ) * ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 =
    ∑ c : F2n n, (derivCharSum f a c) ^ 2 := by
  unfold derivCharSum;
  -- Expand the square and sum over c.
  have h_expand : ∑ c : F2n n, (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, ∑ c : F2n n, chi n (c * (f (x + a) + f x - (f (y + a) + f y))) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, Finset.sum_mul];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun x hx => Finset.sum_comm.trans ( Finset.sum_congr rfl fun y hy => _ ) );
    simp +decide [ ← chi_add, mul_sub ];
    rw [ ← Equiv.sum_comp ( Equiv.neg ( F2n n ) ) ] ; simp +decide [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ];
  -- Apply character orthogonality to the inner sum.
  have h_orthogonality : ∀ x y : F2n n, ∑ c : F2n n, chi n (c * (f (x + a) + f x - (f (y + a) + f y))) = if f (x + a) + f x = f (y + a) + f y then (2 ^ n : ℤ) else 0 := by
    intro x y; split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
    · rw [ F2n.card n hn, chi_zero ] ; norm_num;
    · have := Kasami.chi_orthogonality hn ( f ( x + a ) + f x - ( f ( y + a ) + f y ) ) ( sub_ne_zero_of_ne ‹_› ) ; simp_all +decide [ mul_comm ] ;
  simp_all +decide [ Finset.sum_ite ];
  simp +decide [ mul_comm, Finset.mul_sum _ _ _, derivCount ];
  simp +decide only [Finset.card_filter, sq];
  simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero];
  simp +decide only [← Finset.mul_sum _ _ _];
  simp +decide only [Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ];
  simp +decide [ Finset.sum_ite ];
  simp +decide only [eq_comm]

/-
Wiener-Khinchin: ∑_a R_a(c)^2 = (1/2^n) ∑_{a'} W_f(a',c)^4.
    More precisely: 2^n · ∑_a R_a(c)^2 = ∑_{a'} (wht2 f a' c)^4.
-/
theorem wiener_khinchin_fourth {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (c : F2n n) :
    (2 ^ n : ℤ) * ∑ a : F2n n, (derivCharSum f a c) ^ 2 =
    ∑ a' : F2n n, (wht2 f a' c) ^ 4 := by
  -- By definition of $wht2$, we know that $(wht2 f a' c)^2 = \sum_{u} \chi(a'u) R_u(c)$.
  have h_wht2_sq : ∀ a' : F2n n, (wht2 f a' c) ^ 2 = ∑ u : F2n n, chi n (a' * u) * derivCharSum f u c := by
    intro a';
    -- By definition of $wht2$, we can expand $(wht2 f a' c)^2$ as $\sum_{x,y} \chi(a'(x+y)) \chi(c(f(x)+f(y)))$.
    have h_expand : (wht2 f a' c) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, chi n (a' * (x + y)) * chi n (c * (f x + f y)) := by
      simp +decide only [wht2, sq, Finset.mul_sum _ _ _, Finset.sum_mul];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← chi_add ] ; rw [ ← chi_add ] ; ring );
    -- By changing variables $u = x + y$, we can rewrite the double sum as $\sum_{u} \chi(a'u) \sum_{x} \chi(c(f(x) + f(x+u)))$.
    have h_change_var : ∑ x : F2n n, ∑ y : F2n n, chi n (a' * (x + y)) * chi n (c * (f x + f y)) = ∑ u : F2n n, chi n (a' * u) * ∑ x : F2n n, chi n (c * (f x + f (x + u))) := by
      have h_change_var : ∀ x : F2n n, ∑ y : F2n n, chi n (a' * (x + y)) * chi n (c * (f x + f y)) = ∑ u : F2n n, chi n (a' * u) * chi n (c * (f x + f (x + u))) := by
        intro x; rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; simp +decide [ add_comm x ] ;
        simp +decide [ add_assoc, F2n.add_self ];
      simp +decide only [h_change_var, Finset.mul_sum _ _ _];
      rw [ Finset.sum_comm ];
    simp_all +decide [ derivCharSum ];
    simp +decide only [add_comm];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a' : F2n n, (wht2 f a' c) ^ 4 = ∑ u : F2n n, ∑ v : F2n n, derivCharSum f u c * derivCharSum f v c * ∑ a' : F2n n, chi n (a' * (u + v)) := by
    have h_fubini : ∑ a' : F2n n, (wht2 f a' c) ^ 4 = ∑ a' : F2n n, (∑ u : F2n n, chi n (a' * u) * derivCharSum f u c) * (∑ v : F2n n, chi n (a' * v) * derivCharSum f v c) := by
      exact Finset.sum_congr rfl fun _ _ => by rw [ ← h_wht2_sq ] ; ring;
    simp +decide only [h_fubini, mul_comm, Finset.mul_sum _ _ _, mul_left_comm];
    simp +decide only [mul_add, mul_comm, chi_add];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By orthogonality, $\sum_{a'} \chi(a'(u+v)) = 2^n$ if $u=v$, and $0$ otherwise.
  have h_orthogonality : ∀ u v : F2n n, ∑ a' : F2n n, chi n (a' * (u + v)) = if u = v then (2 ^ n : ℤ) else 0 := by
    intro u v; split_ifs <;> simp_all +decide [ mul_comm ] ;
    · rw [ chi_zero ] ; norm_num [ F2n.card n hn ];
    · convert chi_orthogonality hn ( u + v ) ( add_eq_zero_iff_eq_neg.not.mpr <| by aesop ) using 1;
      ac_rfl;
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_two ]

/-! ### AB → APN proof -/

/-
For full AB, ∑_a R_a(c)^2 = 2^{2n+1} for each c ≠ 0.
-/
theorem ab_autocorr_sq_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (c : F2n n) (hc : c ≠ 0) :
    ∑ a : F2n n, (derivCharSum f a c) ^ 2 = (2 ^ (2 * n + 1) : ℤ) := by
  have := wiener_khinchin_fourth hn f c;
  exact mul_left_cancel₀ ( pow_ne_zero n two_ne_zero ) ( by rw [ this, ab_fourth_moment_component hn f hf c hc ] ; ring )

/-
Total second moment of derivatives from full AB.
-/
theorem ab_total_deriv_sq_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    (2 ^ n : ℤ) * ∑ a : F2n n, (∑ b : F2n n, (derivCount f a b : ℤ) ^ 2) =
    (2 ^ n : ℤ) * ((2 ^ n : ℤ) ^ 2 + ((2 : ℤ) ^ n - 1) * 2 ^ (n + 1)) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ c : F2n n, (derivCharSum f a c) ^ 2 = ∑ c : F2n n, ∑ a : F2n n, (derivCharSum f a c) ^ 2 := by
    exact Finset.sum_comm;
  -- Apply the results from ab_autocorr_sq_sum and derivCharSum_zero to split the sum.
  have h_split : ∑ c : F2n n, ∑ a : F2n n, (derivCharSum f a c) ^ 2 = (2 ^ (3 * n) : ℤ) + (2 ^ n - 1) * (2 ^ (2 * n + 1) : ℤ) := by
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
    congr 1;
    · rw [ Finset.sum_congr rfl fun _ _ => by rw [ derivCharSum_zero hn f ] ] ; norm_num ; ring;
      rw [ F2n.card ] ; ring;
      · norm_cast ; ring;
      · assumption;
    · rw [ Finset.sum_congr rfl fun x hx => ab_autocorr_sq_sum hn f hf x <| by aesop ] ; norm_num [ Finset.card_sdiff, Finset.card_singleton, F2n.card n hn ];
  convert h_fubini.trans h_split using 1;
  · rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun _ _ => mod_cast deriv_parseval hn f _;
  · ring

/-
Each ∑_b N_a(b)^2 = 2^{n+1} for a ≠ 0 under full AB.
-/
theorem ab_deriv_sq_eq {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f)
    (a : F2n n) (ha : a ≠ 0) :
    ∑ b : F2n n, (derivCount f a b) ^ 2 = 2 ^ (n + 1) := by
  -- Apply the theorem that states each term in the sum is at least $2^{n+1}$.
  have h_lower_bound : ∀ a : F2n n, a ≠ 0 → ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 ≥ 2 ^ (n + 1) := by
    intro a ha
    have h_even : ∀ b : F2n n, Even (derivCount f a b) := by
      exact?
    have h_sum : ∑ b : F2n n, (derivCount f a b : ℤ) = 2 ^ n := by
      convert derivCount_sum f a;
      rw [ ← @Nat.cast_inj ℤ ] ; norm_num [ F2n.card n hn ];
    have h_support : (Finset.univ.filter fun b : F2n n => derivCount f a b ≠ 0).card ≤ 2 ^ (n - 1) := by
      have h_support : ∑ b ∈ Finset.univ.filter fun b : F2n n => derivCount f a b ≠ 0, (derivCount f a b : ℤ) ≥ 2 * (Finset.univ.filter fun b : F2n n => derivCount f a b ≠ 0).card := by
        have h_support : ∀ b ∈ Finset.univ.filter fun b : F2n n => derivCount f a b ≠ 0, (derivCount f a b : ℤ) ≥ 2 := by
          exact fun b hb => mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( even_iff_two_dvd.mp ( h_even b ) );
        simpa [ mul_comm ] using Finset.sum_le_sum h_support;
      rcases n <;> simp_all +decide [ pow_succ' ];
      rw [ Finset.sum_filter_of_ne ] at h_support <;> norm_cast at * ; aesop;
      aesop;
    have h_cauchy_schwarz : (∑ b : F2n n, (derivCount f a b : ℤ)) ^ 2 ≤ (Finset.univ.filter fun b : F2n n => derivCount f a b ≠ 0).card * ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 := by
      have h_cauchy_schwarz : ∀ (s : Finset (F2n n)) (g : F2n n → ℝ), (∑ b ∈ s, g b) ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, g b ^ 2 := by
        exact?;
      convert h_cauchy_schwarz ( Finset.univ.filter fun b => derivCount f a b ≠ 0 ) ( fun b => derivCount f a b ) using 1 ; norm_num [ Finset.sum_filter_of_ne ];
      norm_cast;
    rcases n <;> simp_all +decide [ pow_succ' ];
    nlinarith [ pow_pos ( zero_lt_two' ℤ ) ‹_›, show ( Finset.card ( Finset.filter ( fun b => ¬derivCount f a b = 0 ) Finset.univ ) : ℤ ) ≤ 2 ^ ‹_› by exact_mod_cast h_support ];
  have h_sum_eq : ∑ a ∈ Finset.univ.erase 0, ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 = (2 ^ n - 1) * 2 ^ (n + 1) := by
    have := ab_total_deriv_sq_sum hn f hf;
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ] at this;
    rw [ Finset.sum_eq_single 0 ] at this <;> norm_num at *;
    · rw [ show derivCount f 0 0 = 2 ^ n from ?_ ] at this;
      · norm_num at * ; linarith;
      · unfold derivCount; simp +decide [ F2n.card n hn ] ;
    · unfold derivCount; aesop;
  contrapose! h_sum_eq;
  refine' ne_of_gt ( lt_of_le_of_lt _ ( Finset.sum_lt_sum _ _ ) );
  rotate_left;
  use fun _ => 2 ^ ( n + 1 );
  · aesop;
  · exact ⟨ a, Finset.mem_erase_of_ne_of_mem ha ( Finset.mem_univ a ), lt_of_le_of_ne ( h_lower_bound a ha ) ( Ne.symm <| mod_cast h_sum_eq ) ⟩;
  · norm_num [ F2n.card n hn ]

/-! ### AB implies APN -/

/-- An AB function is also APN (almost perfect nonlinear).
    For any `a ≠ 0` and `b`, the equation `f(x+a) + f(x) = b`
    has at most 2 solutions.

    **Proof**: From full AB, the total ∑_{a≠0} ∑_b N_a(b)^2 = (2^n-1)·2^{n+1}.
    Each term ≥ 2^{n+1} (Cauchy-Schwarz + even multiplicities). So each = 2^{n+1}.
    Then `even_sum_sq_bound` gives N_a(b) ≤ 2. -/
theorem ab_implies_apn {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2 := by
  intro a ha b
  apply even_sum_sq_bound hn (fun b => derivCount f a b)
    (fun b => derivCount_even f a ha b)
    (by rw [derivCount_sum, F2n.card n hn])
    (by exact Nat.le_of_eq (ab_deriv_sq_eq hn f hf a ha))

end
end Kasami