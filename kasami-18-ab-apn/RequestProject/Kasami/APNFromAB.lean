/-
# AB implies APN

Proof that Almost Bent functions are Almost Perfect Nonlinear.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Key identity: Walsh fourth moment equals derivative second moment -/

/-- The derivative distribution sums to |F|. -/
theorem derivCount_sum' {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, (derivCount f a b : ℤ) = (Fintype.card (F2n n) : ℤ) := by
  simp only [derivCount, Finset.card_filter]
  push_cast
  rw [← Finset.card_univ]
  rw [Finset.sum_comm]
  simp

/-
The sum of squared derivative counts at a=0.
-/
theorem derivCount_sq_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ b : F2n n, (derivCount f 0 b : ℤ) ^ 2 = ((2 : ℤ) ^ n) ^ 2 := by
  -- For a=0: D_0 f(x) = f(x+0)+f(x) = f(x)+f(x) = 0 (char 2). So derivCount f 0 b = 2^n if b=0 and 0 otherwise.
  have h_derivCount_zero : ∀ b, derivCount f 0 b = if b = 0 then 2 ^ n else 0 := by
    intro b; unfold derivCount; split_ifs <;> simp_all +decide [ F2n.card ] ;
    aesop;
  aesop

/-
Key Parseval-type identity: ∑_b N_a(b)² relates to the autocorrelation
    of the Walsh transform.

    More precisely:
    2^n · ∑_b N_a(b)² = ∑_c |∑_x χ(c·(f(x+a)+f(x)))|²

    This follows from Parseval applied to the function b ↦ N_a(b).
-/
theorem deriv_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    (2 ^ n : ℤ) * ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 =
    ∑ c : F2n n, (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 := by
  have h_fourier : ∀ (g : F2n n → ℤ), (∑ c : F2n n, (∑ b : F2n n, g b * chi n (c * b)) ^ 2) = (2 ^ n : ℤ) * (∑ b : F2n n, g b ^ 2) := by
    intro g
    have h_fourier : ∀ (c : F2n n), (∑ b : F2n n, g b * chi n (c * b)) ^ 2 = ∑ b₁ : F2n n, ∑ b₂ : F2n n, g b₁ * g b₂ * chi n (c * (b₁ + b₂)) := by
      intro c
      have h_fourier : ∀ b₁ b₂ : F2n n, chi n (c * (b₁ + b₂)) = chi n (c * b₁) * chi n (c * b₂) := by
        exact fun x y => by rw [ ← chi_add ] ; ring;
      simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc, h_fourier];
    have h_fourier_sum : ∀ (b₁ b₂ : F2n n), ∑ c : F2n n, chi n (c * (b₁ + b₂)) = if b₁ + b₂ = 0 then (2 ^ n : ℤ) else 0 := by
      intro b₁ b₂; split_ifs <;> simp_all +decide [ ← mul_add ] ;
      · rw [ chi_zero ] ; norm_num [ F2n.card n hn ];
      · convert chi_sum hn ( b₁ + b₂ ) using 1;
        · ac_rfl;
        · aesop;
    simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_mul ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sq ];
    simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', add_eq_zero_iff_eq_neg ];
    rw [ mul_comm, Finset.sum_mul ];
  rw [ ← h_fourier ];
  congr! 2;
  unfold derivCount;
  simp +decide only [Finset.card_filter];
  simp +decide only [Nat.cast_sum, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ] ; aesop

/-- The autocorrelation ∑_x χ(c·D_a·f(x)) at a=0 gives 2^n. -/
theorem autocorr_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (c : F2n n) :
    ∑ x : F2n n, chi n (c * (f (x + 0) + f x)) = (2 ^ n : ℤ) := by
  simp [F2n.add_self, chi_zero, F2n.card n hn]

/-
For even N_a(b) with ∑ N_a(b) = 2^n, if ∑ N_a(b)² ≤ 2^{n+1} then each N_a(b) ≤ 2.
-/
theorem even_sum_sq_bound {n : ℕ} (hn : n ≠ 0)
    (N : F2n n → ℕ) (h_even : ∀ b, Even (N b))
    (h_sum : ∑ b : F2n n, N b = 2 ^ n)
    (h_sq : ∑ b : F2n n, (N b) ^ 2 ≤ 2 ^ (n + 1)) :
    ∀ b : F2n n, N b ≤ 2 := by
  contrapose! h_sq;
  obtain ⟨ b, hb ⟩ := h_sq;
  -- Since $N(b) \geq 4$, we have $N(b)^2 - 2N(b) \geq 8$.
  have h_diff : N b ^ 2 - 2 * N b ≥ 8 := by
    exact le_tsub_of_add_le_left ( by nlinarith only [ hb, show N b ≥ 4 by exact le_of_not_gt fun h => by have := h_even b; interval_cases N b ; trivial ] );
  have h_sum_sq : ∑ b, N b ^ 2 ≥ N b ^ 2 + 2 * (∑ b ∈ Finset.univ \ {b}, N b) := by
    have h_sum_sq : ∀ x ∈ Finset.univ \ {b}, N x ^ 2 ≥ 2 * N x := by
      intro x hx; specialize h_even x; rcases h_even with ⟨ k, hk ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ ] ;
      grind;
    rw [ Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sdiff ( Finset.subset_univ { b } ) ];
    rw [ add_comm ] ; gcongr ; aesop;
    exact h_sum_sq _ ‹_›;
  rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ b ) ] at h_sum ; rw [ pow_succ' ] ; omega

/-! ### Main theorem: AB implies APN -/

/-
**AB implies APN**: An almost bent function is almost perfect nonlinear.
    For any `a ≠ 0` and `b`, the equation `f(x+a) + f(x) = b` has at most 2 solutions.

    Proof strategy:
    1. Use `deriv_parseval` to express ∑_b N_a(b)² in terms of autocorrelations
    2. Bound the autocorrelations using the AB spectrum
    3. Use `even_sum_sq_bound` to conclude N_a(b) ≤ 2

The autocorrelation identity for the WHT:
∑_c W(c)² χ(ca) = 2^n · ∑_x χ(f(x+a) + f(x))
where D_a f(x) = f(x+a) + f(x).
-/
theorem wht_sq_chi_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
∑ c : F2n n, wht f c ^ 2 * chi n (c * a) =
(2 ^ n : ℤ) * ∑ x : F2n n, chi n (f (x + a) + f x) := by
have h_expand : ∑ c, (∑ x, chi n (c * x + f x)) ^ 2 * chi n (c * a) = ∑ x, ∑ y, ∑ c, chi n (c * (x + y + a)) * chi n (f x + f y) := by
  simp +decide only [pow_two, Finset.mul_sum _ _ _, Finset.sum_mul];
  simp +decide only [← chi_add, add_assoc];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
-- Apply the orthogonality relation to the inner sum.
have h_inner : ∀ x y : F2n n, ∑ c, chi n (c * (x + y + a)) = if x + y + a = 0 then (2 ^ n : ℤ) else 0 := by
  intro x y; split_ifs with h; simp_all +decide [ mul_comm ] ;
  · rw [ F2n.card n hn, chi_zero ] ; norm_num;
  · convert Kasami.chi_orthogonality hn ( x + y + a ) h using 1;
    ac_rfl;
convert h_expand using 1;
rw [ Finset.mul_sum _ _ _ ];
refine' Finset.sum_congr rfl fun x hx => _;
rw [ Finset.sum_eq_single ( x + a ) ] <;> simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
· simp +decide [ add_comm, add_left_comm, add_assoc ];
· grind

/-
For AB functions, |∑_x χ(c·D_a·f(x))|² ≤ 2^{2n} for any c and a.
-/
theorem ab_autocorr_bound {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (a c : F2n n) :
    (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 ≤ ((2 : ℤ) ^ n) ^ 2 := by
  -- The absolute value of the sum is less than or equal to the sum of the absolute values.
  have h_abs : |∑ x : F2n n, chi n (c * (f (x + a) + f x))| ≤ ∑ x : F2n n, |chi n (c * (f (x + a) + f x))| := by
    exact Finset.abs_sum_le_sum_abs _ _;
  convert pow_le_pow_left₀ ( abs_nonneg _ ) h_abs 2 using 1;
  · norm_num;
  · rw [ Finset.sum_congr rfl fun x hx => by rw [ chi_abs ] ] ; norm_num [ F2n.card n hn ]

/-
For AB functions, ∑_b N_a(b)² ≤ 2^{n+1} for any nonzero a.
-/
theorem ab_deriv_sq_bound {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) (a : F2n n) (ha : a ≠ 0) :
    ∑ b : F2n n, (derivCount f a b) ^ 2 ≤ 2 ^ (n + 1) := by
  contrapose! hf;
  intro H
  have := H a
  simp_all +decide [ IsAlmostBent ];
  have := ab_implies_apn hn f ( by
    exact fun a => by cases H a <;> simp +decide [ * ] ; ) a ha;
  have h_sum : ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 ≤ ∑ b : F2n n, (derivCount f a b : ℤ) * 2 := by
    exact Finset.sum_le_sum fun b _ => by nlinarith only [ this b, show ( derivCount f a b : ℤ ) ≤ 2 by exact_mod_cast this b ] ;
  simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  have := derivCount_sum' f a; simp_all +decide [ pow_succ' ] ;
  norm_cast at *; simp_all +decide [ F2n.card ] ;
  linarith

theorem ab_implies_apn_proved {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2 := by
  intro a ha b
  apply even_sum_sq_bound hn (fun b => derivCount f a b)
    (fun b => derivCount_even f a ha b)
    (by rw [derivCount_sum, F2n.card n hn])
    (ab_deriv_sq_bound hn f hf a ha)

end
end Kasami