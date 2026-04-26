/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AB implies APN — Ported from iteration 11

This file proves that every Almost Bent (AB) function over F_{2^n} is
Almost Perfect Nonlinear (APN), using the fourth-moment identity for the
Walsh–Hadamard transform.

## Proof outline

The proof uses the fourth-moment identity:
  ∑_{a,b} W_f(a,b)⁴ = 2^{2n} · ∑_{a,b} δ_f(a,b)²

Under the AB condition, the LHS is computed explicitly. Combined with
∑ δ_f(a,b) = 2^n, we get ∑ δ*(δ-2) = 0 with each term ≥ 0 (since δ is even),
forcing δ ∈ {0, 2}.

## Ported from
- `kasami-11/RequestProject/BoolFun/ABImpliesAPN.lean` (GF(2)^n framework)
- Adapted to `GaloisField 2 n` framework used in kasami-14

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.2
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard

namespace Kasami

open Finset BigOperators Classical

noncomputable section

variable {n : ℕ}

/-! ### Two-argument Walsh–Hadamard transform -/

/-- The two-argument Walsh–Hadamard transform:
    `W_f(a,b) = ∑_x χ(a·x + b·f(x))`. -/
def walshTwo (f : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + b * f x)

/-- `walshTwo f a 1 = wht f a`. -/
theorem walshTwo_eq_wht (f : F2n n → F2n n) (a : F2n n) :
    walshTwo f a 1 = wht f a := by
  simp [walshTwo, wht, one_mul]

/-- `walshTwo f a b = ∑_x χ(a·x) · χ(b·f(x))`. -/
theorem walshTwo_prod (f : F2n n → F2n n) (a b : F2n n) :
    walshTwo f a b = ∑ x : F2n n, chi n (a * x) * chi n (b * f x) := by
  simp [walshTwo, chi_add]

/-- `W_f(a, 0) = ∑_x χ(a·x)`. -/
theorem walshTwo_zero_right (f : F2n n → F2n n) (a : F2n n) :
    walshTwo f a 0 = ∑ x : F2n n, chi n (a * x) := by
  simp [walshTwo]

/-! ### Derivative character sum and differential count -/

/-- The derivative character sum `D_f(d,b) = ∑_x χ(b·(f(x+d) + f(x)))`. -/
def derivChi (f : F2n n → F2n n) (d b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (b * (f (x + d) + f x))

/-- The differential count `δ_f(a,b) = |{x : f(x+a) + f(x) = b}|`. -/
noncomputable def diffCount (f : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card

/-! ### Two-argument Almost Bent (AB) -/

/-- A function f is **Almost Bent** (two-argument, full definition) if
    `W_f(a,b)² ∈ {0, 2^{n+1}}` for all `a` and `b ≠ 0`.
    This is the standard cryptographic definition for vectorial Boolean functions. -/
def IsAB (f : F2n n → F2n n) : Prop :=
  ∀ a b : F2n n, b ≠ 0 → walshTwo f a b ^ 2 = 0 ∨
    walshTwo f a b ^ 2 = (2 : ℤ) ^ (n + 1)

/-! ### Parseval's identity (two-argument) -/

/-
Parseval's identity: `∑_a W_f(a,b)² = (2^n)²`.
-/
theorem walshTwo_parseval (hn : n ≠ 0) (f : F2n n → F2n n) (b : F2n n) :
    ∑ a : F2n n, walshTwo f a b ^ 2 = ((2 : ℤ) ^ n) ^ 2 := by
  exact wht_parseval hn fun x => b * f x

/-! ### Walsh squared identity -/

/-
`W_f(a,b)² = ∑_d χ(a·d) · D_f(d,b)`.
-/
theorem walshTwo_sq_eq (f : F2n n → F2n n) (a b : F2n n) :
    walshTwo f a b ^ 2 = ∑ d : F2n n, chi n (a * d) * derivChi f d b := by
  unfold walshTwo derivChi;
  simp +decide only [pow_two, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; simp +decide [ mul_add, add_assoc, chi_add ] ;
  rw [ Finset.sum_mul _ _ _ ] ; congr ; ext x ; ring;
  rw [ chi_sq ] ; ring

/-! ### Fourth moment identity (per b) -/

/-
Per-b fourth moment: `∑_a W_f(a,b)⁴ = 2^n · ∑_d D_f(d,b)²`.
-/
theorem fourth_moment_per_b (hn : n ≠ 0) (f : F2n n → F2n n) (b : F2n n) :
    ∑ a : F2n n, walshTwo f a b ^ 4 =
    (2 : ℤ) ^ n * ∑ d : F2n n, derivChi f d b ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ d : F2n n, ∑ d' : F2n n, chi n (a * d) * chi n (a * d') * (derivChi f d b) * (derivChi f d' b) = ∑ d : F2n n, ∑ d' : F2n n, (∑ a : F2n n, chi n (a * d) * chi n (a * d')) * (derivChi f d b) * (derivChi f d' b) := by
    simp +decide only [sum_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  convert h_fubini using 1;
  · refine' Finset.sum_congr rfl fun a _ => _;
    rw [ show walshTwo f a b ^ 4 = ( walshTwo f a b ^ 2 ) ^ 2 by ring, walshTwo_sq_eq ];
    simp +decide only [mul_comm, sq, Finset.mul_sum _ _ _, mul_left_comm, mul_assoc];
  · have h_inner : ∀ d d' : F2n n, ∑ a : F2n n, chi n (a * d) * chi n (a * d') = if d = d' then (2 ^ n : ℤ) else 0 := by
      intro d d'; specialize h_fubini; have := chi_inner_product hn d d'; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    simp +decide [ h_inner, Finset.mul_sum _ _ _, mul_assoc, sq ]

/-! ### D² sum identity -/

/-
`∑_b D_f(d,b)² = 2^n · ∑_c δ_f(d,c)²`.
-/
theorem derivChi_sq_sum (hn : n ≠ 0) (f : F2n n → F2n n) (d : F2n n) :
    ∑ b : F2n n, derivChi f d b ^ 2 =
    (2 : ℤ) ^ n * ∑ c : F2n n, (diffCount f d c : ℤ) ^ 2 := by
  have h_expand : ∀ b : F2n n, (derivChi f d b) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, chi n (b * (f (x + d) + f x + f (y + d) + f y)) := by
    intro b
    have h_expand : (derivChi f d b) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, chi n (b * (f (x + d) + f x)) * chi n (b * (f (y + d) + f y)) := by
      simp +decide only [derivChi, sq, sum_mul_sum];
    convert h_expand using 3;
    rw [ ← chi_add ] ; ring;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ b : F2n n, ∑ x : F2n n, ∑ y : F2n n, chi n (b * (f (x + d) + f x + f (y + d) + f y)) = ∑ x : F2n n, ∑ y : F2n n, ∑ b : F2n n, chi n (b * (f (x + d) + f x + f (y + d) + f y)) := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  have h_inner_sum : ∀ x y : F2n n, ∑ b : F2n n, chi n (b * (f (x + d) + f x + f (y + d) + f y)) = if f (x + d) + f x = f (y + d) + f y then (2 ^ n : ℤ) else 0 := by
    intro x y;
    convert chi_sum hn ( f ( x + d ) + f x + f ( y + d ) + f y ) using 1;
    · ac_rfl;
    · grind;
  simp_all +decide [ Finset.sum_ite ];
  have h_group : ∑ x : F2n n, (Finset.card (Finset.filter (fun y => f (x + d) + f x = f (y + d) + f y) Finset.univ) : ℤ) = ∑ c ∈ Finset.image (fun x => f (x + d) + f x) Finset.univ, (Finset.card (Finset.filter (fun x => f (x + d) + f x = c) Finset.univ) : ℤ) ^ 2 := by
    rw [ Finset.sum_image' ];
    simp +contextual [ sq, Finset.sum_filter ];
    simp +decide [ Finset.sum_ite, eq_comm ];
  simp_all +decide [ ← Finset.sum_mul _ _ _, diffCount ];
  rw [ mul_comm, Finset.sum_subset ( Finset.subset_univ _ ) ] ; aesop

/-! ### Global fourth moment identity -/

/-
Global fourth moment: `∑_{a,b} W_f(a,b)⁴ = 2^{2n} · ∑_{a,b} δ_f(a,b)²`.
-/
theorem global_fourth_moment (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, ∑ b : F2n n, walshTwo f a b ^ 4 =
    (2 : ℤ) ^ (2 * n) * ∑ a : F2n n, ∑ b : F2n n, (diffCount f a b : ℤ) ^ 2 := by
  have h_sum : ∑ a : F2n n, ∑ b : F2n n, walshTwo f a b ^ 4 = (2 : ℤ) ^ n * ∑ d : F2n n, ∑ b : F2n n, derivChi f d b ^ 2 := by
    have h_sum : ∑ a : F2n n, ∑ b : F2n n, walshTwo f a b ^ 4 = ∑ b : F2n n, (2 : ℤ) ^ n * ∑ d : F2n n, derivChi f d b ^ 2 := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => fourth_moment_per_b hn f _ ];
    rw [ h_sum, ← Finset.mul_sum _ _ _, Finset.sum_comm ];
  rw [ h_sum, Finset.sum_congr rfl fun d hd => derivChi_sq_sum hn f d ];
  norm_num [ pow_mul', ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring

/-! ### AB-specific computations -/

/-
Under AB, `W_f(a,b)⁴ = 2^{n+1} · W_f(a,b)²` for `b ≠ 0`.
-/
theorem ab_walshTwo_fourth_eq_sq (f : F2n n → F2n n) (hab : IsAB f)
    (a b : F2n n) (hb : b ≠ 0) :
    walshTwo f a b ^ 4 = (2 : ℤ) ^ (n + 1) * walshTwo f a b ^ 2 := by
  cases hab a b hb <;> simp_all +decide [ pow_succ, mul_assoc ]

/-
Under AB, `∑_a W_f(a,b)⁴ = 2^{n+1} · 2^{2n}` for `b ≠ 0`.
-/
theorem ab_walshTwo_fourth_sum (hn : n ≠ 0) (f : F2n n → F2n n) (hab : IsAB f)
    (b : F2n n) (hb : b ≠ 0) :
    ∑ a : F2n n, walshTwo f a b ^ 4 =
    (2 : ℤ) ^ (n + 1) * (2 : ℤ) ^ (2 * n) := by
  have h_sum : ∑ a : F2n n, walshTwo f a b ^ 4 = (2 : ℤ) ^ (n + 1) * ∑ a : F2n n, walshTwo f a b ^ 2 := by
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => ab_walshTwo_fourth_eq_sq f hab x b hb;
  rw [ h_sum, walshTwo_parseval hn f b ] ; ring

/-! ### Counting lemmas -/

/-
`δ_f(0, b) = 2^n` if `b = 0`, else `0`.
-/
theorem diffCount_zero_left (f : F2n n → F2n n) (b : F2n n) :
    diffCount f 0 b = if b = 0 then Fintype.card (F2n n) else 0 := by
  split_ifs <;> simp_all +decide [ Finset.filter_eq', diffCount ];
  aesop

/-
`∑_b δ_f(a,b) = 2^n` (or rather, `Fintype.card (F2n n)`).
-/
theorem diffCount_sum (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, (diffCount f a b : ℤ) = (Fintype.card (F2n n) : ℤ) := by
  norm_cast;
  unfold diffCount;
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ] ; aesop

/-
`δ_f(a,b)` is always even for `a ≠ 0` (involution `x ↦ x + a`).
-/
theorem diffCount_even (f : F2n n → F2n n) (a : F2n n) (ha : a ≠ 0)
    (b : F2n n) : Even (diffCount f a b) := by
  -- By definition of $diffCount$, we know that its value is equal to the cardinality of the set $\{x : F_2^n \mid f(x+a)+f(x) = b\}$.
  set S : Finset (F2n n) := Finset.univ.filter (fun x : F2n n => f (x + a) + f x = b) with hS_def;
  -- Since $a \neq 0$, the map $x \mapsto x + a$ is a fixed-point-free involution on $S$.
  have h_involution : ∀ x ∈ S, x + a ∈ S ∧ x + a ≠ x := by
    grind;
  -- Since $S$ is partitioned into pairs $\{x, x + a\}$, its cardinality is even.
  have h_partition : ∃ T : Finset (Finset (F2n n)), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ u ∈ T, t ≠ u → Disjoint t u) ∧ S = Finset.biUnion T id := by
    use Finset.image (fun x => {x, x + a}) S;
    simp_all +decide [ Finset.disjoint_left ];
    constructor;
    · grind;
    · ext x; aesop;
  obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_partition; rw [ show diffCount f a b = S.card from rfl ] ; rw [ hT₃, Finset.card_biUnion ] <;> aesop;

/-! ### The main theorem -/

/-
**AB implies APN**: Every Almost Bent function (in the two-argument sense)
    is Almost Perfect Nonlinear.
-/
theorem isAB_implies_apn (hn : n ≠ 0) (f : F2n n → F2n n) (hab : IsAB f) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n, diffCount f a b ≤ 2 := by
  -- Apply the global fourth moment identity to the sum over all a and b of (diffCount f a b)^2.
  have h_global_fourth_moment : ∑ a : F2n n, ∑ b : F2n n, (diffCount f a b : ℤ) ^ 2 = 2 ^ (2 * n) + (2 ^ n - 1) * 2 ^ (n + 1) := by
    have h_global_fourth_moment : ∑ a : F2n n, ∑ b : F2n n, (walshTwo f a b : ℤ) ^ 4 = (2 : ℤ) ^ (4 * n) + (2 ^ n - 1) * (2 : ℤ) ^ (3 * n + 1) := by
      have h_lhs : ∑ a : F2n n, ∑ b : F2n n, (walshTwo f a b) ^ 4 = ∑ b : F2n n, (∑ a : F2n n, (walshTwo f a b) ^ 4) := by
        exact Finset.sum_comm;
      rw [ h_lhs, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
      congr 1;
      · have h_lhs_zero : ∀ a : F2n n, walshTwo f a 0 = if a = 0 then (2 ^ n : ℤ) else 0 := by
          intro a; exact (by
          convert chi_sum hn a using 1;
          exact walshTwo_zero_right f a);
        rw [ Finset.sum_congr rfl fun x hx => by rw [ h_lhs_zero x ] ] ; norm_num [ pow_mul' ];
      · rw [ Finset.sum_congr rfl fun x hx => ab_walshTwo_fourth_sum hn f hab x <| by aesop ];
        norm_num [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, F2n.card n hn ] ; ring;
        norm_num;
    have := global_fourth_moment hn f;
    exact mul_left_cancel₀ ( pow_ne_zero ( 2 * n ) two_ne_zero ) ( by rw [ this ] at h_global_fourth_moment; linear_combination' h_global_fourth_moment );
  -- From the global fourth moment, we know that $\sum_{a \neq 0, b} \delta(a, b)^2 = (2^n - 1) * 2^{n + 1}$.
  have h_sum_sq : ∑ a ∈ Finset.univ.erase 0, ∑ b : F2n n, (diffCount f a b : ℤ) ^ 2 = (2 ^ n - 1) * 2 ^ (n + 1) := by
    have h_sum_sq : ∑ a ∈ {0}, ∑ b : F2n n, (diffCount f a b : ℤ) ^ 2 = 2 ^ (2 * n) := by
      simp +decide [ diffCount_zero_left, pow_mul' ];
      exact_mod_cast F2n.card n hn;
    simp_all +decide [ Finset.sum_erase ];
  -- From the global fourth moment, we know that $\sum_{a \neq 0, b} \delta(a, b) = (2^n - 1) * 2^n$.
  have h_sum : ∑ a ∈ Finset.univ.erase 0, ∑ b : F2n n, (diffCount f a b : ℤ) = (2 ^ n - 1) * 2 ^ n := by
    have h_sum : ∀ a : F2n n, a ≠ 0 → ∑ b : F2n n, (diffCount f a b : ℤ) = 2 ^ n := by
      intro a ha; have := diffCount_sum f a; simp_all +decide [ F2n.card ] ;
    rw [ Finset.sum_congr rfl fun x hx => h_sum x <| Finset.ne_of_mem_erase hx ] ; norm_num [ F2n.card n hn ];
  -- Since $\delta(a, b)$ is always even for $a \neq 0$, we can write $\delta(a, b) = 2k$ for some integer $k$.
  have h_even : ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n, ∃ k : ℕ, diffCount f a b = 2 * k := by
    exact fun a ha b => even_iff_two_dvd.mp ( diffCount_even f a ha b );
  -- Since $\delta(a, b)$ is always even for $a \neq 0$, we can write $\delta(a, b) = 2k$ for some integer $k$. Therefore, $\delta(a, b)^2 = 4k^2$.
  have h_even_sq : ∑ a ∈ Finset.univ.erase 0, ∑ b : F2n n, (diffCount f a b : ℤ) * ((diffCount f a b : ℤ) - 2) = 0 := by
    simp_all +decide [ mul_sub, ← sq ];
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
    grind;
  rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_even_sq;
  · intro a ha b; specialize h_even_sq a ( Finset.mem_erase_of_ne_of_mem ha ( Finset.mem_univ a ) ) ; rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_even_sq <;> norm_num at *;
    · cases h_even_sq b <;> linarith;
    · intro b; specialize h_even a ha b; obtain ⟨ k, hk ⟩ := h_even; norm_num [ hk ] ;
      rcases k with ( _ | _ | k ) <;> norm_num ; nlinarith;
  · intro a ha; refine Finset.sum_nonneg fun b hb => ?_; obtain ⟨ k, hk ⟩ := h_even a ( Finset.ne_of_mem_erase ha ) b; norm_num [ hk ] ;
    rcases k with ( _ | _ | k ) <;> norm_num ; nlinarith

end
end Kasami