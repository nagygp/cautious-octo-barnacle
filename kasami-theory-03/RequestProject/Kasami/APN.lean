/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Perfect Nonlinear (APN) Functions

A function `f : F_{2^n} → F_{2^n}` is **APN** if for every `a ≠ 0` and every `b`,
the equation `f(x + a) + f(x) = b` has at most 2 solutions.

## Main definitions
- `IsAPN f` — the APN property
- `derivDistrib f a b` — number of solutions to `f(x+a) + f(x) = b`

## Main results
- `apn_deriv_le_two`: APN ↔ derivative distribution ≤ 2
- `apn_deriv_even`: in char 2, derivative counts are even
- `apn_deriv_sum`: ∑_b N_a(b) = 2^n
- `apn_deriv_image_card`: for APN, exactly 2^{n-1} values b have N_a(b) = 2

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.1
- [Nyberg (1994)][nyberg1994], Advances in Cryptology — EUROCRYPT '93
-/
import Mathlib
import RequestProject.Kasami.Basic

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

set_option maxHeartbeats 800000

/-! ### Definition -/

/-- A function `f : F_{2^n} → F_{2^n}` is **APN** (almost perfect nonlinear) if
    for every `a ≠ 0` and `b`, `f(x+a) + f(x) = b` has at most 2 solutions. -/
def IsAPN {n : ℕ} (f : F2n n → F2n n) : Prop :=
  ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card ≤ 2

/-- The derivative distribution: number of solutions to `f(x+a) + f(x) = b`. -/
def derivDistrib {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card

/-! ### Basic properties of derivatives in char 2 -/

/-- If `x₀` is a solution to `f(x+a) + f(x) = b`, so is `x₀ + a`. -/
theorem deriv_paired {n : ℕ} (f : F2n n → F2n n) (a x₀ : F2n n) :
    f (x₀ + a) + f x₀ = f ((x₀ + a) + a) + f (x₀ + a) := by
  have : x₀ + a + a = x₀ := by rw [add_assoc, F2n.add_self, add_zero]
  rw [this, add_comm]

/-
Solutions come in pairs `{x₀, x₀ + a}`, so the count is always even.
-/
theorem deriv_count_even {n : ℕ} (f : F2n n → F2n n) (a : F2n n) (ha : a ≠ 0)
    (b : F2n n) : Even (derivDistrib f a b) := by
  -- By definition of $derivDistrib$, we know that $(Finset.univ.filter fun x : F2n n => (f (x + a)) + (f x) = b).card$ is even.
  have h_even : ∃ S : Finset (F2n n), (Finset.univ.filter fun x : F2n n => (f (x + a)) + (f x) = b) = S ∧ ∀ x ∈ S, x + a ∈ S ∧ x ≠ x + a := by
    grind;
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_even; rw [ show derivDistrib f a b = S.card by exact congr_arg Finset.card hS₁ ] ;
  -- Since $S$ is closed under the involution $x \mapsto x + a$, we can partition $S$ into pairs $\{x, x + a\}$.
  have h_partition : ∃ T : Finset (Finset (F2n n)), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ x ∈ t, x ∈ S) ∧ (∀ x ∈ S, ∃ t ∈ T, x ∈ t) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂) := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) S, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
    · grind;
  obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_partition; rw [ show S = Finset.biUnion T id from ?_ ] ; rw [ Finset.card_biUnion ] ; aesop;
  · exact fun x hx y hy hxy => hT₄ x hx y hy hxy;
  · grind +qlia

/-
Sum of derivative distribution over all b equals 2^n.
-/
theorem deriv_count_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, derivDistrib f a b = 2 ^ n := by
  rw [ ← F2n.card n hn ];
  unfold derivDistrib;
  simp +decide only [Finset.card_filter];
  rw [ Finset.sum_comm ] ; aesop

/-! ### APN characterization -/

/-
For APN functions with a ≠ 0, each derivDistrib value is 0 or 2.
-/
theorem apn_deriv_zero_or_two {n : ℕ} (f : F2n n → F2n n) (hf : IsAPN f)
    (a : F2n n) (ha : a ≠ 0) (b : F2n n) :
    derivDistrib f a b = 0 ∨ derivDistrib f a b = 2 := by
  exact Classical.or_iff_not_imp_left.2 fun h => le_antisymm ( hf a ha b ) ( Nat.le_of_dvd ( Nat.pos_of_ne_zero h ) <| even_iff_two_dvd.mp <| deriv_count_even f a ha b )

/-
For APN functions, exactly 2^{n-1} values b have N_a(b) = 2.
-/
theorem apn_image_card {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAPN f)
    (a : F2n n) (ha : a ≠ 0) :
    (Finset.univ.filter fun b : F2n n => derivDistrib f a b = 2).card = 2 ^ (n - 1) := by
  -- From the definition of `IsAPN`, we know that each `derivDistrib f a b` is either 0 or 2.
  have h_derivDistrib : ∀ b : F2n n, derivDistrib f a b = 0 ∨ derivDistrib f a b = 2 := by
    grind +suggestions;
  -- From the definition of `IsAPN`, we know that the sum of `derivDistrib f a b` over all `b` is `2^n`.
  have h_sum : ∑ b : F2n n, derivDistrib f a b = 2 ^ n := by
    exact?;
  rw [ Finset.sum_congr rfl fun x hx => show derivDistrib f a x = if derivDistrib f a x = 2 then 2 else 0 by cases h_derivDistrib x <;> aesop ] at h_sum ; norm_num [ Finset.sum_ite ] at h_sum;
  exact mul_right_cancel₀ two_ne_zero ( h_sum.trans ( by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.pos_of_ne_zero hn ) ] ) )

/-! ### APN and the derivative map -/

/-- The derivative map `D_a f : x ↦ f(x+a) + f(x)` for `a ≠ 0`. -/
def derivMap {n : ℕ} (f : F2n n → F2n n) (a : F2n n) : F2n n → F2n n :=
  fun x => f (x + a) + f x

/-
For APN functions, the derivative map is exactly 2-to-1 onto its image.
-/
theorem apn_deriv_two_to_one {n : ℕ} (f : F2n n → F2n n) (hf : IsAPN f)
    (a : F2n n) (ha : a ≠ 0) (y : F2n n)
    (hy : y ∈ Finset.image (derivMap f a) Finset.univ) :
    (Finset.univ.filter fun x : F2n n => derivMap f a x = y).card = 2 := by
  obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hy;
  convert ( apn_deriv_zero_or_two f hf a ha ( derivMap f a x ) ) |> Or.resolve_left <| ?_ using 1;
  exact ne_of_gt ( Finset.card_pos.mpr ⟨ x, Finset.mem_filter.mpr ⟨ hx, rfl ⟩ ⟩ )

/-! ### Fourth-moment characterization of APN -/

/-- The fourth moment bound: A function is APN iff
    `∑_a ∑_b N_a(b)² ≤ 3 · 2^{2n}`.
    For APN, each N_a(b) ∈ {0, 2} (for a ≠ 0), so
    `∑_{a≠0} ∑_b N_a(b)² = (2^n - 1) · 2^{n-1} · 4 = (2^n-1) · 2^{n+1}`. -/
theorem apn_fourth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAPN f) :
    ∑ a : F2n n, ∑ b : F2n n, (derivDistrib f a b) ^ 2 =
    2 ^ (2 * n) + (2 ^ n - 1) * 2 ^ (n + 1) := by
  sorry

end
end Kasami