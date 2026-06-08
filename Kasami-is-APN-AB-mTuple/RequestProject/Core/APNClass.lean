import Mathlib
import RequestProject.Core.CharTwo

/-!
# APN: Unified Definition and Structural Lemmas

Two equivalent APN definitions and their bridge.

## Key definitions
- `APNFun f`:       APN (cardinality form)
- `APNCollision f`: APN (collision form)
- `apn_iff_collision`: equivalence
-/

open Finset Fintype CharTwoAPI

namespace APNClass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

def D (f : F → F) (a x : F) : F := f (x + a) - f x
def Δ (f : F → F) (a : F) : Finset F := univ.image (D f a)

def APNFun (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, (univ.filter fun x => D f a x = b).card ≤ 2

def APNCollision (f : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (x y : F),
    f (x + a) + f x = f (y + a) + f y → y = x ∨ y = x + a

omit [Fintype F] [DecidableEq F] in
lemma deriv_shift (f : F → F) (a x : F) : D f a (x + a) = D f a x := by
  simp only [D, CharTwoAPI.sub_eq_add, CharTwoAPI.shift_cancel]; ring

omit [Fintype F] [DecidableEq F] [CharP F 2] in
lemma ne_shift (x a : F) (ha : a ≠ 0) : x ≠ x + a := fun h => ha (by
  exact add_left_cancel (a := x) (show x + a = x + 0 by rw [add_zero]; exact h.symm))

theorem collision_to_card (f : F → F) (hf : APNCollision f) : APNFun f := by
  intro a ha b
  by_contra h_gt; push_neg at h_gt
  obtain ⟨x₁, hx₁m, x₂, hx₂m, x₃, hx₃m, h12, h13, h23⟩ :=
    two_lt_card.mp h_gt
  simp only [mem_filter, mem_univ, true_and, D] at hx₁m hx₂m hx₃m
  have heq12 : f (x₁ + a) + f x₁ = f (x₂ + a) + f x₂ := by
    rw [CharTwo.sub_eq_add] at hx₁m hx₂m; rw [hx₁m, hx₂m]
  have heq13 : f (x₁ + a) + f x₁ = f (x₃ + a) + f x₃ := by
    rw [CharTwo.sub_eq_add] at hx₁m hx₃m; rw [hx₁m, hx₃m]
  rcases hf a ha x₁ x₂ heq12 with rfl | rfl
  · exact h12 rfl
  · rcases hf a ha x₁ x₃ heq13 with rfl | rfl
    · exact h13 rfl
    · exact h23 rfl

theorem card_to_collision (f : F → F) (hf : APNFun f) : APNCollision f := by
  intro a ha x y hxy
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨hne, hne_shift⟩ := h_neg
  have hy_in : D f a y = D f a x := by
    simp only [D, CharTwo.sub_eq_add]; exact hxy.symm
  have hxa_in : D f a (x + a) = D f a x := deriv_shift f a x
  have h1 : x ≠ x + a := ne_shift x a ha
  have : 2 < (univ.filter fun z => D f a z = D f a x).card := by
    apply two_lt_card.mpr
    exact ⟨x, by simp, x + a, by simp [hxa_in], y, by simp [hy_in], h1, hne.symm, hne_shift.symm⟩
  exact Nat.lt_irrefl _ (lt_of_lt_of_le this (hf a ha (D f a x)))

theorem apn_iff_collision (f : F → F) : APNFun f ↔ APNCollision f :=
  ⟨card_to_collision f, collision_to_card f⟩

theorem apn_comp_additive_bij
    {G : Type*} [Field G]
    {f : G → G} (hf : APNCollision f)
    {σ : G → G} (hσ_bij : Function.Bijective σ)
    (hσ_add : ∀ x y, σ (x + y) = σ x + σ y) :
    APNCollision (σ ∘ f) := by
  intro a ha x y hxy
  have h : f (x + a) + f x = f (y + a) + f y := by
    have h1 : σ (f (x + a)) + σ (f x) = σ (f (y + a)) + σ (f y) := hxy
    have h2 : σ (f (x + a) + f x) = σ (f (y + a) + f y) := by
      rw [hσ_add, hσ_add]; exact h1
    exact hσ_bij.injective h2
  exact hf a ha x y h

lemma fiber_card_two (f : F → F) (hf : APNFun f) (a : F) (ha : a ≠ 0)
    (b : F) (hb : b ∈ Δ f a) :
    (univ.filter fun x => D f a x = b).card = 2 := by
  obtain ⟨x, _, hx⟩ := mem_image.mp hb
  exact le_antisymm (hf a ha b)
    (one_lt_card.2 ⟨x, by simp [hx], x + a, by simp [deriv_shift, hx], ne_shift x a ha⟩)

omit [CharP F 2] in
lemma sum_fibers (f : F → F) (a : F) :
    ∑ b ∈ Δ f a, (univ.filter fun x => D f a x = b).card = card F := by
  simp only [card_filter]; rw [sum_comm]; simp
  exact congr_arg Finset.card
    (filter_true_of_mem fun x _ => mem_image_of_mem _ (mem_univ x))

theorem card_times_two (f : F → F) (hf : APNFun f) (a : F) (ha : a ≠ 0) :
    (Δ f a).card * 2 = card F := by
  have h := sum_fibers f a
  rw [sum_congr rfl (fun b hb => fiber_card_two f hf a ha b hb)] at h
  simpa [sum_const, smul_eq_mul] using h

theorem deriv_image_half (f : F → F) (hf : APNFun f) (a : F) (ha : a ≠ 0)
    (n : ℕ) (hcard : card F = 2 ^ n) :
    (Δ f a).card = 2 ^ (n - 1) := by
  have h2 := card_times_two f hf a ha
  rw [hcard] at h2
  have hn : 1 ≤ n := by
    by_contra h; push_neg at h; interval_cases n; simp at hcard
    exact absurd hcard (by
      have : 2 ≤ card F := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance; omega)
  rw [show 2 ^ n = 2 ^ (n - 1) * 2 from by rw [← pow_succ]; congr 1; omega] at h2
  exact mul_right_cancel₀ (by norm_num) h2

end APNClass
