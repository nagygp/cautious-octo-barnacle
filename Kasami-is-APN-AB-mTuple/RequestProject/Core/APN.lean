import Mathlib
import RequestProject.Core.CharTwo

/-!
# APN Functions and Derivative Image Theory

Defines Almost Perfect Nonlinear (APN) functions over finite fields of
characteristic 2 and proves the key structural result:

> APN ⟹ |Δ_a(f)| = 2^{n-1}

## Definitions
- `D f a x`: derivative `f(x+a) - f(x)`
- `Δ f a`: derivative image `{D f a x | x}`
- `APN f`: `∀ a ≠ 0, ∀ b, |{x | D f a x = b}| ≤ 2`

## Key results
- `fiber_card_two`: APN ⟹ each fiber has exactly 2 elements
- `deriv_image_half`: APN over GF(2ⁿ) ⟹ |Δ| = 2^{n-1}
-/

open Finset Fintype

namespace MTupleCount

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

-- ── Definitions ──────────────────────────────────────────────────

/-- Derivative of `f` in direction `a`. -/
def D (f : 𝔽 → 𝔽) (a x : 𝔽) : 𝔽 := f (x + a) - f x

/-- Image of the derivative map `D f a`. -/
def Δ (f : 𝔽 → 𝔽) (a : 𝔽) : Finset 𝔽 := univ.image (D f a)

/-- A function is APN if every nontrivial derivative equation
    `D f a x = b` has at most 2 solutions. -/
def APN (f : 𝔽 → 𝔽) : Prop :=
  ∀ a : 𝔽, a ≠ 0 → ∀ b : 𝔽, (univ.filter fun x => D f a x = b).card ≤ 2

-- ── Char-2 derivative symmetry ───────────────────────────────────

/-- `D f a (x + a) = D f a x` — each fiber has a char-2 partner. -/
lemma deriv_shift (f : 𝔽 → 𝔽) (a x : 𝔽) : D f a (x + a) = D f a x := by
  simp only [D, CharTwoAPI.sub_eq_add, CharTwoAPI.shift_cancel]; ring

/-- `x ≠ x + a` when `a ≠ 0`. -/
lemma ne_shift (x a : 𝔽) (ha : a ≠ 0) : x ≠ x + a := fun h => ha (by
  exact add_left_cancel (a := x) (show x + a = x + 0 by rw [add_zero]; exact h.symm))

-- ── Fiber analysis ───────────────────────────────────────────────

/-- APN ⟹ each achieved derivative value has exactly 2 preimages. -/
lemma fiber_card_two (f : 𝔽 → 𝔽) (hf : APN f) (a : 𝔽) (ha : a ≠ 0)
    (b : 𝔽) (hb : b ∈ Δ f a) :
    (univ.filter fun x => D f a x = b).card = 2 := by
  obtain ⟨x, _, hx⟩ := mem_image.mp hb
  exact le_antisymm (hf a ha b)
    (one_lt_card.2 ⟨x, by simp [hx], x + a, by simp [deriv_shift, hx], ne_shift x a ha⟩)

/-- Sum of fiber cardinalities equals |𝔽|. -/
lemma sum_fibers (f : 𝔽 → 𝔽) (a : 𝔽) :
    ∑ b ∈ Δ f a, (univ.filter fun x => D f a x = b).card = card 𝔽 := by
  simp only [card_filter]; rw [sum_comm]; simp
  exact congr_arg Finset.card
    (filter_true_of_mem fun x _ => mem_image_of_mem _ (mem_univ x))

/-- APN ⟹ |Δ| · 2 = |𝔽|. -/
theorem card_times_two (f : 𝔽 → 𝔽) (hf : APN f) (a : 𝔽) (ha : a ≠ 0) :
    (Δ f a).card * 2 = card 𝔽 := by
  have h := sum_fibers f a
  rw [sum_congr rfl (fun b hb => fiber_card_two f hf a ha b hb)] at h
  simpa [sum_const, smul_eq_mul] using h

/-- **Derivative image half**: APN over GF(2ⁿ) ⟹ |Δ| = 2^{n-1}. -/
theorem deriv_image_half (f : 𝔽 → 𝔽) (hf : APN f) (a : 𝔽) (ha : a ≠ 0)
    (n : ℕ) (hcard : card 𝔽 = 2 ^ n) :
    (Δ f a).card = 2 ^ (n - 1) := by
  have h2 := card_times_two f hf a ha
  rw [hcard] at h2
  have hn : 1 ≤ n := by
    by_contra h; push_neg at h; interval_cases n; simp at hcard
    exact absurd hcard (by
      have : 2 ≤ card 𝔽 := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance; omega)
  rw [show 2 ^ n = 2 ^ (n - 1) * 2 from by rw [← pow_succ]; congr 1; omega] at h2
  exact mul_right_cancel₀ (by norm_num) h2

end MTupleCount
