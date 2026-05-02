/-
# Walsh-Fourier Analysis: Character Orthogonality and Parseval

This file establishes the core Fourier-analytic results for the Walsh transform
over finite fields of characteristic 2.

## Main Results

- `character_orthogonality`: For x ≠ 0, ∑_a (-1)^{Tr(ax)} = 0
- `walsh_parseval`: ∑_a W_f(a)² = |F|²
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open scoped BigOperators
open Finset

set_option maxHeartbeats 3200000

/-- Orthogonality of additive characters: for x ≠ 0,
    ∑_a (-1)^{Tr(a·x)} = 0. -/
theorem character_orthogonality
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (x : F) (hx : x ≠ 0) :
    ∑ a : F, (if (Tr (a * x)).val = 0 then (1 : ℤ) else -1) = 0 := by
  have h_cancel : ∃ b : F, Tr (b * x) = 1 := by
    exact Exists.elim (hTr_sep x hx) fun a ha =>
      ⟨a, Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) ha⟩
  obtain ⟨b, hb⟩ := h_cancel
  have h_sum_zero : ∑ a : F, (if (Tr (a * x)).val = 0 then 1 else -1) =
      ∑ a : F, (if (Tr (a * x)).val = 0 then -1 else 1) := by
    apply Finset.sum_bij (fun a _ => a + b)
    · simp +decide
    · aesop
    · exact fun y _ => ⟨y - b, Finset.mem_univ _, sub_add_cancel _ _⟩
    · simp +decide [add_mul, hTr_add, hb]
      intro a; rcases Tr (a * x) with (_ | _ | n) <;> tauto
  simp_all +decide [Finset.sum_ite]
  linarith

/-- Parseval's identity: ∑_a W_f(a)² = |F|². -/
theorem walsh_parseval
    (F : Type*) [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    (Tr : F → ZMod 2)
    (hTr_add : ∀ x y, Tr (x + y) = Tr x + Tr y)
    (hTr_zero : Tr 0 = 0)
    (hTr_sep : ∀ x : F, x ≠ 0 → ∃ a : F, Tr (a * x) ≠ 0)
    (f : F → ZMod 2) :
    ∑ a : F, (walshTransform F Tr f a) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  have h_expand : ∀ a, (walshTransform F Tr f a) ^ 2 =
      ∑ x, ∑ y, (if (f x + f y + Tr (a * (x + y))).val = 0 then (1 : ℤ) else -1) := by
    intro a
    have h_expand : (walshTransform F Tr f a) ^ 2 =
        ∑ x, ∑ y, (if (f x + Tr (a * x)).val = 0 then (1 : ℤ) else -1) *
          (if (f y + Tr (a * y)).val = 0 then (1 : ℤ) else -1) := by
      simp +decide only [walshTransform, sq, sum_mul_sum]
    refine h_expand.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
    rw [mul_add]; simp +decide [*, ZMod.val_add]; ring
    grind
  have h_ortho : ∀ x y : F, x ≠ y →
      ∑ a : F, (if (f x + f y + Tr (a * (x + y))).val = 0 then (1 : ℤ) else -1) = 0 := by
    intro x y hxy
    have h_ortho : ∑ a : F, (if (Tr (a * (x + y))).val = 0 then (1 : ℤ) else -1) = 0 := by
      apply character_orthogonality F Tr hTr_add hTr_sep (x + y) (by grind)
    cases' Fin.exists_fin_two.mp ⟨f x + f y, rfl⟩ with h h <;> simp_all +decide [Fin.val_add]
    convert congr_arg Neg.neg h_ortho using 1
    rw [← Finset.sum_neg_distrib]; congr; ext a
    rcases Tr (a * (x + y)) with (_ | _ | n) <;> norm_cast
  rw [Finset.sum_congr rfl fun a _ => h_expand a, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x _ =>
    Finset.sum_eq_single x (fun y _ => by by_cases h : x = y <;> aesop) (by aesop)]
  simp +decide [sq]
  simp +decide [← two_mul, CharTwo.two_eq_zero]
  aesop

end
