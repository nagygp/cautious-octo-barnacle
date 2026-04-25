/-
# Linearized Polynomials over Finite Fields
-/
import Mathlib
import RequestProject.TraceChar
open Finset BigOperators
noncomputable section
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
attribute [local instance] ZMod.algebra

def frobeniusEndo (x : F) : F := x ^ 2

def artinSchreier (x : F) : F := x ^ 2 + x

lemma artinSchreier_add (x y : F) :
    artinSchreier F (x + y) = artinSchreier F x + artinSchreier F y := by
  unfold artinSchreier; rw [add_pow_char x y 2]; ring

lemma artinSchreier_eq_mul (x : F) :
    artinSchreier F x = x * (x + 1) := by
  unfold artinSchreier; ring

lemma artinSchreier_eq_zero_iff (x : F) :
    artinSchreier F x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [artinSchreier_eq_mul, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; exact h
    · right
      have : x = -1 := eq_neg_of_add_eq_zero_left h
      rw [this, CharTwo.neg_eq]
  · rintro (rfl | rfl)
    · left; rfl
    · right; exact CharTwo.add_self_eq_zero 1

lemma artinSchreier_kernel :
    (Finset.univ.filter (fun x : F => artinSchreier F x = 0)) =
    ({0, 1} : Finset F) := by
  ext x; simp [artinSchreier_eq_zero_iff]

lemma artinSchreier_kernel_card :
    (Finset.univ.filter (fun x : F => artinSchreier F x = 0)).card = 2 := by
  rw [artinSchreier_kernel]
  simp [Finset.card_pair (show (0 : F) ≠ 1 from one_ne_zero.symm)]

def IsLinearized (P : F → F) : Prop :=
  ∀ x y : F, P (x + y) = P x + P y

def L_op (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x

lemma L_op_linearized (k : ℕ) : IsLinearized F (L_op F k) := by
  intro x y; simp only [L_op]
  have : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, add_pow_char _ _ 2]
  rw [this]; ring

omit [Fintype F] [DecidableEq F] [CharP F 2] in
lemma linearized_kernel_subspace (P : F → F) (hP : IsLinearized F P) :
    ∀ x y : F, P x = 0 → P y = 0 → P (x + y) = 0 := by
  intro x y hx hy
  rw [hP x y, hx, hy, add_zero]

end
