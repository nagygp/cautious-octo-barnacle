/-
  KasamiCharacters.lean

  Additive characters over GF(2^n) and their orthogonality properties.

  This file establishes:
  1. The canonical primitive additive character χ : F → ℂ
  2. The orthogonality relation: ∑_x χ(a·x) = 0 for a ≠ 0
  3. Character value norms

  Reference: Standard finite field Fourier analysis.
-/
import Mathlib
import KasamiTripleCount.KasamiDefs

noncomputable section

open Finset BigOperators Complex

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The Canonical Additive Character -/

/-- The canonical primitive additive character on a finite field F with values in ℂ.
    For F = GF(2^n), this gives χ(α) = (-1)^{Tr(α)}. -/
def kasamiChar : AddChar F ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex F

/-- The canonical character is primitive: χ(a · -) ≠ 1 for a ≠ 0. -/
theorem kasamiChar_isPrimitive :
    (kasamiChar F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

/-! ## Character Orthogonality -/

/-- For a ≠ 0: ∑_x χ(x · a) = 0. -/
theorem sum_char_mul_eq_zero (a : F) (ha : a ≠ 0) :
    ∑ x : F, (kasamiChar F) (x * a) = 0 := by
  have hprim := kasamiChar_isPrimitive F
  have h := AddChar.sum_mulShift (ψ := kasamiChar F) a hprim
  simp [ha] at h
  exact h

/-- For a ≠ 0: ∑_x χ(a · x) = 0. -/
theorem sum_char_mul_left_eq_zero (a : F) (ha : a ≠ 0) :
    ∑ x : F, (kasamiChar F) (a * x) = 0 := by
  simp only [show ∀ x : F, a * x = x * a from fun x => mul_comm a x]
  exact sum_char_mul_eq_zero F a ha

/-- Each character value has norm 1. -/
theorem kasamiChar_norm (x : F) :
    ‖(kasamiChar F) x‖ = 1 :=
  AddChar.norm_apply (kasamiChar F) x

end
