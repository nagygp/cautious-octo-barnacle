/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Characteristic 2 Properties for GaloisField 2 n

Basic properties of fields of characteristic 2 used in the Kasami function theory.
-/
import Mathlib

open scoped BigOperators
noncomputable section

namespace Kasami

/-- In characteristic 2, `x + x = 0`. -/
theorem charTwo_add_self {n : ℕ} (x : GaloisField 2 n) : x + x = 0 := by
  have : (2 : GaloisField 2 n) = 0 := CharP.cast_eq_zero (GaloisField 2 n) 2
  calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [this]
    _ = 0 := by ring

/-- In characteristic 2, `-x = x`. -/
theorem charTwo_neg_eq_self {n : ℕ} (x : GaloisField 2 n) : -x = x := by
  have h : x + x = 0 := charTwo_add_self x
  have : -x = -x + (x + x) := by rw [h, add_zero]
  rw [this, ← add_assoc, neg_add_cancel, zero_add]

/-- In characteristic 2, `x - y = x + y`. -/
theorem charTwo_sub_eq_add {n : ℕ} (x y : GaloisField 2 n) : x - y = x + y := by
  rw [sub_eq_add_neg, charTwo_neg_eq_self]

end Kasami

end
