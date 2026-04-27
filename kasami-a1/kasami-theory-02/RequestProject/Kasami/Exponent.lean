/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properties of the Kasami Exponent

This file proves basic arithmetic properties of the Kasami exponent
`e(k) = 4^k - 2^k + 1`.
-/
import Mathlib
import RequestProject.Kasami.Defs

open scoped BigOperators
noncomputable section

namespace Kasami

theorem kasamiExponent_eq (k : ℕ) :
    kasamiExponent k = 2 ^ (2 * k) - 2 ^ k + 1 := rfl

/-- The Kasami exponent for k ≥ 1 is at least 1. -/
theorem kasamiExponent_ge_one (k : ℕ) : 1 ≤ kasamiExponent k :=
  kasamiExponent_pos k

end Kasami

end
