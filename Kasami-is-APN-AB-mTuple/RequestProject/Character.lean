import Mathlib

/-!
# Additive Characters and Character Sums

Defines the integer-valued additive character structure `Chi` and
the weighted character sum `S χ v T`.

## Definitions
- `Chi 𝔽`: additive character `𝔽 → ℤ` with multiplicativity and orthogonality
- `S χ v T`: character sum `∑ x ∈ T, χ(v · x)`

## Key result
- `char_sum_zero`: `S χ 0 T = |T|`
-/

open Finset Fintype

namespace MTupleCount

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-- An additive character `χ : 𝔽 → ℤ` satisfying:
- `χ(0) = 1`
- `χ(x + y) = χ(x) · χ(y)`
- orthogonality: `∑ x, χ(c · x) = |𝔽|` if `c = 0`, else `0` -/
structure Chi (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] where
  /-- The character function. -/
  app : 𝔽 → ℤ
  /-- χ(0) = 1. -/
  app_zero : app 0 = 1
  /-- Multiplicativity: χ(x + y) = χ(x) · χ(y). -/
  app_add : ∀ x y, app (x + y) = app x * app y
  /-- Orthogonality relation. -/
  orth : ∀ c : 𝔽, ∑ x : 𝔽, app (c * x) = if c = 0 then (card 𝔽 : ℤ) else 0

/-- Character sum: `S χ v T = ∑ x ∈ T, χ(v · x)`. -/
def S (χ : Chi 𝔽) (v : 𝔽) (T : Finset 𝔽) : ℤ :=
  ∑ x ∈ T, χ.app (v * x)

/-- Evaluating at zero: `S χ 0 T = |T|`. -/
lemma char_sum_zero (χ : Chi 𝔽) (T : Finset 𝔽) : S χ 0 T = (T.card : ℤ) := by
  simp [S, zero_mul, χ.app_zero]

end MTupleCount
