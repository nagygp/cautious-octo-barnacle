import Mathlib

/-!
# Characteristic-2 Field Arithmetic

Four atomic identities for fields of characteristic 2.
Each lemma establishes exactly one algebraic fact.

## Lemmas
- `add_self_zero`: `x + x = 0`
- `neg_eq_self`: `-x = x`
- `sub_eq_add`: `x - y = x + y`
- `shift_cancel`: `x + a + a = x`
-/

namespace MTupleCount

variable {𝔽 : Type*} [Ring 𝔽] [CharP 𝔽 2]

/-- `x + x = 0` in characteristic 2. -/
lemma add_self_zero (x : 𝔽) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

/-- `-x = x` in characteristic 2. -/
lemma neg_eq_self (x : 𝔽) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_zero x)

/-- `x - y = x + y` in characteristic 2. -/
lemma sub_eq_add (x y : 𝔽) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self]

/-- `x + a + a = x` in characteristic 2. -/
lemma shift_cancel (x a : 𝔽) : x + a + a = x := by
  rw [add_assoc, add_self_zero, add_zero]

end MTupleCount
