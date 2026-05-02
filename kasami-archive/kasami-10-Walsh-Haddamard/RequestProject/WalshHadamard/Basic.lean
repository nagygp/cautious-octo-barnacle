/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Basic Setup for F_{2^n}

This module provides:
- `F2n n` as an abbreviation for `GaloisField 2 n`
- Basic instances (`Field`, `Fintype`, `CharP`, `DecidableEq`)
- Characteristic-2 lemmas (`neg_eq`, `add_self`, `sub_eq_add`)
- Cardinality: `Fintype.card (F2n n) = 2 ^ n`

## References
- [Lidl, Niederreiter, *Finite Fields*], Chapter 1
-/

import Mathlib

namespace WalshHadamardTheory

open scoped BigOperators

/-- The finite field with `2^n` elements. -/
abbrev F2n (n : ℕ) := GaloisField 2 n

/-! ### Instances -/

noncomputable instance F2n.instFintype (n : ℕ) : Fintype (F2n n) :=
  Fintype.ofFinite _

/-! ### Characteristic 2 lemmas -/

@[simp]
theorem F2n.neg_eq {n : ℕ} (x : F2n n) : -x = x :=
  CharTwo.neg_eq x

@[simp]
theorem F2n.add_self {n : ℕ} (x : F2n n) : x + x = 0 :=
  CharTwo.add_eq_zero.mpr rfl

theorem F2n.sub_eq_add {n : ℕ} (x y : F2n n) : x - y = x + y :=
  CharTwo.sub_eq_add x y

/-- In characteristic 2, `(x + y)^2 = x^2 + y^2` (Freshman's dream). -/
theorem F2n.add_sq {n : ℕ} (x y : F2n n) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have : Fact (Nat.Prime 2) := Fact.mk (by norm_num)
  exact add_pow_char x y 2

/-! ### Cardinality -/

theorem F2n.card (n : ℕ) (hn : n ≠ 0) : Fintype.card (F2n n) = 2 ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 n hn

theorem F2n.card_pos (n : ℕ) (hn : n ≠ 0) : 0 < Fintype.card (F2n n) := by
  rw [F2n.card n hn]; positivity

theorem F2n.card_ne_zero (n : ℕ) (hn : n ≠ 0) : Fintype.card (F2n n) ≠ 0 := by
  rw [F2n.card n hn]; positivity

theorem F2n.card_cast_ne_zero (n : ℕ) (hn : n ≠ 0) : (Fintype.card (F2n n) : ℤ) ≠ 0 := by
  rw [F2n.card n hn]; positivity

/-! ### Add/neg identities in char 2 -/

theorem F2n.add_eq_zero_iff {n : ℕ} (x y : F2n n) : x + y = 0 ↔ x = y := by
  constructor
  · intro h; have := congr_arg (· + y) h; simp [add_assoc] at this; exact this
  · intro h; subst h; exact F2n.add_self x

end WalshHadamardTheory
