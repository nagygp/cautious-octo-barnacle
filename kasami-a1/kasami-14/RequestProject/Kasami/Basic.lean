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
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 1
-/

import Mathlib

namespace Kasami

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
theorem F2n.add_self {n : ℕ} (x : F2n n) : x + x = 0 := by
  have : x + x = x - (-x) := by ring
  rw [this, CharTwo.neg_eq, sub_self]

theorem F2n.sub_eq_add {n : ℕ} (x y : F2n n) : x - y = x + y :=
  CharTwo.sub_eq_add x y

/-- In characteristic 2, `(x + y)^2 = x^2 + y^2` (Freshman's dream). -/
theorem F2n.add_sq {n : ℕ} (x y : F2n n) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h : x * y + x * y = 0 := F2n.add_self _
  have h2 : (x + y) ^ 2 - (x ^ 2 + y ^ 2) = x * y + x * y := by ring
  have h3 : (x + y) ^ 2 - (x ^ 2 + y ^ 2) = 0 := by rw [h2, h]
  exact sub_eq_zero.mp h3

/-! ### Cardinality -/

theorem F2n.card (n : ℕ) (hn : n ≠ 0) : Fintype.card (F2n n) = 2 ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 n hn

theorem F2n.card_pos (n : ℕ) (hn : n ≠ 0) : 0 < Fintype.card (F2n n) := by
  rw [F2n.card n hn]
  positivity

/-! ### Power map -/

/-- The power map `x ↦ x^d` on F_{2^n}. -/
noncomputable def F2n.powMap (n d : ℕ) : F2n n → F2n n := fun x => x ^ d

@[simp]
theorem F2n.powMap_zero (n d : ℕ) (hd : d ≠ 0) : F2n.powMap n d 0 = 0 := by
  simp [F2n.powMap, zero_pow hd]

@[simp]
theorem F2n.powMap_one (n : ℕ) : F2n.powMap n 1 = id := by
  ext x; simp [F2n.powMap]

end Kasami
