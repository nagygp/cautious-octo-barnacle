/-
# Characteristic 2 Utilities

Simple lemmas about fields of characteristic 2, built on `CharP`.
In char 2, subtraction equals addition, negation is identity, and
every element is its own additive inverse.

These are the arithmetic building blocks for APN/AB theory over GF(2^n).
-/
import Mathlib

open Finset

namespace ABAPN.CharTwo

variable {F : Type*} [Field F] [CharP F 2]

/-- In characteristic 2, `2 = 0`. -/
lemma two_eq_zero : (2 : F) = 0 :=
  CharP.cast_eq_zero F 2

/-
In characteristic 2, every element is its own additive inverse: `x + x = 0`.
-/
lemma add_self_eq_zero (x : F) : x + x = 0 := by
  grind

/-
In characteristic 2, negation is the identity: `-x = x`.
-/
lemma neg_eq_self (x : F) : -x = x := by
  grind +locals

/-
In characteristic 2, subtraction equals addition: `x - y = x + y`.
-/
lemma sub_eq_add (x y : F) : x - y = x + y := by
  grind

/-- The difference map simplifies in char 2: `f(x+a) - f(x) = f(x+a) + f(x)`. -/
lemma diffMap_char2 (f : F → F) (a x : F) :
    f (x + a) - f (x) = f (x + a) + f (x) := by
  exact sub_eq_add _ _

/-- In char 2, the equation `f(x+a) + f(x) = b` is equivalent to `f(x+a) - f(x) = b`. -/
lemma char2_diff_iff_sum (f : F → F) (a b x : F) :
    f (x + a) - f (x) = b ↔ f (x + a) + f (x) = b := by
  rw [sub_eq_add]

/-
In char 2, `x + y = 0 ↔ x = y`.
-/
lemma add_eq_zero_iff_eq (x y : F) : x + y = 0 ↔ x = y := by
  grind

/-
In char 2, `(x + y)^2 = x^2 + y^2` (Frobenius identity).
-/
lemma add_sq (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  grind

/-
In char 2, `(x + y)^(2^n) = x^(2^n) + y^(2^n)`.
-/
lemma add_pow_two_pow (x y : F) (n : ℕ) :
    (x + y) ^ (2 ^ n) = x ^ (2 ^ n) + y ^ (2 ^ n) := by
  induction n <;> simp_all +decide [ pow_succ', pow_mul ];
  simp_all +decide [ mul_pow, add_sq ];
  grind +ring

/-
Frobenius endomorphism in char 2 is `x ↦ x^2`, which is a ring homomorphism.
-/
lemma frobenius_eq_sq (x : F) : frobenius F 2 x = x ^ 2 := by
  exact?

/-
Iterated Frobenius is `x ↦ x^(2^n)`.
-/
lemma iterateFrobenius_eq (x : F) (n : ℕ) :
    iterateFrobenius F 2 n x = x ^ (2 ^ n) := by
  induction n <;> simp +decide [ *, pow_succ, pow_mul, iterateFrobenius ]

/-- The Frobenius is additive in char 2: it's a ring homomorphism. -/
lemma frobenius_add (x y : F) :
    frobenius F 2 (x + y) = frobenius F 2 x + frobenius F 2 y :=
  map_add (frobenius F 2) x y

/-- Iterated Frobenius is additive. -/
lemma iterateFrobenius_add (x y : F) (n : ℕ) :
    iterateFrobenius F 2 n (x + y) =
      iterateFrobenius F 2 n x + iterateFrobenius F 2 n y :=
  map_add (iterateFrobenius F 2 n) x y

end ABAPN.CharTwo