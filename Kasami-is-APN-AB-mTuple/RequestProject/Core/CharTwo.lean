import Mathlib

/-!
# Unified Characteristic-2 Field API

This module consolidates all characteristic-2 arithmetic lemmas into a single,
well-organized API. It replaces the scattered char-2 facts from `CharTwo.lean`,
`CharTwoBasics.lean`, and inline proofs throughout the library.

## Design principles

1. **Atomic lemmas**: Each lemma proves exactly one algebraic identity.
2. **Layered**: Basic ring facts first, then field-specific, then Frobenius.
3. **Namespace**: Everything in `CharTwoAPI` to avoid collision with Mathlib's `CharTwo`.
4. **Minimal hypotheses**: Use `[CommSemiring R] [CharP R 2]` when possible,
   upgrade to `[Field F]` only when needed.

## Sections

- §1 Ring arithmetic: `add_self`, `neg_eq`, `sub_eq_add`, `shift_cancel`
- §2 Frobenius map: `frob_add`, `frob_one`, `frob_mul`, `frob_comp`
- §3 Frobenius bijectivity (finite fields)
-/

namespace CharTwoAPI

-- ═══════════════════════════════════════════
-- §1  Basic ring arithmetic in char 2
-- ═══════════════════════════════════════════

section RingArith

variable {R : Type*} [Ring R] [CharP R 2]

/-- `x + x = 0` in characteristic 2. -/
@[simp] lemma add_self (x : R) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

/-- `-x = x` in characteristic 2. -/
@[simp] lemma neg_eq (x : R) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self x)

/-- `x - y = x + y` in characteristic 2. -/
@[simp] lemma sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq]

/-- `x + a + a = x` — adding twice cancels in char 2. -/
lemma shift_cancel (x a : R) : x + a + a = x := by
  rw [add_assoc, add_self, add_zero]

/-- `2 = 0` in characteristic 2. -/
@[simp] lemma two_eq_zero : (2 : R) = 0 :=
  CharP.cast_eq_zero R 2

end RingArith

-- ═══════════════════════════════════════════
-- §2  Frobenius map (additive power maps)
-- ═══════════════════════════════════════════

section Frobenius

variable {R : Type*} [CommSemiring R] [CharP R 2]

/-- The Frobenius map is additive: `(x+y)^{2^k} = x^{2^k} + y^{2^k}`. -/
lemma frob_add (k : ℕ) (x y : R) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
  add_pow_char_pow_of_commute 2 k (Commute.all x y)

/-- The freshman's dream: `(x+y)² = x² + y²` in char 2. -/
lemma sq_add (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  frob_add 1 x y

omit [CharP R 2] in
/-- Frobenius preserves `1`: `1^{2^k} = 1`. -/
@[simp] lemma frob_one (k : ℕ) : (1 : R) ^ (2 ^ k) = 1 :=
  one_pow _

omit [CharP R 2] in
/-- Frobenius distributes over multiplication (trivially). -/
lemma frob_mul (k : ℕ) (x y : R) :
    (x * y) ^ (2 ^ k) = x ^ (2 ^ k) * y ^ (2 ^ k) :=
  mul_pow x y _

omit [CharP R 2] in
/-- Iterated Frobenius: `(x^{2^j})^{2^k} = x^{2^{j+k}}`. -/
lemma frob_comp (j k : ℕ) (x : R) :
    (x ^ (2 ^ j)) ^ (2 ^ k) = x ^ (2 ^ (j + k)) := by
  rw [← pow_mul, ← pow_add]

end Frobenius

-- ═══════════════════════════════════════════
-- §3  Frobenius bijectivity on finite fields
-- ═══════════════════════════════════════════

section FrobBij

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The Frobenius `x ↦ x^{2^k}` is bijective on any finite field. -/
lemma frob_bijective (k : ℕ) :
    Function.Bijective (fun x : F => x ^ (2 ^ k)) := by
  have : (fun x : F => x ^ (2 ^ k)) = iterateFrobenius F 2 k := by
    ext x; simp [iterateFrobenius_def]
  rw [this]
  exact Finite.injective_iff_bijective.mp (iterateFrobenius F 2 k).injective

omit [CharP F 2] in
/-- On `GF(2ⁿ)`, `x^{2ⁿ} = x`. -/
lemma frob_period {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
  rw [← hn, FiniteField.pow_card]

end FrobBij

end CharTwoAPI
