import CodeTheoryCryptoEquiv.APN.Defs

/-!
# Characteristic 2 Basics and Linearized Polynomial Lemmas

This file builds up the foundational lemmas about characteristic 2 fields
that are needed for the cross-pair analysis.

## Educational Notes

### Working with Characteristic 2 in Lean

In Lean 4 + Mathlib, characteristic 2 is expressed via `CharP F 2`.
Key consequences:
- `CharTwo.add_self_eq_zero`: `x + x = 0`
- `CharTwo.neg_eq`: `-x = x`
- `CharTwo.sub_eq_add`: `x - y = x + y`

The **Freshman's Dream** in char 2:
- `add_pow_char_of_commute`: `(x+y)^p = x^p + y^p` for char = p
- `add_pow_char_pow_of_commute`: `(x+y)^(p^k) = x^(p^k) + y^(p^k)`

### Tip: Working with `CharP`

Always have `instance : Fact (Nat.Prime 2) := ⟨by decide⟩` available.
Many Mathlib lemmas about char p require `Fact (Nat.Prime p)`.

### Tip: The `ring` tactic

`ring` works over commutative (semi)rings. It's your best friend for
algebraic identities. Use `ring_nf` to normalize without closing the goal.

### Tip: `simp` with `CharTwo` lemmas

Use `simp [CharTwo.add_self_eq_zero]` or `simp [CharTwo.neg_eq]` to
simplify char-2 expressions. The `+decide` modifier helps with small computations.
-/

set_option maxHeartbeats 800000

namespace CollisionAnalysis

open Finset Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

-- Make Nat.Prime 2 available as a Fact for Frobenius lemmas
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Characteristic 2 Fundamentals

These are the building blocks. Every proof in char 2 uses these repeatedly.
-/

/-- In char 2, `x + x = 0`. This is the most fundamental char-2 fact. -/
theorem char2_add_self (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- In char 2, `-x = x`. Negation is the identity! -/
theorem char2_neg (x : F) : -x = x := CharTwo.neg_eq x

/-- In char 2, `x - y = x + y`. Subtraction equals addition! -/
theorem char2_sub (x y : F) : x - y = x + y := CharTwo.sub_eq_add x y

/-- **Freshman's Dream** (char 2): `(x+y)^2 = x^2 + y^2`.
No cross terms! This is because `2·x·y = 0` in char 2. -/
theorem freshman_sq (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char_of_commute 2 (Commute.all x y)

/-- **Iterated Freshman's Dream**: `(x+y)^(2^k) = x^(2^k) + y^(2^k)`.
The Frobenius map `x ↦ x^(2^k)` is additive in char 2! -/
theorem freshman_pow (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
  add_pow_char_pow_of_commute 2 k (Commute.all x y)

/-! ## Linearized Polynomial Properties

The linearized polynomial `L_k(x) = x^(2^k) + x` is the workhorse of
the Kasami analysis. Its key property is GF(2)-linearity.
-/

/-- `L` is additive: `L(x+y) = L(x) + L(y)`.
This follows directly from the Freshman's Dream. -/
theorem L_add (k : ℕ) (x y : F) : L k (x + y) = L k x + L k y := by
  simp [L, freshman_pow]; ring

/-- `L(0) = 0`. -/
theorem L_zero (k : ℕ) : L k (0 : F) = 0 := by simp [L]

/-- `L(1) = 1^(2^k) + 1 = 1 + 1 = 0` in char 2. -/
theorem L_one (k : ℕ) : L k (1 : F) = 0 := by
  simp [L, one_pow, CharTwo.add_self_eq_zero]

/-! ## sVal Pairing

The key structural property: `sVal(k, t) = sVal(k, t+1)`.
This means sVal fibers come in pairs `{t, t+1}`.
-/

-- **sVal pairing**: `sVal(k, t) = sVal(k, t+1)`.
-- Proof idea: Direct calculation using `(t+1)+1 = t` in char 2.
omit [Fintype F] [DecidableEq F] in
theorem sVal_pairing (k : ℕ) (t : F) : sVal k t = sVal k (t + 1) := by
  simp only [sVal]
  have : t + 1 + 1 = t := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [this]; ring

/-! ## Cross Form Properties

The cross form `Cross(s, P) = s·P^(2^k) + s^(2^k)·P` connects
the collision structure to linearized polynomials.
-/

/-- Cross form is additive in the second argument. -/
theorem cross_add (k : ℕ) (s P₁ P₂ : F) :
    Cross k s (P₁ + P₂) = Cross k s P₁ + Cross k s P₂ := by
  simp only [Cross, freshman_pow, mul_add]; ring

-- **Cross-norm factorization**: `Cross(s, P) = N(s) · L(P/s)` when `s ≠ 0`.
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem cross_eq_norm_L (k : ℕ) (s P : F) (hs : s ≠ 0) :
    Cross k s P = N k s * L k (P / s) := by
  simp only [Cross, N, L]; rw [div_pow, mul_add]
  congr 1 <;> (field_simp; ring)

-- Cross form vanishes iff `L(P/s) = 0` (when `s ≠ 0`).
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem cross_zero_iff (k : ℕ) (s P : F) (hs : s ≠ 0) :
    Cross k s P = 0 ↔ L k (P / s) = 0 := by
  rw [cross_eq_norm_L k s P hs]; constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hs)
  · intro h; rw [h, mul_zero]

/-! ## Kernel of L_k

When `gcd(k, n) = 1`, the kernel of `L_k` over GF(2^n) is just `{0, 1}`.
-/

/-
**L_k kernel triviality**: If `gcd(k,n) = 1` and `|F| = 2^n`,
then `L_k(x) = 0` implies `x ∈ {0, 1}`.
-/
theorem L_ker_trivial {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (x : F) (hx : L k x = 0) :
    x = 0 ∨ x = 1 := by
  by_cases hx0 : x = 0 <;> simp_all +decide [ L ];
  -- Since $x^{2^k} = x$, we have $x^{2^k - 1} = 1$.
  have hx_pow : x ^ (2 ^ k - 1) = 1 := by
    cases m : 2 ^ k <;> simp_all +decide [ pow_succ, add_eq_zero_iff_eq_neg ];
    grobner;
  -- Since $x^{2^n - 1} = 1$, we have $x^{gcd(2^k - 1, 2^n - 1)} = 1$.
  have hx_gcd : x ^ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 1 := by
    rw [ Nat.gcd_comm, pow_gcd_eq_one ];
    exact ⟨ by rw [ ← hcard, FiniteField.pow_card_sub_one_eq_one x hx0 ], hx_pow ⟩;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]

/-! ## Cross Form Triviality -/

-- **Cross-zero triviality**: When `gcd(k,n) = 1` and `s ≠ 0`,
-- `Cross(s, P) = 0` iff `P = 0` or `P = s`.
theorem cross_zero_iff_trivial {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (s P : F) (hs : s ≠ 0) :
    Cross k s P = 0 ↔ (P = 0 ∨ P = s) := by
  rw [cross_zero_iff k s P hs]
  constructor
  · intro h
    rcases L_ker_trivial hcard k hcop _ h with h0 | h1
    · left; exact (div_eq_zero_iff.mp h0).resolve_right hs
    · right; rwa [div_eq_one_iff_eq hs] at h1
  · rintro (rfl | rfl)
    · simp [L]
    · rw [div_self hs]; exact L_one k

end CollisionAnalysis