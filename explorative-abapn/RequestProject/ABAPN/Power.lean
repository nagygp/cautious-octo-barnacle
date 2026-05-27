/-
# Power Functions and Exponents

Power functions `x ↦ x^d` over finite fields, and key exponent families
(Gold, Kasami, inverse). Built on `HPow`, `frobenius`, `Polynomial.eval`.

Power functions are the most-studied source of APN/AB functions.
-/
import Mathlib
import RequestProject.ABAPN.Defs
import RequestProject.ABAPN.CharTwo

open Finset Function ABAPN

namespace ABAPN.Power

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Power function definition and basic properties -/

/-- The power function `x ↦ x ^ d`. -/
def powerFn (d : ℕ) : F → F := fun x => x ^ d

/-- Power function at zero. -/
@[simp]
lemma powerFn_zero (d : ℕ) (hd : 0 < d) : powerFn d (0 : F) = 0 := by
  simp [powerFn, pos_iff_ne_zero.mp hd]

/-- Power function at one. -/
@[simp]
lemma powerFn_one (d : ℕ) : powerFn d (1 : F) = 1 := by
  simp [powerFn]

/-- The cubing function `x ↦ x³`. -/
def cubeFn : F → F := powerFn 3

/-- The inverse function `x ↦ x⁻¹` (as a power function over GF(2^n)). -/
def inverseFn : F → F := fun x => x⁻¹

/-! ### Difference of powers -/

/-- Key identity for power maps: `(x+a)^d - x^d` factors through a polynomial in `x` and `a`. -/
lemma powerFn_diffMap (d : ℕ) (a x : F) :
    ABAPN.diffMap (powerFn d) a x = (x + a) ^ d - x ^ d := by
  simp [diffMap, powerFn]

/-! ### Gold exponents -/

/-- A Gold exponent is `2^k + 1` for some `k`. These give APN power functions over GF(2^n)
    when `gcd(k, n) = 1`. -/
def isGoldExponent (d : ℕ) : Prop := ∃ k : ℕ, d = 2 ^ k + 1

/-- The simplest Gold exponent: `d = 3 = 2^1 + 1`. -/
lemma three_is_gold : isGoldExponent 3 := ⟨1, by norm_num⟩

/-- Gold exponent `d = 5 = 2^2 + 1`. -/
lemma five_is_gold : isGoldExponent 5 := ⟨2, by norm_num⟩

/-! ### Kasami exponents -/

/-- A Kasami exponent is `2^(2k) - 2^k + 1` for some `k`.
    These give APN power functions over GF(2^n) when `gcd(k, n) = 1`. -/
def isKasamiExponent (d : ℕ) : Prop := ∃ k : ℕ, 0 < k ∧ d = 2 ^ (2 * k) - 2 ^ k + 1

/-- Kasami at k=1 gives d = 4 - 2 + 1 = 3 (which is also Gold). -/
lemma kasami_one_eq_three : 2 ^ (2 * 1) - 2 ^ 1 + 1 = 3 := by norm_num

/-- Kasami at k=2 gives d = 16 - 4 + 1 = 13. -/
lemma kasami_two_eq_thirteen : 2 ^ (2 * 2) - 2 ^ 2 + 1 = 13 := by norm_num

/-! ### Cube function difference identity (Gold d=3) -/

variable [CharP F 2]

/-
In char 2, the difference of cubes: `(x+a)³ + x³ = a³ + a·x² + a²·x`.
    (Using + instead of - since char 2.)
-/
lemma cube_diff_char2 (a x : F) :
    (x + a) ^ 3 - x ^ 3 = a ^ 3 + a * x ^ 2 + a ^ 2 * x := by
  grind +ring

/-
The cube difference is a linearized polynomial in `x` (plus constant term `a³`).
    Specifically, `(x+a)³ + x³ = a³ + a·x² + a²·x = a³ + L_a(x)`
    where `L_a(x) = a·x² + a²·x` is `F₂`-linear in `x`.
-/
lemma cube_diff_linear_part (a x : F) :
    (x + a) ^ 3 - x ^ 3 - a ^ 3 = a * x ^ 2 + a ^ 2 * x := by
  grind +revert

/-
The linearized part of the cube difference `L_a(x) = a·x² + a²·x`
    is additive (F₂-linear) in `x`.
-/
lemma cube_linear_part_additive (a x y : F) :
    a * (x + y) ^ 2 + a ^ 2 * (x + y) =
      (a * x ^ 2 + a ^ 2 * x) + (a * y ^ 2 + a ^ 2 * y) := by
  grind

/-! ### Gold exponent difference identity -/

/-
For Gold exponent `d = 2^k + 1`:
    `(x+a)^(2^k+1) + x^(2^k+1) = a^(2^k+1) + a·x^(2^k) + a^(2^k)·x`.
    This is the generalization of the cube case.
-/
lemma gold_diff_char2 (k : ℕ) (a x : F) :
    (x + a) ^ (2 ^ k + 1) - x ^ (2 ^ k + 1) =
      a ^ (2 ^ k + 1) + a * x ^ (2 ^ k) + a ^ (2 ^ k) * x := by
  simp +decide only [pow_succ'];
  rw [ add_pow_char_pow, sub_eq_iff_eq_add ] ; ring

/-
The linearized part of the Gold difference is additive in `x`.
-/
lemma gold_linear_part_additive (k : ℕ) (a x y : F) :
    a * (x + y) ^ (2 ^ k) + a ^ (2 ^ k) * (x + y) =
      (a * x ^ (2 ^ k) + a ^ (2 ^ k) * x) +
        (a * y ^ (2 ^ k) + a ^ (2 ^ k) * y) := by
  convert congr_arg ( fun z => a * z + a ^ 2 ^ k * ( x + y ) ) ( ABAPN.CharTwo.add_pow_two_pow x y k ) using 1 ; ring

end ABAPN.Power