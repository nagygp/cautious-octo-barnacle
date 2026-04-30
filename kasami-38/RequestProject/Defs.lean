/-
# Kasami Formalization — Basic Definitions

This file contains the fundamental definitions for the Kasami function formalization
over finite fields of characteristic 2.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Characteristic 2 Helpers -/

theorem char2_neg_eq (x : F) : -x = x := CharTwo.neg_eq x

theorem char2_sub_eq_add (x y : F) : x - y = x + y := CharTwo.sub_eq_add x y

theorem char2_add_self (x : F) : x + x = 0 := by
  rw [← two_mul]; exact mul_eq_zero_of_left (CharP.cast_eq_zero F 2) x

/-- Freshman's dream in characteristic 2: `(a + b)^{2^k} = a^{2^k} + b^{2^k}`. -/
theorem char2_freshman (a b : F) (k : ℕ) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_char_pow a b 2 k

/-- Frobenius identity: `x^{|F|} = x` in a finite field. -/
theorem frobenius_id (x : F) : x ^ Fintype.card F = x :=
  FiniteField.pow_card x

/-! ## Linearized Polynomials -/

/-- The linearized polynomial `L_k(x) = x^{2^{2k}} + x^{2^k} + x`. -/
def linPolyL (k : ℕ) (x : F) : F :=
  x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + x

/-- The linearized polynomial `M_k(x) = x^{2^k} + x`. -/
def linPolyM (k : ℕ) (x : F) : F :=
  x ^ (2 ^ k) + x

/-! ## Kasami Exponent -/

/-- The Kasami exponent `d = 2^{2k} - 2^k + 1 = 4^k - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami function `x ↦ x^d` where `d = kasamiExp k`. -/
def kasamiF (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-! ## CCD Cross-Term -/

/-- The CCD cross-term `C(t) = t^{2^{2k}+2^k} + t^{2^k+1} + t^{2^{2k}+1}`. -/
def ccdCrossTerm (k : ℕ) (t : F) : F :=
  t ^ (2 ^ (2 * k) + 2 ^ k) + t ^ (2 ^ k + 1) + t ^ (2 ^ (2 * k) + 1)

/-! ## Trace and Additive Character -/

/-- Abstract trace function satisfying the required properties. -/
class HasTrace (F : Type*) [Field F] [Fintype F] [CharP F 2] where
  tr : F → ZMod 2
  tr_add : ∀ x y : F, tr (x + y) = tr x + tr y
  tr_pow2 : ∀ x : F, tr (x ^ 2) = tr x
  tr_surjective : Function.Surjective tr

/-- The additive character `χ(x) = (-1)^{Tr(x)}` represented as an integer. -/
def chi [HasTrace F] (x : F) : ℤ :=
  if HasTrace.tr x = (0 : ZMod 2) then 1 else -1

/-- Walsh-Hadamard transform: `W_f(a) = ∑_x χ(a·f(x))`. -/
def wht [HasTrace F] (f : F → F) (a : F) : ℤ :=
  ∑ x : F, chi (a * f x)

/-- A function is Almost Bent if `W_f(a)² ∈ {0, 2^{n+1}}` for all `a`. -/
def IsAlmostBent [HasTrace F] (f : F → F) : Prop :=
  ∀ a : F, wht f a ^ 2 = 0 ∨ wht f a ^ 2 = (2 : ℤ) ^ (Nat.log 2 (Fintype.card F) + 1)

end
