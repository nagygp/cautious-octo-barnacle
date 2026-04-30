/-
  Definitions for Almost Bent (AB) functions over finite fields of characteristic 2.

  References:
  - T. Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
    2nd Order Binary Reed-Muller Codes", Information and Control 18 (1971), 369-394.
-/
import Mathlib

noncomputable section

open Finset BigOperators

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The absolute trace map Tr : F → ZMod 2, for a finite field F of characteristic 2.
    This is the algebra trace from the extension F / GF(2). -/
abbrev AbsoluteTrace [CharP F 2] [Algebra (ZMod 2) F] : F →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) F

/-- The additive character χ : ZMod 2 → ℤ, defined by χ(t) = (-1)^val(t).
    Maps 0 ↦ 1 and 1 ↦ -1. -/
def chi (t : ZMod 2) : ℤ := (-1 : ℤ) ^ t.val

@[simp] lemma chi_zero : chi (0 : ZMod 2) = 1 := by simp [chi]
@[simp] lemma chi_one : chi (1 : ZMod 2) = -1 := by simp [chi]; decide

/-- The Walsh transform of a function f : F → F at (a, b) ∈ F × F.
    W_f(a, b) = Σ_{x ∈ F} (-1)^{Tr(b · f(x) + a · x)} -/
def WalshTransform [CharP F 2] [Algebra (ZMod 2) F] (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, chi (AbsoluteTrace F (b * f x + a * x))

/-- A function f : F → F is Almost Bent (AB) if its Walsh transform takes only
    the values 0 and ±2^((n+1)/2) for all a ∈ F and b ∈ F \ {0},
    where |F| = 2^n.

    AB functions exist only when n is odd (otherwise the bound is not an integer).
    This is the defining property from Kasami's weight enumerator analysis:
    three-valued cross-correlation corresponds to exactly these Walsh transform values.
-/
def IsAlmostBent [CharP F 2] [Algebra (ZMod 2) F] (f : F → F) : Prop :=
  ∃ n : ℕ, Fintype.card F = 2 ^ n ∧ n % 2 = 1 ∧
    ∀ a b : F, b ≠ 0 →
      WalshTransform F f a b = 0 ∨
      WalshTransform F f a b = (2 : ℤ) ^ ((n + 1) / 2) ∨
      WalshTransform F f a b = -(2 : ℤ) ^ ((n + 1) / 2)

/-- A function f : F → F is Almost Perfect Nonlinear (APN) if for every a ≠ 0 and every
    b ∈ F, the equation f(x + a) + f(x) = b has at most 2 solutions in F.

    Equivalently, the derivative D_a f(x) = f(x + a) - f(x) is at most 2-to-1.
    In characteristic 2, subtraction equals addition. -/
def IsAPN [CharP F 2] (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    (Finset.univ.filter (fun x => f (x + a) + f x = b)).card ≤ 2

/-- The Kasami exponent: d = 2^(2k) - 2^k + 1.

    For k = 1: d = 3 (cube function)
    For k = 2: d = 13
    For k = 3: d = 57
    These exponents give rise to optimal nonlinear functions over GF(2^n). -/
def kasamiExponent (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami (power) function: x ↦ x^d where d is the Kasami exponent. -/
def kasamiFunction (k : ℕ) (x : F) : F := x ^ (kasamiExponent k)

end
