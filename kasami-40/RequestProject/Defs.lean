/-
# Almost Bent implies Almost Perfect Nonlinear — Definitions

This file contains definitions for APN and AB functions over finite fields
of characteristic 2, as well as the Kasami power function.

## References

* Chabaud, Vaudenay, "Links between Differential and Linear Cryptanalysis" (1994)
* Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
  2nd Order Binary Reed-Muller Codes" (1971)
-/
import Mathlib

open Finset BigOperators

/-! ### Setup -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The additive character χ: F → ℤ defined by χ(x) = (-1)^{Tr(x)}
    where Tr is the absolute trace from F to GF(2). -/
noncomputable def chi (x : F) : ℤ :=
  if (Algebra.trace (ZMod 2) F) x = 0 then 1 else -1

/-- The Walsh-Hadamard transform of f : F → F at (a, b). -/
noncomputable def walshTransform (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, chi (b * f x + a * x)

/-- The number of solutions to f(x + a) + f(x) = b. -/
noncomputable def deltaCount (f : F → F) (a b : F) : ℕ :=
  (univ.filter (fun x => f (x + a) + f x = b)).card

/-- A function f : F → F is **Almost Perfect Nonlinear (APN)** if for every
    nonzero a and every b, the equation f(x+a) + f(x) = b has at most 2 solutions. -/
def IsAPN (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F, deltaCount f a b ≤ 2

/-- A function f : F → F is **Almost Bent (AB)** if for all a and all nonzero b,
    the squared Walsh-Hadamard coefficient W_f(a,b)² is either 0 or 2·|F|.

    This is equivalent to requiring that every nonzero component function
    Tr(b·f(·)) has Walsh spectrum {0, ±√(2|F|)}. -/
def IsAB (f : F → F) : Prop :=
  ∀ a : F, ∀ b : F, b ≠ 0 →
    walshTransform f a b ^ 2 = 0 ∨
    walshTransform f a b ^ 2 = 2 * (Fintype.card F : ℤ)

/-- The Kasami exponent d = 2^{2k} − 2^k + 1. -/
def kasamiExponent (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami power function f(x) = x^d where d is the Kasami exponent. -/
noncomputable def kasamiFunction (k : ℕ) (x : F) : F := x ^ kasamiExponent k
