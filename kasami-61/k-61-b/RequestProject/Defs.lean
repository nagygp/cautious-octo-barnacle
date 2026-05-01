/-
# Kasami Almost Bent Functions — Core Definitions

This file defines the mathematical objects needed for the proof that
Kasami power functions x ↦ x^d (with d = 2^(2k) - 2^k + 1) over GF(2^n)
(n = 2k+1 odd) are Almost Bent (AB).

## Main Definitions
- `kasamiExp` : The Kasami exponent d = 2^(2k) - 2^k + 1
- `trGF2` : The field trace Tr : F → GF(2)
- `linearizedOp` : The linearized operator L_a(y) = a·y^(2^(2k)) + a^(2^k)·y^(2^k) + a^(2^(2k))·y
- `walshSum` : The Walsh-Hadamard transform W_f(b)
- `IsAlmostBent` : The AB property

## References
- Kasami, T. "The weight enumerators for several classes of subcodes of
  the 2nd order binary Reed-Muller codes" (1971)
-/
import Mathlib

open Finset BigOperators

/-! ### Setting: Finite field of characteristic 2 -/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

section CharTwo

variable [CharP F 2]

noncomputable instance KasamiAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

instance KasamiFact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance KasamiExpChar : ExpChar F 2 := ExpChar.prime Nat.prime_two

/-! ### Kasami exponent -/

/-- The Kasami exponent d = 2^(2k) - 2^k + 1 for the power function x ↦ x^d.
    We work in ℤ to avoid subtraction issues with ℕ, then convert. -/
def kasamiExpZ (k : ℕ) : ℤ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The Kasami exponent as a natural number.
    For k ≥ 1, we have 2^(2k) - 2^k + 1 > 0 so the cast is safe. -/
def kasamiExp (k : ℕ) : ℕ := (kasamiExpZ k).toNat

/-! ### Field trace -/

/-- The field trace Tr : F → GF(2), defined via `Algebra.trace`. -/
noncomputable def trGF2 : F →ₗ[ZMod 2] (ZMod 2) :=
  Algebra.trace (ZMod 2) F

/-! ### The sign character χ : F → ℤ

χ(x) = (-1)^Tr(x). This maps F to {-1, 1} ⊂ ℤ. -/

/-- The additive character χ(x) = (-1)^(Tr(x).val) ∈ {-1, 1}. -/
noncomputable def chiGF2 (x : F) : ℤ :=
  (-1) ^ (trGF2 F x).val

/-! ### Walsh-Hadamard transform -/

/-- The Walsh-Hadamard transform of a function f : F → F at a point b ∈ F, defined as
    W_f(b) = ∑_{x ∈ F} (-1)^{Tr(f(x) + b·x)}. -/
noncomputable def walshSum (f : F → F) (b : F) : ℤ :=
  ∑ x : F, chiGF2 F (f x + b * x)

/-! ### Almost Bent property -/

/-- A function f : F → F is Almost Bent if, assuming |F| = 2^n with n odd,
    the Walsh sum W_f(b)² ∈ {0, 2^(n+1)} for all b.

    Equivalently: |W_f(b)| ∈ {0, 2^((n+1)/2)} for all b.

    Here n = the log base 2 of |F|. -/
noncomputable def IsAlmostBent (f : F → F) : Prop :=
  let n := Nat.log 2 (Fintype.card F)
  ∀ b : F, walshSum F f b ^ 2 = 0 ∨ walshSum F f b ^ 2 = 2 ^ (n + 1)

/-! ### Kasami power function -/

/-- The Kasami power function x ↦ x^d where d = kasamiExp k. -/
def kasamiFun (k : ℕ) (x : F) : F := x ^ kasamiExp k

/-! ### The linearized operator L_a -/

/-- The linearized operator L_a(y) = a·y^(2^(2k)) + a^(2^k)·y^(2^k) + a^(2^(2k))·y.
    This is the adjoint of the polar form of the Kasami power function
    with respect to the trace bilinear form. -/
noncomputable def linearizedOp (k : ℕ) (a : F) (y : F) : F :=
  a * y ^ (2 ^ (2 * k)) + a ^ (2 ^ k) * y ^ (2 ^ k) + a ^ (2 ^ (2 * k)) * y

/-! ### The polar/bilinear form of the Kasami function -/

/-- The polar form of x ↦ x^d, measuring the "cross terms":
    Polar_d(x, y) = (x+y)^d - x^d - y^d.
    In characteristic 2, subtraction = addition, so this is (x+y)^d + x^d + y^d. -/
def polarForm (k : ℕ) (x y : F) : F :=
  (x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k

/-- The trace bilinear form B_a(x, y) = Tr(a · Polar_d(x, y)).
    Returns a value in ZMod 2. -/
noncomputable def traceBilinForm (k : ℕ) (a x y : F) : ZMod 2 :=
  trGF2 F (a * polarForm F k x y)

/-! ### The radical of the quadratic form -/

/-- The radical of the quadratic form Q_a(x) = Tr(a·x^d).
    rad(Q_a) = { y ∈ F | ∀ x, B_a(x, y) = 0 }
    (We use the bilinear radical; in char 2, Q_a(y) = 0 is automatic for the radical
     when d is odd, since the quadratic form vanishes on the radical of its associated
     bilinear form.) -/
def radical (k : ℕ) (a : F) : Set F :=
  { y : F | ∀ x : F, traceBilinForm F k a x y = 0 }

end CharTwo
