/-
  Kasami-59: Formalization of the radical-kernel bridge for power functions
  over finite fields of characteristic 2.

  We prove that for the Gold exponent d = 2^k + 1, the "radical" (linear space)
  of the Boolean function Q_a(x) = Tr(a · x^d) equals the kernel of the
  linearized polynomial L_a.

  The proof uses three key ingredients:
  1. Polar form expansion: Polar(x, y) = x · y^(2^k) + x^(2^k) · y
  2. Trace adjoint property: Tr(u · v^(2^j)) = Tr(u^(2^(n-j)) · v)
  3. Non-degeneracy of the trace form for separable extensions

  This is the "Route 1: Trace Adjoint Approach" from the proof sketch.
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Basic setup -/

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

/-- In a field with `Algebra (ZMod 2) F`, we get `CharP F 2`. -/
noncomputable instance charP_of_ZMod2_algebra : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-- The field trace Tr : F → ZMod 2. -/
noncomputable abbrev Tr : F →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) F

/-! ## Gold exponent definitions -/

/-- The Gold exponent: d = 2^k + 1. -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-- The quadratic function Q_a(x) = Tr(a * x^d) for the Gold exponent. -/
noncomputable def goldQ (k : ℕ) (a x : F) : ZMod 2 :=
  Tr (a * x ^ goldExp k)

/-- The polar form: Polar_d(x, y) = (x + y)^d + x^d + y^d (before trace). -/
def polar (d : ℕ) (x y : F) : F :=
  (x + y) ^ d + x ^ d + y ^ d

/-- The bilinear map B_a(x, y) = Tr(a * Polar(x, y)). -/
noncomputable def goldB (k : ℕ) (a x y : F) : ZMod 2 :=
  Tr (a * polar (goldExp k) x y)

/-- The linearized polynomial L_a(y) for the Gold exponent.
    L_a(y) = a * y^(2^k) + a^(2^(n-k)) * y^(2^(n-k))
    where n = [F : ZMod 2].

    Note: When n and k satisfy φ^n = id, this simplifies the trace adjoint computation.
-/
noncomputable def goldL (k : ℕ) (a y : F) : F :=
  let n := Module.finrank (ZMod 2) F
  a * y ^ (2 ^ k) + a ^ (2 ^ (n - k)) * y ^ (2 ^ (n - k))

/-- The radical (linear space) of Q_a: the set of y such that B_a(x, y) = 0 for all x. -/
def goldRadical (k : ℕ) (a : F) : Set F :=
  {y | ∀ x, goldB k a x y = 0}

/-- The kernel of L_a. -/
noncomputable def goldKerL (k : ℕ) (a : F) : Set F :=
  {y | goldL k a y = 0}

/-! ## Key identity: B_a(x, y) = Q_a(x + y) + Q_a(x) + Q_a(y) -/

lemma goldB_eq (k : ℕ) (a x y : F) :
    goldB k a x y = goldQ k a (x + y) + goldQ k a x + goldQ k a y := by
  simp only [goldB, goldQ, polar]
  simp only [map_add, mul_add]

