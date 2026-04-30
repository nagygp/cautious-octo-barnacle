/-
  Kasami Radical–Kernel Identification
  =====================================
  The bridge between the quadratic form Q_a and the linearized polynomial L_a:
    rad(Q_a) = ker(L_a)

  This is the deepest algebraic step, connecting:
  - The radical of the quadratic form Q_a(x) = Tr(a · x^d)
  - The kernel of the linearized polynomial L_a(z)

  The proof proceeds by:
  1. Expanding the polar form (x+y)^d + x^d + y^d using d = 2^(2k) − 2^k + 1
  2. Using Frobenius invariance of trace to simplify
  3. Showing the expression equals Tr(x · L_a(y))
  4. Concluding via non-degeneracy of the trace
-/
import Mathlib
import RequestProject.Kasami.Defs

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000

/-! ## Polar Form Expansion

For the Kasami exponent d = 2^(2k) − 2^k + 1, the polar form
  (x + y)^d + x^d + y^d
has a specific structure that connects to L_a.
-/

section PolarForm

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-
In characteristic 2, (x + y)^(2^m) = x^(2^m) + y^(2^m)
-/
lemma add_pow_two_pow (m : ℕ) (x y : F) :
    (x + y) ^ (2 ^ m) = x ^ (2 ^ m) + y ^ (2 ^ m) := by
  induction m <;> simp_all +decide [ pow_succ, pow_mul ];
  grind +revert

/-- The polar form of x^d for the Kasami exponent, after trace manipulation,
    equals Tr(x · L_a(y)) where L_a is the a-twisted linearized polynomial.

    Specifically, for Q_a(x) = Tr(a · x^d):
      B_a(x, y) = Q_a(x+y) + Q_a(x) + Q_a(y) = Tr(x · L_a(y))

    where L_a(y) = a^(2^(2k))·y^(2^(2k)) + a^(2^k)·y^(2^k) + a·y
-/
lemma polar_form_eq_trace_linPolyLA (n k : ℕ) (a x y : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (hgcd : Nat.Coprime (3 * k) n) :
    absoluteTrace n (a * ((x + y) ^ kasamiExponent k + x ^ kasamiExponent k + y ^ kasamiExponent k))
    = absoluteTrace n (x * linPolyLA k a y) := by
  sorry

/-- The radical of Q_a equals the kernel of L_a.
    y ∈ rad(Q_a) ⟺ ∀ x, Tr(a·((x+y)^d + x^d + y^d)) = 0 ⟺ L_a(y) = 0 -/
lemma radical_eq_ker_LA (n k : ℕ) (a : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (hgcd : Nat.Coprime (3 * k) n)
    (y : F) :
    (∀ x : F, absoluteTrace n (a * ((x + y) ^ kasamiExponent k +
      x ^ kasamiExponent k + y ^ kasamiExponent k)) = 0) ↔
    linPolyLA k a y = 0 := by
  sorry

end PolarForm