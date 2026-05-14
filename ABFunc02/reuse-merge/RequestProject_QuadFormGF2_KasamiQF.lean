/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Quadratic Form Construction — Layer 2

This file formalizes Layer 2 items 2b and 2e from the proof architecture:

## 2b: Q_a is a Quadratic Form (Gold case, k=1)

For the Gold exponent d = 3 (i.e., the Kasami exponent with k=1), the function
`Q_a(x) = Tr(a · x³) : GF(2^n) → GF(2)` is a quadratic form over GF(2).
The associated polar (bilinear) form is:
  `B_a(x,y) = Tr(a · (x²y + xy²))`

**Note on general k:** For the Kasami exponent with k ≥ 2, the function
`Tr(a · x^d)` has algebraic degree k+1 > 2 (the 2-weight of d = 4^k - 2^k + 1
is k+1), so it is NOT a quadratic form over GF(2). The proof of `kasami_is_ab`
for general k uses the APN property and fourth-moment analysis rather than the
direct quadratic form route.

## 2e: B_a Simplified (Gold case, k=1)

Using the Frobenius identity `Tr(z^{2^i}) = Tr(z)`, the bilinear form is:
  `B_a(x,y) = Tr(y · L_a(x))`
where `L_a(x) = a · x² + a^{2^{n-1}} · x^{2^{n-1}}` is a linearized polynomial.

## Main Definitions

- `goldQa a` : The function `x ↦ Tr(a · x³)` for Gold exponent
- `goldQuadFormF2 a` : The `QuadFormF2` instance for `goldQa a`

## Main Results

- `gold_cross_term` : `(x + y)³ + x³ + y³ = x²y + xy²` in char 2
- `gold_cross_add_left` : The cross term is additive in the first variable
- `gold_Ba_simplified` : `B_a(x,y) = Tr(y · (a·x² + a^{2^{n-1}}·x^{2^{n-1}}))`

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.2
- [Canteaut, Charpin, Dobbertin (2000)], SIAM J. Discrete Math.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.CCDFactorization
import RequestProject.Kasami.CCDHelpers
import RequestProject.QuadFormGF2.Defs

namespace Kasami

open scoped BigOperators
noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### Cross-term expansion for the Gold exponent (Layer 2d, k=1) -/

/-
In characteristic 2, `(x+y)³ + x³ + y³ = x²y + xy²`.
    This is the cross-term expansion for the Gold exponent d = 3.
    Proof: `(x+y)³ = x³ + 3x²y + 3xy² + y³`, and `3 = 1` in char 2.
-/
theorem gold_cross_term (x y : F2n n) :
    (x + y) ^ 3 + x ^ 3 + y ^ 3 = x ^ 2 * y + x * y ^ 2 := by
  grind +ring

/-
The Gold cross term `x²y + xy²` is additive in x.
    This follows from Freshman's dream: `(x₁+x₂)² = x₁²+x₂²` in char 2.
-/
theorem gold_cross_add_left (x₁ x₂ y : F2n n) :
    (x₁ + x₂) ^ 2 * y + (x₁ + x₂) * y ^ 2 =
    (x₁ ^ 2 * y + x₁ * y ^ 2) + (x₂ ^ 2 * y + x₂ * y ^ 2) := by
  grind +ring

/-
The Gold cross term `x²y + xy²` is additive in y (by symmetry).
-/
theorem gold_cross_add_right (x y₁ y₂ : F2n n) :
    x ^ 2 * (y₁ + y₂) + x * (y₁ + y₂) ^ 2 =
    (x ^ 2 * y₁ + x * y₁ ^ 2) + (x ^ 2 * y₂ + x * y₂ ^ 2) := by
  grind

/-! ### Layer 2a/2b: Q_a for the Gold exponent -/

/-- `Q_a(x) = Tr(a · x³)` for the Gold exponent (k=1, d=3). -/
def goldQa (a : F2n n) : F2n n → ZMod 2 :=
  fun x => tr2 n (a * x ^ 3)

/-- `Q_a(0) = 0`. -/
@[simp]
theorem goldQa_zero (a : F2n n) : goldQa a 0 = 0 := by
  simp [goldQa]

/-
The polar form of Q_a equals `Tr(a · (x²y + xy²))`.
    This uses the cross-term expansion `gold_cross_term`.
-/
theorem goldQa_polar (a x y : F2n n) :
    goldQa a (x + y) + goldQa a x + goldQa a y =
    tr2 n (a * (x ^ 2 * y + x * y ^ 2)) := by
  convert congr_arg ( fun z => tr2 n ( a * z ) ) ( gold_cross_term x y ) using 1 ; ring;
  unfold goldQa;
  rw [ ← map_add, ← map_add ] ; ring

/-
The polar form is additive in the first variable (key axiom for QuadFormF2).
    This follows from `gold_cross_add_left` and linearity of Tr.
-/
theorem goldQa_polar_add_left (a : F2n n) (x₁ x₂ y : F2n n) :
    goldQa a (x₁ + x₂ + y) + goldQa a (x₁ + x₂) + goldQa a y =
    goldQa a (x₁ + y) + goldQa a x₁ + (goldQa a (x₂ + y) + goldQa a x₂) := by
  convert goldQa_polar a ( x₁ + x₂ ) y using 1;
  convert congr_arg₂ ( · + · ) ( goldQa_polar a x₁ y ) ( goldQa_polar a x₂ y ) using 1 ; ring;
  · grind;
  · convert ( tr2 n ).map_add _ _ using 2 ; ring;
    grind

/-- **Layer 2b (Gold case)**: `Q_a(x) = Tr(a·x³)` is a quadratic form over GF(2).

    The polar form `B_a(x,y) = Tr(a·(x²y+xy²))` is bilinear because
    `x²y+xy²` is additive in each variable separately:
    - Additivity in x uses Freshman's dream: `(x₁+x₂)² = x₁²+x₂²`
    - Additivity in y uses the symmetric argument -/
def goldQuadFormF2 (a : F2n n) : QuadFormF2 (F2n n) where
  toFun := goldQa a
  map_zero' := goldQa_zero a
  polar_add_left' x₁ x₂ y := goldQa_polar_add_left a x₁ x₂ y

/-! ### Layer 2e: B_a simplified for Gold exponent -/

/-
**Layer 2e (Gold case)**: The bilinear form can be expressed as `Tr(y · L_a(x))`
    where `L_a(x) = a·x² + a^{2^{n-1}}·x^{2^{n-1}}` is a linearized polynomial.

    Proof: `B_a(x,y) = Tr(a·x²·y) + Tr(a·x·y²)`.
    The first term is already `Tr(y · (a·x²))`.
    For the second, apply `Tr(z) = Tr(z^{2^{n-1}})`:
    `Tr(a·x·y²) = Tr((a·x·y²)^{2^{n-1}}) = Tr(a^{2^{n-1}}·x^{2^{n-1}}·y^{2^n})`
    and `y^{2^n} = y` in `GF(2^n)`.
-/
theorem gold_Ba_simplified (hn : n ≠ 0) (a x y : F2n n) :
    tr2 n (a * (x ^ 2 * y + x * y ^ 2)) =
    tr2 n (y * (a * x ^ 2 + a ^ (2 ^ (n - 1)) * x ^ (2 ^ (n - 1)))) := by
  -- Apply the property of the trace that $\text{Tr}(z) = \text{Tr}(z^{2^{n-1}})$ to the second term.
  have h_trace_prop : tr2 n (a * x * y ^ 2) = tr2 n ((a * x * y ^ 2) ^ (2 ^ (n - 1))) := by
    rw [ ← tr2_pow2 hn ];
  -- Simplify the expression using the properties of exponents.
  have h_simplify : (a * x * y ^ 2) ^ (2 ^ (n - 1)) = a ^ (2 ^ (n - 1)) * x ^ (2 ^ (n - 1)) * y := by
    simp +decide [ mul_pow ];
    exact Or.inl ( by rw [ ← pow_mul, ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hn ), F2n_frobenius hn ] );
  convert congr_arg₂ ( · + · ) ( show tr2 n ( a * x ^ 2 * y ) = tr2 n ( a * x ^ 2 * y ) from rfl ) h_trace_prop using 1 <;> push_cast [ h_simplify ] <;> ring;
  · rw [ add_comm, map_add ];
  · exact map_add _ _ _

/-
The linearized polynomial `L_a(x) = a·x² + a^{2^{n-1}}·x^{2^{n-1}}` is additive.
-/
theorem gold_La_add (_hn : n ≠ 0) (a x₁ x₂ : F2n n) :
    a * (x₁ + x₂) ^ 2 + a ^ (2 ^ (n - 1)) * (x₁ + x₂) ^ (2 ^ (n - 1)) =
    (a * x₁ ^ 2 + a ^ (2 ^ (n - 1)) * x₁ ^ (2 ^ (n - 1))) +
    (a * x₂ ^ 2 + a ^ (2 ^ (n - 1)) * x₂ ^ (2 ^ (n - 1))) := by
  -- By the properties of exponents in characteristic 2, we can simplify the expression.
  have h_exp : (x₁ + x₂) ^ 2 ^ (n - 1) = x₁ ^ 2 ^ (n - 1) + x₂ ^ 2 ^ (n - 1) := by
    exact char2_add_pow x₁ x₂ (n - 1);
  grind

/-! ### General Kasami cross-term structure (Layer 2d)

The polar form identity for the general Kasami function:
`Q_a(x₁+x₂+y) + Q_a(x₁+x₂) + Q_a(y) + Q_a(x₁+y) + Q_a(x₁) + Q_a(x₂+y) + Q_a(x₂)`
is the bilinearity defect `D(x₁,x₂,y)`.

For the Gold exponent (k=1), D = 0 (proved above as `goldQa_polar_add_left`).
For general k ≥ 2, D ≠ 0, which means `Tr(a·x^d)` is not a quadratic form.
However, the derivative `D_z(x) = (x+z)^d + x^d` still has controlled structure
that feeds into the linearized polynomial kernel analysis (Layer 3). -/

/-- The second derivative at directions (1, z) of the Gold power `x^{2^m+1}` is
    independent of `x`. This is a key structural property used in the CCD analysis.
    Specifically, `D₁ Dz (x^{2^m+1}) = z^{2^m} + z`, which does not depend on `x`. -/
theorem gold_second_deriv_independent (m : ℕ) (z : F2n n) :
    ∀ x₁ x₂ : F2n n,
    ((x₁ + z + 1) ^ (2^m + 1) + (x₁ + z) ^ (2^m + 1)) +
    ((x₁ + 1) ^ (2^m + 1) + x₁ ^ (2^m + 1)) =
    ((x₂ + z + 1) ^ (2^m + 1) + (x₂ + z) ^ (2^m + 1)) +
    ((x₂ + 1) ^ (2^m + 1) + x₂ ^ (2^m + 1)) := by
  intro x₁ x₂
  rw [gold_second_deriv x₁ z m, gold_second_deriv x₂ z m]

end
end Kasami