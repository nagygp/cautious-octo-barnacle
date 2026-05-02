/-
# Pless Power Moment Identities

This file formalizes the Pless power moment identities for binary linear codes.
These identities relate the power moments of the weight distribution of a code
to those of its dual code, and are derived from the MacWilliams identities.

## Main results

- The MacWilliams identity for weight enumerators
- Pless power moment identities
- Application to determining weight distributions from moments

## References

- Pless, V. (1963). Power moment identities on weight distributions in error
  correcting codes. Information and Control.
- MacWilliams, F.J. (1963). A theorem on the distribution of weights in a
  systematic code. Bell System Technical Journal.
-/

import Mathlib
import RequestProject.Kasami.Defs

open Finset BigOperators

noncomputable section

namespace BinaryLinearCode

variable {n : ℕ}

/-! ## MacWilliams Transform

The MacWilliams identity relates the weight enumerator of a code to that of its dual.
For a binary [n, k] code C with weight enumerator W_C(x,y) = ∑ A_i x^(n-i) y^i,
the dual code C⊥ has weight enumerator:
  W_{C⊥}(x,y) = (1/|C|) * W_C(x+y, x-y)

In the binary case (over GF(2)), x - y = x + y, so:
  W_{C⊥}(x,y) = (1/2^k) * W_C(x+y, x-y)
-/

/-- The weight enumerator polynomial of a code (as a function ℕ → ℚ for the transform). -/
noncomputable def weightEnumQ (C : BinaryLinearCode n) (w : ℕ) : ℚ :=
  (weightCount C w : ℚ)

/-- The size of a binary linear code (number of codewords). -/
noncomputable def codeSize (C : BinaryLinearCode n) : ℕ :=
  Set.ncard (C : Set (Fin n → ZMod 2))

/-- The Krawtchouk polynomial K_k(x; n) = ∑_{j=0}^{k} (-1)^j * C(x,j) * C(n-x, k-j). -/
def krawtchouk (nn k x : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1) ^ j * (Nat.choose x j : ℤ) * (Nat.choose (nn - x) (k - j) : ℤ)

/-- Basic property: K_0(x; n) = 1. -/
theorem krawtchouk_zero (nn x : ℕ) : krawtchouk nn 0 x = 1 := by
  simp [krawtchouk]

/-
K_1(x; n) = n - 2x.
-/
theorem krawtchouk_one (nn x : ℕ) (hx : x ≤ nn) : krawtchouk nn 1 x = nn - 2 * x := by
  unfold krawtchouk;
  rcases x with ( _ | x ) <;> simp_all +decide [ Finset.sum_range_succ' ] ; linarith

/-- The MacWilliams identity: the weight distribution of the dual code
    is determined by the weight distribution of the original code via
    Krawtchouk polynomials.
    B_k = (1/|C|) * ∑_{i=0}^{n} A_i * K_k(i; n) -/
theorem macwilliams_identity (C : BinaryLinearCode n) (k : ℕ) (hk : k ≤ n)
    (hC : codeSize C > 0) :
    (weightCount (dual C) k : ℚ) =
    (1 / (codeSize C : ℚ)) *
    ∑ i ∈ Finset.range (n + 1), (weightCount C i : ℚ) * (krawtchouk n k i : ℚ) := by
  sorry

/-! ## Pless Power Moment Identities

The k-th power moment of the weight distribution is:
  M_k(C) = ∑_w w^k * A_w = ∑_{c ∈ C} wt(c)^k

The Pless identities relate M_k(C) to M_j(C⊥) for j ≤ k.
For binary codes, the first few identities are:

  M_0(C⊥) = |C⊥| = 2^(n-k)
  M_1(C⊥) = (n/2) * |C⊥| - (1/|C|) * M_1(C) (not quite - these are more complex)

More precisely, the Pless power moment identities state:
  ∑_{c⊥ ∈ C⊥} wt(c⊥)^k = (1/|C|) * ∑_{c ∈ C} P_k(wt(c))
where P_k is a polynomial related to Krawtchouk polynomials.
-/

/-- The k-th power moment of the weight distribution.
    This uses Set.ncard since C may not be Fintype directly. -/
noncomputable def powerMomentQ (C : BinaryLinearCode n) (k : ℕ) : ℚ :=
  ∑ w ∈ Finset.range (n + 1), (w ^ k : ℚ) * (weightCount C w : ℚ)

/-- The 0th power moment equals the code size. -/
theorem powerMoment_zero (C : BinaryLinearCode n) :
    powerMomentQ C 0 = (codeSize C : ℚ) := by
  sorry

/-- The 1st power moment of the dual code (Pless identity for k=1).
    M_1(C⊥) = (n * |C⊥|) / 2 -/
theorem pless_moment_one (C : BinaryLinearCode n) (hC : codeSize C > 0) :
    powerMomentQ (dual C) 1 = (n * codeSize (dual C) : ℚ) / 2 := by
  sorry

/-- The 2nd Pless power moment identity.
    M_2(C⊥) relates to M_1(C) and code parameters. -/
theorem pless_moment_two (C : BinaryLinearCode n) (hC : codeSize C > 0) :
    powerMomentQ (dual C) 2 =
    (n * (n + 1) : ℚ) / 4 * (codeSize (dual C) : ℚ) -
    (1 / (codeSize C : ℚ)) * powerMomentQ C 1 := by
  sorry

/-- The 3rd Pless power moment identity. -/
theorem pless_moment_three (C : BinaryLinearCode n) (hC : codeSize C > 0) :
    powerMomentQ (dual C) 3 =
    (n ^ 2 * (n + 3) : ℚ) / 8 * (codeSize (dual C) : ℚ)
    - (3 * n - 2 : ℚ) / (4 * (codeSize C : ℚ)) * powerMomentQ C 1
    + (1 / (codeSize C : ℚ)) * powerMomentQ C 2 := by
  sorry

end BinaryLinearCode

/-! ## Application: Solving for Weight Distribution from Moments

If a code has exactly `t` distinct nonzero weights w₁, ..., wₜ,
then the number of codewords A_{w₁}, ..., A_{wₜ} of each weight
can be determined from `t` independent Pless moment equations plus
the constraint A₀ = 1.

For t = 3 (as in Kasami codes with weights 2^(m-1) - 2^s, 2^(m-1), 2^(m-1) + 2^s),
three moment equations suffice to determine A₁, A₂, A₃.
-/

/-- Given three distinct weights and three moment values, the weight counts
    are uniquely determined by a 3×3 Vandermonde system. -/
theorem weight_distribution_from_moments
    (w₁ w₂ w₃ : ℕ) (hw12 : w₁ ≠ w₂) (hw13 : w₁ ≠ w₃) (hw23 : w₂ ≠ w₃)
    (M₁ M₂ M₃ : ℚ)
    (A₁ A₂ A₃ : ℚ)
    (h1 : A₁ * w₁ + A₂ * w₂ + A₃ * w₃ = M₁)
    (h2 : A₁ * w₁ ^ 2 + A₂ * w₂ ^ 2 + A₃ * w₃ ^ 2 = M₂)
    (h3 : A₁ * w₁ ^ 3 + A₂ * w₂ ^ 3 + A₃ * w₃ ^ 3 = M₃) :
    -- The solution equals (A₁, A₂, A₃)
    ∀ (B₁ B₂ B₃ : ℚ),
      B₁ * w₁ + B₂ * w₂ + B₃ * w₃ = M₁ →
      B₁ * w₁ ^ 2 + B₂ * w₂ ^ 2 + B₃ * w₃ ^ 2 = M₂ →
      B₁ * w₁ ^ 3 + B₂ * w₂ ^ 3 + B₃ * w₃ ^ 3 = M₃ →
      B₁ = A₁ ∧ B₂ = A₂ ∧ B₃ = A₃ := by
  sorry

end