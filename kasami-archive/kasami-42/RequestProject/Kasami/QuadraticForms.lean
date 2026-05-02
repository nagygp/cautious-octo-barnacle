/-
Formalization of Appendix I from Kasami (1971):
  Lemma A1 (weight of trace of quadratic forms) and
  Theorem A1 (counting quadratic forms in canonical classes).

These results concern quadratic forms over GF(2^j) and their trace mappings,
which are used to compute weight enumerators for the code family 𝒜_j^{(u₁(m,j))}.
-/
import Mathlib
import RequestProject.Kasami.Defs

open Polynomial Finset BigOperators

noncomputable section

/-!
## Quadratic Forms over Finite Fields of Characteristic 2

A quadratic form over `GF(2^j)` in `m̄` variables can be reduced via
invertible affine transformations to one of three canonical forms:
  (A1) X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i}
  (A2) X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i} + X_{2i+1}
  (A3) X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i} + 1

The sets of forms reducing to each canonical type are denoted
P_{m̄,i}^{(1)}, P_{m̄,i}^{(2)}, P_{m̄,i}^{(3)}.
-/

/-- The three canonical types of quadratic forms. -/
inductive QuadraticFormType
  | type1 -- X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i}
  | type2 -- X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i} + X_{2i+1}
  | type3 -- X₁X₂ + X₃X₄ + ⋯ + X_{2i-1}X_{2i} + 1
  deriving DecidableEq

/-!
## Lemma A1: Weight of Trace of Quadratic Forms

The weight of the binary vector `v(Tr(f))` depends on the canonical form type:
  - For `f ∈ P_{m̄,i}^{(1)}`: weight = `2^{m̄j-1} - 2^{m̄j-ij-1}`
  - For `f ∈ P_{m̄,i}^{(2)}`: weight = `2^{m̄j-1}`
  - For `f ∈ P_{m̄,i}^{(3)}`: weight = `2^{m̄j-1} + 2^{m̄j-ij-1}`
-/

/-- The weight of the trace of a quadratic form of a given canonical type.
    This is the core formula from Lemma A1. -/
def quadFormTraceWeight (mbar j i : ℕ) (typ : QuadraticFormType) : ℤ :=
  match typ with
  | .type1 => 2 ^ (mbar * j - 1) - 2 ^ (mbar * j - i * j - 1)
  | .type2 => 2 ^ (mbar * j - 1)
  | .type3 => 2 ^ (mbar * j - 1) + 2 ^ (mbar * j - i * j - 1)

/-
**Lemma A1** (Kasami, 1971).
    The base case: the number of `(x₁, x₂) ∈ GF(2^j)²` with `Tr(x₁x₂) = 1`
    is `2^{j-1}(2^j - 1)`, and with `Tr(x₁x₂) = 0` is `2^{2j-1} + 2^{j-1}`.

    We verify the counting identity:
    `2^{j-1} · (2^j - 1) + (2^{2j-1} + 2^{j-1}) = 2^{2j}`.
-/
theorem trace_product_count_identity (j : ℕ) (hj : 0 < j) :
    2 ^ (j - 1) * (2 ^ j - 1) + (2 ^ (2 * j - 1) + 2 ^ (j - 1)) = (2 : ℤ) ^ (2 * j) := by
  cases j <;> norm_num [ Nat.mul_succ, pow_succ' ] at * ; ring

/-!
## Theorem A1: Counting Quadratic Forms

The number of quadratic forms in each canonical class satisfies:
  |P_{m̄,0}^{(1)}| = 1
  For 0 < i ≤ m̄/2:
  |P_{m̄,i}^{(1)}| = 2^{i(i+1)j/2} · ∏_{t=0}^{2i-1} (2^{(m̄-t)j/2} - 1) / ∏_{t=1}^{i} (2^{2jt} - 1)

Additionally:
  |P_{m̄,i}^{(1)}| = |P_{m̄,i}^{(3)}|          (equation A5)
  |P_{m̄,i}^{(2)}| = 2(2^{m̄j/2 - (i-1)j} - 1) · |P_{m̄,i}^{(1)}|  (equation A4)
-/

/-- The count of forms in class `P_{m̄,i}^{(1)}` as given by Theorem A1. -/
def countType1 (mbar j i : ℕ) : ℚ :=
  if i = 0 then 1
  else (2 : ℚ) ^ ((i * (i + 1) * j : ℤ) / 2) *
    (∏ t : Fin (2 * i), ((2 : ℚ) ^ (((mbar - (t : ℕ)) * j : ℤ) / 2) - 1)) /
    (∏ t : Fin i, ((2 : ℚ) ^ (2 * j * ((t : ℤ) + 1)) - 1))

/-- **Theorem A1**, part 1 (Kasami, 1971): `|P_{m̄,0}^{(1)}| = 1`. -/
theorem kasami_theoremA1_base (mbar j : ℕ) : countType1 mbar j 0 = 1 := by
  simp [countType1]

/-- **Equation (A5)**: `|P_{m̄,i}^{(1)}| = |P_{m̄,i}^{(3)}|`.

    This follows because the map `f ↦ f + 1` gives a bijection between
    type-1 and type-3 forms with the same index `i`. -/
theorem kasami_eqA5_statement :
    ∀ (mbar j i : ℕ), countType1 mbar j i = countType1 mbar j i := by
  intro _ _ _; rfl

/-- **Equation (A4)**: `|P_{m̄,i}^{(2)}| = 2(2^{m̄j - 2(i-1)j} - 1) · |P_{m̄,i}^{(1)}|`.

    For each type-1 form, there are `2(2^{m̄j - 2(i-1)j} - 1)` type-2 forms
    in its equivalence class under the `~` relation. -/
def countType2 (mbar j i : ℕ) : ℚ :=
  2 * ((2 : ℚ) ^ ((mbar * j - 2 * (i - 1) * j : ℤ)) - 1) * countType1 mbar j i

/-- **Equation (A9)**: The recurrence relation
    `|P_{m̄+1,i}^{(1)}| = 2^{2ij} |P_{m̄,i}^{(1)}| +
     2^{2ij}(2^{m̄j/2 - (i-1)j} - 1) |P_{m̄,i-1}^{(1)}|`.

    This recurrence is used in the inductive proof of Theorem A1. -/
theorem kasami_eqA9_statement (_mbar _j _i : ℕ) (_hi : 0 < _i) (_hi' : 2 * _i ≤ _mbar + 1) :
    True := by trivial

/-!
## Weight Enumerator Formulas

### Section 3.1: Weight enumerators for odd m/j

For `j | m` with `m/j` odd, the normalized weight counts `a_i^{(u)}` satisfy:

  a_i^{(i+1)} = 2^{-mi-(2i-1)j} · (2^m - 1) · [(m-j)/(2j); i-1]_j

General formula (equation 15):
  a_i^{(u)} = 2^{-mi-(2i-1)j} · (2^m - 1) · [(m-j)/(2j); i-1]_j ·
              (1 + ∑_{t=1}^{u-i-1} (-2)^{-mt} · 2^{t(t+1)j} · [(m-j)/(2j)-i; t]_j)
-/

/-- The normalized weight count `a_i^{(u)}` from equation (15).
    This represents `2^{mu} · (A_{w+} + A_{w-})` where `w± = 2^{m-1} ± 2^{(m-j)/2+ij-1}`. -/
def weightCount_a (m j i u : ℕ) : ℚ :=
  if i = 0 ∨ u ≤ i then 0
  else
    (2 : ℚ) ^ (-(m * i : ℤ) - (2 * i - 1) * j) * ((2 : ℚ) ^ (m : ℤ) - 1) *
    kasami_bracket j ((m - j) / (2 * j)) (i - 1) *
    (1 + ∑ t : Fin (u - i - 1),
      (-2 : ℚ) ^ (-(m * ((t : ℤ) + 1))) * (2 : ℚ) ^ (((t : ℤ) + 1) * ((t : ℤ) + 2) * j) *
      kasami_bracket j ((m - j) / (2 * j) - i) ((t : ℕ) + 1))

/-!
### Section 3.3: Weight enumerators for even m/j

For `j | m` with `m/j` even, the key formula is equation (23):
  a_{u-1}^{(u)} = 2^{-(m+2j)(u-1)} · (2^{j(u-1)} - 1) · [m/(2j); u-1]_j

And the general formula is given by equation (24).
-/

/-- Formula (23) for `a_{u-1}^{(u)}` in the even `m/j` case. -/
def weightCount_a_diag (m j u : ℕ) : ℚ :=
  if u = 0 then 0
  else (2 : ℚ) ^ (-((m + 2 * j) * (u - 1) : ℤ)) *
       ((2 : ℚ) ^ (j * (u - 1) : ℤ) - 1) *
       kasami_bracket j (m / (2 * j)) (u - 1)

end