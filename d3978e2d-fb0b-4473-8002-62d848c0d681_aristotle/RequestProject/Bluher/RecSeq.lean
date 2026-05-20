/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# The Recursive Sequence A_r and Bluher's Factorization

This file formalizes the recursive sequence `A_r(x)` from Bluher's theory of
linearized polynomial factorizations over finite fields.

## The Recurrence

  `A_0 = 0, A_1 = 1, A_{r+2} = -A_{r+1} - σ^r(x) · A_r`

where `σ` is a ring endomorphism (Frobenius in the finite field case).

## Cool Patterns and Big Ideas

1. **Continuant Connection**: The recurrence `A_{r+2} = -A_{r+1} - c_r · A_r`
   is a *signed continuant* — the same structure that appears in continued
   fractions, tridiagonal matrix determinants, and Chebyshev polynomials.
   When all `c_r = 1`, this gives (signed) Fibonacci numbers!

2. **Determinantal Interpretation**: `A_r(x)` is the determinant of the
   tridiagonal matrix with `-1` on the diagonal and `σ^j(x)` on the
   subdiagonal. This connects to:
   - Transfer matrices in statistical mechanics
   - The characteristic polynomial of a companion matrix
   - Cluster algebra mutations

3. **Open Question**: For which choices of the sequence `(σ^j(x))_j` does
   the sequence `A_r` eventually vanish? This is related to the rank of
   certain linearized polynomial maps and to the structure of Bluher's
   "exceptional" elements.

4. **Category Theory**: The 2-term recurrence defines a representation of
   the path algebra of the A_∞ quiver. The sequence `(A_r, A_{r+1})` evolves
   by a product of 2×2 matrices — this is a functor from ℕ (viewed as a
   category with a single morphism n → n+1) to GL₂-torsors.
-/

import Mathlib

open Finset Function Matrix BigOperators

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

/-! ## The Recursive Sequence -/

/-- Bluher's recursive sequence parameterized by a ring endomorphism σ and element x.

    `A_0(x) = 0`
    `A_1(x) = 1`
    `A_{r+2}(x) = -A_{r+1}(x) - σ^r(x) · A_r(x)`

    This is a signed continuant polynomial in the iterates `σ^j(x)`. -/
noncomputable def bluherA (σ : R →+* R) (x : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => - bluherA σ x (n + 1) - ((σ ^ n) x) * bluherA σ x n

@[simp] lemma bluherA_zero (σ : R →+* R) (x : R) : bluherA σ x 0 = 0 := rfl
@[simp] lemma bluherA_one (σ : R →+* R) (x : R) : bluherA σ x 1 = 1 := rfl

lemma bluherA_two (σ : R →+* R) (x : R) : bluherA σ x 2 = -1 := by
  -- By definition of `bluherA`, we have:
  have h_def : bluherA σ x 2 = -bluherA σ x 1 - ((σ ^ 0) x) * bluherA σ x 0 := by
    rfl;
  aesop

lemma bluherA_succ_succ (σ : R →+* R) (x : R) (n : ℕ) :
    bluherA σ x (n + 2) = - bluherA σ x (n + 1) - ((σ ^ n) x) * bluherA σ x n := by
  rfl

/-! ## The Transfer Matrix — Functorial Structure -/

/-- The transfer matrix for the recurrence. The sequence `(A_{r+1}, A_r)` evolves as:

    `[A_{r+2}]   [-1  -σ^r(x)] [A_{r+1}]`
    `[A_{r+1}] = [ 1     0   ] [A_r    ]`

    The product of these matrices gives `A_r` as a matrix element —
    this is the **path-ordered exponential** in the discrete setting. -/
noncomputable def bluherMatrix (σ : R →+* R) (x : R) (n : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  !![(-1 : R), -((σ ^ n) x); 1, 0]

/-- The cumulative transfer matrix: product of individual transfer matrices.
    `M_r = T_{r-1} · T_{r-2} · ... · T_0` -/
noncomputable def bluherCumulMatrix (σ : R →+* R) (x : R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | (n + 1) => bluherMatrix σ x n * bluherCumulMatrix σ x n

/-
The transfer matrix has determinant `σ^n(x)`, connecting the sequence
    to invertibility questions over the field.
-/
lemma bluherMatrix_det (σ : R →+* R) (x : R) (n : ℕ) :
    (bluherMatrix σ x n).det = (σ ^ n) x := by
  simp +decide [ bluherMatrix, Matrix.det_fin_two ]

/-
The cumulative transfer matrix determinant telescopes:
    `det(M_r) = ∏_{j=0}^{r-1} σ^j(x) = N_r(x)` (the generalized norm).
-/
lemma bluherCumulMatrix_det (σ : R →+* R) (x : R) (r : ℕ) :
    (bluherCumulMatrix σ x r).det = ∏ j ∈ range r, (σ ^ j) x := by
  induction' r with r ih;
  · exact Matrix.det_one;
  · rw [ Finset.prod_range_succ, ← ih, show bluherCumulMatrix σ x ( r + 1 ) = bluherMatrix σ x r * bluherCumulMatrix σ x r from rfl, Matrix.det_mul, bluherMatrix_det ];
    ring

/-! ## Special Values -/

/-
`A_3(x) = 1 - σ(x)`. Note: the original Coq code had `A_3 = -1 + x` which is only
    correct when σ = id (i.e., q = 1). In general, `A_3 = 1 - σ(x)`.
-/
lemma bluherA_three (σ : R →+* R) (x : R) :
    bluherA σ x 3 = 1 - σ x := by
  -- Substitute the known values of A_1 and A_2 into the recurrence relation for n=1.
  have h_subst : bluherA σ x 3 = - bluherA σ x 2 - (σ x) * bluherA σ x 1 := by
    rfl;
  grind +suggestions

/-
When x = 0, the sequence alternates: `A_r(0) = (-1)^{r-1}` for `r ≥ 1`.
-/
lemma bluherA_zero_arg (σ : R →+* R) (n : ℕ) (hn : 1 ≤ n) :
    bluherA σ 0 n = (-1) ^ (n - 1) := by
  induction' n using Nat.strongRecOn with n ih;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  rcases n with ( _ | n ) <;> simp_all +decide [ bluherA_succ_succ ];
  ring

/-! ## Fibonacci Connection -/

/-
When `σ = id` and `x = -1`, the sequence satisfies `A_{r+2} = -A_{r+1} + A_r`,
    which gives `A_r = (-1)^{r+1} · Fib(r)` where Fib is the Fibonacci sequence.
    This reveals the continuant/Fibonacci structure underlying Bluher's sequence.
-/
lemma bluherA_neg_one_id :
    ∀ (n : ℕ), bluherA (RingHom.id ℤ) (-1) n = (-1) ^ (n + 1) * (Nat.fib n : ℤ) := by
  intro n;
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ *, Nat.fib_add_two ];
  erw [ show bluherA ( RingHom.id ℤ ) ( -1 ) ( n + 3 ) = -bluherA ( RingHom.id ℤ ) ( -1 ) ( n + 2 ) - ( ( RingHom.id ℤ ) ^ ( n + 1 ) ) ( -1 ) * bluherA ( RingHom.id ℤ ) ( -1 ) ( n + 1 ) by rfl ] ; norm_num [ pow_succ, ih n ( by linarith ), ih ( n + 1 ) ( by linarith ), ih ( n + 2 ) ( by linarith ) ] ; ring;
  rw [ show 2 + n = n + 2 by ring, show 1 + n = n + 1 by ring ] ; norm_num [ Nat.fib_add_two ] ; ring;