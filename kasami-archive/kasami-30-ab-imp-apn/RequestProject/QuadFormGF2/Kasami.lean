/-
# Kasami Power Function and Quadratic Forms over GF(2^n)

This file connects the general quadratic form theory to the specific setting
of Kasami codes, where the quadratic forms arise from the Kasami power function
x^d with d = 2^{2s} - 2^s + 1 on GF(2^n).

## Main Definitions

- `kasamiExponent`: The Kasami exponent d = 2^{2s} - 2^s + 1

## Main Results

- `kasamiExponent_one`, `kasamiExponent_two`: concrete values
- Docstring proof outline of the Kasami three-valued Walsh spectrum

## Mathematical Context

The Kasami power function f(x) = x^d on GF(2^n) where d = 2^{2s} - 2^s + 1 is
a fundamental object in coding theory and sequence design. Its Walsh-Hadamard
transform W_f(a) = ∑_{x ∈ GF(2^n)} (-1)^{Tr(a·x + x^d)} can be analyzed via:

1. The quadratic form Q_a(x) = Tr(a·x^d) associated to a ∈ GF(2^n)
2. The bilinear form B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)
3. The rank of B_a, which determines |S(Q_a)| via the main connection theorem
4. The fact that for the Kasami exponent, the rank of B_a is either n-1 or n
   (when gcd(s,n) = 1), yielding the three-valued spectrum.

The Walsh spectrum {0, ±2^{(n+1)/2}} makes Kasami functions optimal for
constructing error-correcting codes (Kasami codes) with minimal distance
properties close to the Plotkin bound.
-/

import Mathlib
import RequestProject.QuadFormGF2.GaussSum

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical in
noncomputable section

/-! ## Kasami Exponent -/

/-- The Kasami exponent: d = 2^{2s} - 2^s + 1.
    For this to define a valid power function on GF(2^n) \ {0},
    we need gcd(d, 2^n - 1) to be small. -/
def kasamiExponent (s : ℕ) : ℕ := 2 ^ (2 * s) - 2 ^ s + 1

/-- The Kasami exponent for s=1 is 3 (the cubing map / Gold function) -/
lemma kasamiExponent_one : kasamiExponent 1 = 3 := by
  simp [kasamiExponent]

/-- The Kasami exponent for s=2 is 13 -/
lemma kasamiExponent_two : kasamiExponent 2 = 13 := by
  simp [kasamiExponent]

/-! ## Trace-based quadratic forms on GF(2^n)

The absolute trace from GF(2^n) to GF(2) is:
  Tr(x) = x + x^2 + x^{2^2} + ... + x^{2^{n-1}}
This is a GF(2)-linear map from GF(2^n) to GF(2).

For the Kasami function, the key quadratic form is
  Q_a(x) = Tr(a · x^d) where Tr is the absolute trace GF(2^n) → GF(2).

The associated bilinear form is:
  B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)
           = Tr(a · ((x+y)^d + x^d + y^d))

For the Kasami exponent d = 2^{2s} - 2^s + 1, this simplifies to
a sum involving cross-terms that gives B_a rank control.
-/

/-! ## Kasami three-valued spectrum (outline)

**Theorem (Kasami three-valued spectrum).**

Let n be odd with gcd(s, n) = 1. For the Kasami exponent d = 2^{2s} - 2^s + 1,
the Walsh-Hadamard transform

  W(a) = ∑_{x ∈ GF(2^n)} (-1)^{Tr(a·x^d)}

takes values in {0, 2^{(n+1)/2}, -2^{(n+1)/2}}.

**Proof outline using the quadratic form → Gauss sum connection:**

1. Define Q_a(x) = Tr(a · x^d). This is a quadratic form Q_a : GF(2^n) → GF(2)
   over the F_2-vector space GF(2^n).

2. The associated bilinear form B_a has rank r_a where r_a ∈ {n-1, n}
   when gcd(s,n) = 1 (this requires analysis of the linearized polynomial
   associated to the Kasami exponent).

3. By `QuadFormF2.expSum_sq_eq_card_mul_radical_card` (our main connection theorem):
   - If Q_a|_{rad} = 0: W(a)² = 2^n · 2^{n - r_a}
     * If r_a = n-1: W(a)² = 2^{n+1}, so W(a) = ±2^{(n+1)/2}
     * If r_a = n (i.e., rad = {0}): W(a)² = 2^n · 1 = 2^n... but this
       only happens when a = 0, giving W(0) = 2^n.
   - If Q_a|_{rad} ≠ 0: W(a) = 0 by `QuadFormF2.expSum_zero_of_radical_nonvanishing`.

4. Therefore W(a) ∈ {0, ±2^{(n+1)/2}} for all a ≠ 0.
-/

end
