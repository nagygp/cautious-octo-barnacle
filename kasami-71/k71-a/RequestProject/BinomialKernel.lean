/-
  BinomialKernel.lean
  
  Theorem 23 (Budaghyan): The linearized derivative of the Budaghyan binomial
  f(x) = x^{2^{2k}+2^k+1} + ω·x^{2^{2k}+1} + ω^{2^k}·x^{2^k+1}
  has a kernel of dimension at most 1 over F_2.
  
  This establishes the APN property of the Budaghyan binomial construction.
  
  Reference: Theorem 23 in "Construction and Analysis of Cryptographic Functions"
  by Lilya Budaghyan, and the Bracken-McGuire paper.
-/
import Mathlib
import RequestProject.GoldAPN

set_option maxHeartbeats 4000000

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ### The Budaghyan binomial function -/

/-- The Budaghyan binomial exponent: d = 2^{2k} + 2^k + 1 -/
def budaghyanExp (k : ℕ) : ℕ := 2 ^ (2 * k) + 2 ^ k + 1

/-- The Budaghyan binomial function:
    f(x) = x^{2^{2k}+2^k+1} + ω·x^{2^{2k}+1} + ω^{2^k}·x^{2^k+1}
    where ω has order 2^{2k}+2^k+1 in F*. -/
noncomputable def budaghyanFunc (k : ℕ) (ω : F) (x : F) : F :=
  x ^ (2 ^ (2 * k) + 2 ^ k + 1) + ω * x ^ (2 ^ (2 * k) + 1) +
  ω ^ (2 ^ k) * x ^ (2 ^ k + 1)

/-- The difference derivative of the Budaghyan binomial:
    Δ_u f(x) = f(x + u) + f(x) -/
noncomputable def budaghyanDiffDeriv (k : ℕ) (ω u x : F) : F :=
  budaghyanFunc k ω (x + u) + budaghyanFunc k ω x

/-! ### Phase A: Algebraic Reduction -/

/-- The linearized polynomial coefficient A, depending on ω -/
noncomputable def linCoeffA (k : ℕ) (ω : F) (u : F) : F :=
  1 + ω * u ^ (2 ^ k - 1) + ω ^ (2 ^ k)

/-- The linearized polynomial coefficient B -/
noncomputable def linCoeffB (k : ℕ) (ω : F) (u : F) : F :=
  1 + ω ^ (2 ^ k) * u ^ (2 ^ (2 * k) - 2 ^ k) + ω * u ^ (2 ^ (2 * k) - 1)

/-- The reduced linearized polynomial L(y) = y^{2^{2k}} + A·y^{2^k} + B·y -/
noncomputable def linPoly (k : ℕ) (ω u : F) (y : F) : F :=
  y ^ (2 ^ (2 * k)) + (linCoeffA k ω u) * y ^ (2 ^ k) + (linCoeffB k ω u) * y

/-- The Lean polynomial corresponding to L(Y) = Y^{2^{2k}} + A·Y^{2^k} + B·Y -/
noncomputable def linPolyPoly (k : ℕ) (A B : F) : Polynomial F :=
  Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.C A * Polynomial.X ^ (2 ^ k) +
  Polynomial.C B * Polynomial.X

/-- Phase A main result: Δ_u f(x) = 0 with u ≠ 0 reduces to L(x·u⁻¹) = 0 -/
theorem budaghyan_deriv_reduces_to_linPoly (k : ℕ) (ω u x : F) (hu : u ≠ 0) :
    budaghyanDiffDeriv k ω u x = 0 →
    linPoly k ω u (x * u⁻¹) = 0 := by
  sorry

/-! ### Phase B: Root Counting via Polynomial Degree -/

section PhaseB
variable {F : Type*} [Field F] [CharP F 2]

/-
The roots of L form an F_2-vector subspace of F (since L is linearized/additive)
-/
lemma linPoly_additive (k : ℕ) (ω u : F) (y₁ y₂ : F) :
    linPoly k ω u (y₁ + y₂) = linPoly k ω u y₁ + linPoly k ω u y₂ := by
  unfold linPoly; ring;
  rw [ add_pow_char_pow, add_pow_char_pow ] ; ring

end PhaseB

/-- The kernel of L has dimension at most 2k over F_2,
    since L has degree 2^{2k} and its roots form an F_2-subspace. -/
lemma linPoly_kernel_dim_le (k : ℕ) (ω u : F) (hu : u ≠ 0) :
    Fintype.card {y : F | linPoly k ω u y = 0} ≤ 2 ^ (2 * k) := by
  sorry

/-- Under the conditions of Theorem 23 (gcd(s, 3k) = 1 where s parameterizes ω,
    and g₁ ≠ g₂), the kernel has at most 2 elements (dimension ≤ 1 over F_2). 
    
    This uses the Bracken-McGuire factorization: L(y) factors as a composition
    of Gold-type linearized polynomials, and the coprimality condition ensures
    each factor has small kernel. -/
theorem linPoly_kernel_le_two (n k s : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime_k : Nat.Coprime k n)
    (hcoprime_s : Nat.Coprime s (3 * k))
    (ω u : F) (hu : u ≠ 0)
    (hω_order : orderOf ω = 2 ^ (2 * k) + 2 ^ k + 1) :
    Fintype.card {y : F | linPoly k ω u y = 0} ≤ 2 := by
  sorry

/-! ### Main Theorem: binomial_kernel_small -/

/-- **Theorem 23 (Budaghyan)**: The linearized derivative of the Budaghyan binomial
    has a kernel of dimension at most 1.
    
    Equivalently: for u ≠ 0, the equation Δ_u f(x) = 0 has at most 2 solutions
    (which includes 0 and u), so the binomial is APN. -/
theorem binomial_kernel_small (n k s : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime_k : Nat.Coprime k n)
    (hcoprime_s : Nat.Coprime s (3 * k))
    (ω u : F) (hu : u ≠ 0)
    (hω_order : orderOf ω = 2 ^ (2 * k) + 2 ^ k + 1) :
    Fintype.card {x : F | budaghyanDiffDeriv k ω u x = 0} ≤ 2 := by
  sorry