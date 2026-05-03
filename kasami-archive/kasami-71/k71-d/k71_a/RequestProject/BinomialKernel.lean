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
import k71_a.RequestProject.GoldAPN

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

/-- The delta derivative (reduced): Δ_u f(x) = f(x + u) + f(x) + f(u) -/
noncomputable def budaghyanDeltaDeriv (k : ℕ) (ω u x : F) : F :=
  budaghyanFunc k ω (x + u) + budaghyanFunc k ω x + budaghyanFunc k ω u

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

/-! ### Key char 2 identity -/

/-- In char 2, (y+1)^(2^a+1) + y^(2^a+1) = y^(2^a) + y + 1 -/
lemma gold_shift_identity (y : F) (a : ℕ) :
    (y + 1) ^ (2 ^ a + 1) + y ^ (2 ^ a + 1) = y ^ (2 ^ a) + y + 1 := by
  have h : (y + 1) ^ (2 ^ a) = y ^ (2 ^ a) + 1 := by
    rw [add_pow_expChar_pow]; simp
  rw [pow_succ, pow_succ, h]
  have : (y ^ 2 ^ a + 1) * (y + 1) = y ^ 2 ^ a * y + y ^ 2 ^ a + y + 1 := by ring
  rw [this]
  nth_rw 1 [show y ^ 2 ^ a * y + y ^ 2 ^ a + y + 1 + y ^ 2 ^ a * y =
    (y ^ 2 ^ a * y + y ^ 2 ^ a * y) + (y ^ 2 ^ a + y + 1) from by ring]
  rw [CharTwo.add_self_eq_zero]
  simp

/-- Phase A main result: Δ_u f(x) = 0 with u ≠ 0 reduces to L(x·u⁻¹) = 0.
    NOTE: This requires the ω order condition to ensure the nonlinear
    terms in the Kasami derivative are properly absorbed. -/
theorem budaghyan_deriv_reduces_to_linPoly (n k s : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime_k : Nat.Coprime k n)
    (hcoprime_s : Nat.Coprime s (3 * k))
    (ω u x : F) (hu : u ≠ 0)
    (hω_order : orderOf ω = 2 ^ (2 * k) + 2 ^ k + 1) :
    budaghyanDiffDeriv k ω u x = 0 →
    linPoly k ω u (x * u⁻¹) = 0 := by
  sorry

/-! ### Phase B: Root Counting via Polynomial Degree -/

section PhaseB
variable {F : Type*} [Field F] [CharP F 2]

/-- The roots of L form an F_2-vector subspace of F (since L is linearized/additive) -/
lemma linPoly_additive (k : ℕ) (ω u : F) (y₁ y₂ : F) :
    linPoly k ω u (y₁ + y₂) = linPoly k ω u y₁ + linPoly k ω u y₂ := by
  unfold linPoly; ring;
  rw [ add_pow_char_pow, add_pow_char_pow ] ; ring

end PhaseB

/-- The kernel of L has dimension at most 2k over F_2,
    since L has degree 2^{2k} and its roots form an F_2-subspace. -/
lemma linPoly_kernel_dim_le (k : ℕ) (ω u : F) (hu : u ≠ 0) :
    Fintype.card {y : F | linPoly k ω u y = 0} ≤ 2 ^ (2 * k) := by
  have h_deg : (Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.C (linCoeffA k ω u) * Polynomial.X ^ (2 ^ k) + Polynomial.C (linCoeffB k ω u) * Polynomial.X : Polynomial F).natDegree ≤ 2 ^ (2 * k) := by
    refine' le_trans ( Polynomial.natDegree_add_le _ _ ) ( max_le _ _ );
    · refine' le_trans ( Polynomial.natDegree_add_le _ _ ) _ ; norm_num;
      exact le_trans ( Polynomial.natDegree_C_mul_X_pow_le _ _ ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) );
    · exact le_trans ( Polynomial.natDegree_mul_le .. ) ( by norm_num; linarith [ Nat.one_le_pow ( 2 * k ) 2 zero_lt_two ] );
  by_cases h : Polynomial.X ^ 2 ^ ( 2 * k ) + Polynomial.C ( linCoeffA k ω u ) * Polynomial.X ^ 2 ^ k + Polynomial.C ( linCoeffB k ω u ) * Polynomial.X = 0 <;> simp_all +decide [ Polynomial.natDegree_le_iff_degree_le ];
  · replace h := congr_arg ( fun p => p.coeff ( 2 ^ ( 2 * k ) ) ) h ; simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
    simp_all +decide [ Polynomial.coeff_X, pow_mul' ];
    split_ifs at h <;> simp_all +decide [ pow_succ', mul_assoc ];
    · simp_all +decide [ linCoeffA, linCoeffB, linPoly ];
      grind;
    · simp_all +decide [ show k = 0 by linarith ];
    · rw [ eq_comm ] at * ; aesop;
  · have h_roots : (Polynomial.roots (Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.C (linCoeffA k ω u) * Polynomial.X ^ (2 ^ k) + Polynomial.C (linCoeffB k ω u) * Polynomial.X : Polynomial F)).toFinset ⊇ Finset.image (fun x => x) (Finset.filter (fun x => linPoly k ω u x = 0) Finset.univ) := by
      simp +decide [ Finset.subset_iff, linPoly ];
      exact fun x hx => ⟨ h, hx ⟩;
    have := Finset.card_mono h_roots; simp_all +decide [ Fintype.card_subtype ] ;
    exact this.trans ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( Polynomial.natDegree_le_of_degree_le h_deg ) ) )

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
