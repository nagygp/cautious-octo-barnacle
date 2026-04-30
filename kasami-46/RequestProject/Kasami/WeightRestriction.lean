/-
# BCH Bound and Weight Restrictions (Theorems 1 and 2)

This file formalizes:
- Theorem 1: The generalized BCH bound for cyclic codes
- Theorem 2: Weight restrictions via the Berlekamp-Sloane method

## References

- Kasami, T. (1971). The Weight Enumerators for Several Classes of Subcodes
  of the 2nd Order Binary Reed-Muller Codes.
- Bose, R.C. & Ray-Chaudhuri, D.K. (1960). On a class of error correcting
  binary group codes.
-/

import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.SymmPoly

open Finset BigOperators

noncomputable section

/-! ## The BCH Bound (Theorem 1)

The BCH bound states: if a cyclic code of length n over GF(q) has generator
polynomial g(x) with consecutive roots α^b, α^(b+1), ..., α^(b+d-2) where
α is a primitive n-th root of unity, then the minimum distance is at least d.

The proof uses the fact that the syndrome matrix of any codeword c is:
  S = [S_b, S_{b+1}, ..., S_{b+d-2}]
If c has weight w < d, the syndrome matrix gives a Vandermonde system
of rank w < d-1, which would force all syndromes to be zero, contradicting
c being nonzero.
-/

variable {m : ℕ} (hm : m ≥ 1)

/-- The Vandermonde matrix formed by locators of a codeword. -/
def locatorVandermonde {F : Type*} [CommRing F] {w : ℕ}
    (locators : Fin w → F) (d : ℕ) : Matrix (Fin d) (Fin w) F :=
  fun i j => (locators j) ^ (i : ℕ)

/-
If w < d and the locators are distinct, the Vandermonde matrix
    has rank w (= number of columns), so the system S = V · c has
    nontrivial solutions only if S = 0.
-/
theorem vandermonde_rank_constraint {F : Type*} [Field F] {w d : ℕ}
    (locators : Fin w → F) (hwd : w < d)
    (h_distinct : Function.Injective locators) :
    -- Any nonzero linear combination of columns is nonzero
    ∀ (coeffs : Fin w → F), (∃ i, coeffs i ≠ 0) →
    ∃ (row : Fin d), ∑ j, coeffs j * (locators j) ^ (row : ℕ) ≠ 0 := by
  intro coeffs h_nonzero
  by_contra h_contra
  push_neg at h_contra
  have h_det : Matrix.det (Matrix.of (fun i j : Fin w => locators j ^ (i : ℕ))) ≠ 0 := by
    erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
    exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| h_distinct.ne <| ne_of_gt <| Finset.mem_Ioi.mp hj;
  have h_vandermonde : Matrix.mulVec (Matrix.of (fun i j : Fin w => locators j ^ (i : ℕ))) coeffs = 0 := by
    ext i; specialize h_contra ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ; simp_all +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
  exact h_nonzero.elim fun i hi => hi <| by simpa [ h_det ] using Matrix.eq_zero_of_mulVec_eq_zero h_det h_vandermonde |> fun h => by simpa [ h ] ;

/-- **Theorem 1 (BCH Bound)**: If a cyclic code has `d - 1` consecutive roots
    α^b, α^(b+1), ..., α^(b+d-2) (where α is a primitive n-th root of unity),
    then any nonzero codeword has weight at least d.

    This is formalized as: given locators (positions where c is nonzero) that are
    distinct elements of GF(2^m)*, if all syndromes S_b, ..., S_{b+d-2} are zero,
    then the codeword must be zero (i.e., w = 0). -/
theorem bch_bound {F : Type*} [Field F] {w d b : ℕ}
    (locators : Fin w → F)
    (h_distinct : Function.Injective locators)
    (h_nonzero : ∀ i, locators i ≠ 0)
    (h_syndromes : ∀ j, b ≤ j → j < b + d - 1 →
      syndrome locators j = 0)
    (hwd : w < d) : w = 0 := by
  sorry

/-! ## Weight Restrictions via Berlekamp-Sloane (Theorem 2)

For the 2nd-order Reed-Muller subcode, the codewords are defined by
  c(x) = Tr(ax^(2^s+1) + bx) for x ∈ GF(2^m)*

The key observation: the exponent 2^s + 1 divides 2^m - 1 when m is odd
and s = (m-1)/2.

The weight of such a codeword equals:
  w = 2^(m-1) - (1/2) ∑_{x ∈ GF(2^m)*} (-1)^{Tr(ax^(2^s+1) + bx)}

By analyzing the quadratic form Tr(ax^(2^s+1) + bx) and using the theory
of quadratic forms over GF(2), one shows the weight must be one of:
  {0, 2^(m-1) - 2^s, 2^(m-1), 2^(m-1) + 2^s}
where s = (m-1)/2.
-/

/-- **Theorem 2 (Weight Restriction)**: The weight of any codeword in the
    Kasami subcode is restricted to {0, 2^(m-1) - 2^s, 2^(m-1), 2^(m-1) + 2^s}
    where s = (m-1)/2 and m is odd.

    This follows from the classification of quadratic forms over GF(2):
    - If a = 0, b = 0: weight = 0
    - If a = 0, b ≠ 0: weight = 2^(m-1) (trace is balanced)
    - If a ≠ 0: the quadratic form has rank 2 or m, giving
      weight = 2^(m-1) ± 2^((m-1)/2) or 2^(m-1) -/
theorem kasami_weight_restriction (P : KasamiParams) :
    ∀ w, w ∉ P.possibleWeights →
    ∀ (C : BinaryLinearCode P.codeLength),
    -- Under the assumption that C is the Kasami code with appropriate structure
    BinaryLinearCode.weightCount C w = 0 := by
  sorry

/-! ## Supporting Lemma: Quadratic Form Classification

Over GF(2), every quadratic form Q(x₁, ..., x_m) in m variables can be
reduced to one of:
1. x₁x₂ + x₃x₄ + ... + x_{2r-1}x_{2r} (hyperbolic, rank 2r)
2. x₁x₂ + x₃x₄ + ... + x_{2r-1}x_{2r} + x_{2r+1}² (parabolic, rank 2r+1)

The number of zeros depends on the type:
- Hyperbolic rank 2r: 2^(m-1) + 2^(m-r-1)
- Parabolic rank 2r+1: 2^(m-1) ± 2^(m-(2r+2)/2)
-/

/-- Classification of quadratic forms over GF(2). -/
inductive QuadFormType where
  | zero      : QuadFormType  -- The zero form
  | hyperbolic (r : ℕ) : QuadFormType  -- rank 2r, type +
  | elliptic (r : ℕ) : QuadFormType    -- rank 2r, type -
  | parabolic (r : ℕ) : QuadFormType   -- rank 2r+1
  deriving DecidableEq

/-- The number of zeros of a quadratic form over GF(2^m) of given type. -/
def quadFormZeros (m : ℕ) : QuadFormType → ℕ
  | .zero => 2 ^ m
  | .hyperbolic r => 2 ^ (m - 1) + 2 ^ (m - r - 1)
  | .elliptic r => 2 ^ (m - 1) - 2 ^ (m - r - 1)
  | .parabolic _ => 2 ^ (m - 1)

/-- The quadratic form Tr(ax^(2^s+1)) over GF(2^m) with m odd, s = (m-1)/2,
    and a ≠ 0, has type that gives zero count in {2^(m-1) - 2^s, 2^(m-1), 2^(m-1) + 2^s}. -/
theorem kasami_quadratic_form_type (P : KasamiParams) :
    ∀ (t : QuadFormType),
    t = .hyperbolic ((P.m - 1) / 2) ∨
    t = .elliptic ((P.m - 1) / 2) ∨
    t = .parabolic ((P.m - 1) / 2) →
    quadFormZeros P.m t ∈
      ({2 ^ (P.m - 1) - 2 ^ P.halfExp, 2 ^ (P.m - 1), 2 ^ (P.m - 1) + 2 ^ P.halfExp} : Finset ℕ) := by
  sorry

end