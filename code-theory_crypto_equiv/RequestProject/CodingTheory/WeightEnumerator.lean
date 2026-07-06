import Mathlib
import RequestProject.CodingTheory.LinearCode

/-!
# Weight distribution and the weight enumerator of a linear code

This module is the next step of the coding-theory development transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It introduces the **weight enumerator** of a code, the homogeneous bivariate
polynomial

`W_C(X, Y) = Σ_{c ∈ C} X^{n - wt c} Y^{wt c} = Σ_{i=0}^{n} A_i X^{n-i} Y^i`,

where `A_i` is the number of codewords of Hamming weight `i` (the *weight
distribution*).  This is the object whose transformation law under dualization is
the **MacWilliams identity** (Ch. 5, Thm 1) — the flagship target of the roadmap
in `CODING_THEORY_DIRECTIONS.md`.  This file provides the definition and its basic
API; it is the foundation the MacWilliams identity is stated on.

Words live in `ι → F` with `[Fintype ι] [Field F] [Fintype F]` (finiteness of `F`
is needed because we count codewords); a code is a `Submodule F (ι → F)`, exactly
as in `RequestProject/CodingTheory/LinearCode.lean`.

## Main definitions

* `weightDistribution C i` — `A_i`, the number of codewords of Hamming weight `i`.
* `weightEnumerator C` — the bivariate polynomial `W_C(X, Y)` over `ℤ`.

## Main results

* `weightDistribution_zero` — `A_0 = 1` (only the zero word has weight `0`).
* `sum_weightDistribution` — `Σ_{i=0}^{n} A_i = |C|` (the `A_i` partition `C`).
* `weightEnumerator_eq_sum_weightDistribution` — the enumerator written via the
  weight distribution `Σ_i A_i X^{n-i} Y^i`.
* `weightEnumerator_eval_one_one` — `W_C(1,1) = |C|`.
-/

namespace CodingTheory

open scoped Classical
open MvPolynomial

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

noncomputable instance instFintypeSubmodule (C : Submodule F (ι → F)) : Fintype C :=
  Fintype.ofFinite _

/-- The **weight distribution** `A_i` of a code: the number of codewords of
Hamming weight exactly `i`. -/
noncomputable def weightDistribution (C : Submodule F (ι → F)) (i : ℕ) : ℕ :=
  Nat.card {c : C // hammingNorm (c : ι → F) = i}

/-- The **weight enumerator** of a code:
`W_C(X, Y) = Σ_{c ∈ C} X^{n - wt c} Y^{wt c}`, a homogeneous degree-`n`
polynomial in two variables (here `X = X 0`, `Y = X 1`), with integer
coefficients. -/
noncomputable def weightEnumerator (C : Submodule F (ι → F)) : MvPolynomial (Fin 2) ℤ :=
  ∑ c : C, (X 0) ^ (Fintype.card ι - hammingNorm (c : ι → F)) *
    (X 1) ^ (hammingNorm (c : ι → F))

omit [Fintype F] in
/--
Only the zero codeword has Hamming weight `0`, so `A_0 = 1`.
-/
theorem weightDistribution_zero (C : Submodule F (ι → F)) :
    weightDistribution C 0 = 1 := by
  simp_all +decide [ weightDistribution ]

/--
The weight distribution partitions the code: `Σ_{i=0}^{n} A_i = |C|`.
-/
theorem sum_weightDistribution (C : Submodule F (ι → F)) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1), weightDistribution C i = Fintype.card C := by
  simp +decide [ weightDistribution ];
  simp +decide only [Fintype.card_subtype];
  rw [ ← Finset.card_biUnion ];
  · convert Finset.card_univ;
    all_goals try infer_instance;
    · ext x; simp +decide [ hammingNorm ] ;
      exact Finset.card_le_univ _;
    · rw [ Fintype.card_of_subtype ] ; aesop;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;

/--
The weight enumerator written through the weight distribution:
`W_C(X, Y) = Σ_{i=0}^{n} A_i X^{n-i} Y^i`.
-/
theorem weightEnumerator_eq_sum_weightDistribution (C : Submodule F (ι → F)) :
    weightEnumerator C =
      ∑ i ∈ Finset.range (Fintype.card ι + 1),
        (weightDistribution C i : ℤ) •
          ((X 0) ^ (Fintype.card ι - i) * (X 1) ^ i) := by
  unfold weightDistribution; simp +decide [ Fintype.card_subtype ] ;
  rw [ Finset.sum_congr rfl fun i hi => by rw [ Finset.card_filter ] ];
  simp +decide only [Nat.cast_sum, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  simp +decide [ hammingNorm ];
  exact fun a ha => Finset.card_le_univ _

/--
Evaluating the weight enumerator at `X = Y = 1` counts the codewords:
`W_C(1,1) = |C|`.
-/
theorem weightEnumerator_eval_one_one (C : Submodule F (ι → F)) :
    MvPolynomial.eval (fun _ => (1 : ℤ)) (weightEnumerator C) = Fintype.card C := by
  unfold weightEnumerator; simp +decide ;

end CodingTheory