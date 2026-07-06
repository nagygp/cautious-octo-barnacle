/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import RequestProject.Upstream.LinearCode

/-!
# Weight distribution and the weight enumerator of a linear code

> Intended Mathlib target path: `Mathlib/InformationTheory/WeightEnumerator.lean`
> (it builds directly on `Mathlib/InformationTheory/LinearCode.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in transitively
> should be minimised (e.g. with `shake`) to the relevant modules.

This file introduces the **weight enumerator** of a linear code over a finite
field, the homogeneous bivariate polynomial

`W_C(X, Y) = Σ_{c ∈ C} X^{n - wt c} Y^{wt c} = Σ_{i=0}^{n} A_i X^{n-i} Y^i`,

where `A_i` is the number of codewords of Hamming weight `i` (the *weight
distribution*).  This is the object whose transformation law under dualization is
the MacWilliams identity (MacWilliams–Sloane, Ch. 5, Thm 1).

We fix a finite field `F` with `q = #F` elements and a finite index type `ι` of
coordinate positions (`n = #ι`), so the ambient word space is `ι → F`, exactly as
for `LinearCode`.

## Main definitions

* `LinearCode.weightDistribution C i` — `A_i`, the number of codewords of weight
  `i`.
* `LinearCode.weightEnumerator C` — the bivariate polynomial `W_C(X, Y)` over `ℤ`.

## Main results

* `LinearCode.weightDistribution_zero` — `A_0 = 1`.
* `LinearCode.sum_weightDistribution` — `Σ_{i=0}^{n} A_i = |C|`.
* `LinearCode.weightEnumerator_eq_sum_weightDistribution` —
  `W_C(X, Y) = Σ_i A_i X^{n-i} Y^i`.
* `LinearCode.weightEnumerator_eval_one_one` — `W_C(1,1) = |C|`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 5.)

## Tags

linear code, coding theory, Hamming distance, weight, weight enumerator, weight
distribution, MacWilliams
-/

open scoped Classical
open MvPolynomial

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

namespace LinearCode

noncomputable instance instFintypeSubtype (C : LinearCode ι F) : Fintype C :=
  Fintype.ofFinite _

/-- The **weight distribution** `A_i` of a code: the number of codewords of
Hamming weight exactly `i`. -/
noncomputable def weightDistribution (C : LinearCode ι F) (i : ℕ) : ℕ :=
  Nat.card {c : C // hammingNorm (c : ι → F) = i}

/-- The **weight enumerator** `W_C(X, Y) = Σ_{c ∈ C} X^{n - wt c} Y^{wt c}` of a
code, a homogeneous degree-`n` polynomial in two variables (`X = X 0`, `Y = X 1`)
with integer coefficients. -/
noncomputable def weightEnumerator (C : LinearCode ι F) : MvPolynomial (Fin 2) ℤ :=
  ∑ c : C, (X 0) ^ (Fintype.card ι - hammingNorm (c : ι → F)) *
    (X 1) ^ (hammingNorm (c : ι → F))

omit [Fintype F] in
/-- Only the zero codeword has Hamming weight `0`, so `A_0 = 1`. -/
theorem weightDistribution_zero (C : LinearCode ι F) :
    weightDistribution C 0 = 1 := by
  simp_all +decide [ weightDistribution ]

/-- The weight distribution partitions the code: `Σ_{i=0}^{n} A_i = |C|`. -/
theorem sum_weightDistribution (C : LinearCode ι F) :
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

/-
The weight enumerator written through the weight distribution:
`W_C(X, Y) = Σ_{i=0}^{n} A_i X^{n-i} Y^i`.
-/
theorem weightEnumerator_eq_sum_weightDistribution (C : LinearCode ι F) :
    weightEnumerator C =
      ∑ i ∈ Finset.range (Fintype.card ι + 1),
        (weightDistribution C i : ℤ) •
          ((X 0) ^ (Fintype.card ι - i) * (X 1) ^ i) := by
  simp +decide [ weightEnumerator ];
  simp +decide only [weightDistribution];
  have h_sum_fiberwise : ∀ (T : C → MvPolynomial (Fin 2) ℤ), (∑ c : C, T c) = ∑ i ∈ Finset.range (Fintype.card ι + 1), ∑ c ∈ Finset.filter (fun c : C => hammingNorm (c : ι → F) = i) Finset.univ, T c := by
    intro T;
    rw [ ← Finset.sum_biUnion ];
    · rcongr c ; simp +decide [ hammingNorm ];
      exact Finset.card_le_univ _;
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx hx' => hij <| by aesop;
  convert h_sum_fiberwise _ using 2;
  rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2 ] ] ; simp +decide [ Nat.card_eq_fintype_card ];
  rw [ Fintype.subtype_card ]

/-
Evaluating the weight enumerator at `X = Y = 1` counts the codewords:
`W_C(1,1) = |C|`.
-/
theorem weightEnumerator_eval_one_one (C : LinearCode ι F) :
    MvPolynomial.eval (fun _ => (1 : ℤ)) (weightEnumerator C) = Fintype.card C := by
  simp +decide [ LinearCode.weightEnumerator ]

end LinearCode