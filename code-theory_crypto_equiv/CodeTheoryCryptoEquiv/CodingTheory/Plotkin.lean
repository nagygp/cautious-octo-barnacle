import Mathlib
import CodeTheoryCryptoEquiv.CodingTheory.LinearCode

/-!
# The Plotkin bound for linear codes

This module is a further step of the coding-theory development transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977,

(Ch. 2, Thm 1).  It proves the **Plotkin bound** for a linear code `C ⊆ Fⁿ` over
a finite field `F` with `q = |F|`, in the cleared-denominator form

> `q · (|C| − 1) · d ≤ n · (q − 1) · |C|`,

where `n` is the length, `d = minWeight C` the minimum weight, and `|C|` the
number of codewords.  When `q·d > (q−1)·n` this rearranges to the classical
upper bound `|C| ≤ q·d / (q·d − (q−1)·n)`.

The proof is the standard double counting of the total weight
`S = Σ_{c ∈ C} wt c`:

* **Lower bound** (`pred_card_mul_minWeight_le`): each of the `|C| − 1` nonzero
  codewords has weight `≥ d`, so `(|C| − 1)·d ≤ S`.
* **Upper bound** (`card_mul_sum_weight_le`): summing weights column by column
  (`sum_weight_eq_sum_coord`), in each coordinate the evaluation map `C → F` is
  linear, so its image is `{0}` or all of `F`; hence the number of codewords
  nonzero in that coordinate satisfies `q · (#nonzero) ≤ (q − 1)·|C|`
  (`coord_count_bound`), giving `q·S ≤ n·(q − 1)·|C|`.

Combining the two yields `plotkin_bound`.

Words live in `ι → F` with `[Fintype ι] [Field F] [Fintype F]`, exactly as in
`CodeTheoryCryptoEquiv/CodingTheory/WeightEnumerator.lean`.
-/

namespace CodingTheory

open scoped Classical
open Finset BigOperators

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

noncomputable instance instFintypeSubmodulePlotkin (C : Submodule F (ι → F)) : Fintype C :=
  Fintype.ofFinite _

/-
The total weight of a code, summed column by column: the sum of Hamming
weights over all codewords equals the sum over coordinates of the number of
codewords nonzero in that coordinate (Fubini on the support).
-/
theorem sum_weight_eq_sum_coord (C : Submodule F (ι → F)) :
    ∑ c : C, hammingNorm (c : ι → F)
      = ∑ i : ι, (Finset.univ.filter (fun c : C => (c : ι → F) i ≠ 0)).card := by
  simp +decide only [hammingNorm, card_filter];
  rw [ Finset.sum_comm ]

/-
**Per-coordinate count bound.**  For each coordinate `i`, the evaluation
`c ↦ c i` is `F`-linear on `C`, so its image is `{0}` or all of `F`; in either
case `q · (#codewords nonzero at i) ≤ (q − 1) · |C|`.
-/
theorem coord_count_bound (C : Submodule F (ι → F)) (i : ι) :
    Fintype.card F * (Finset.univ.filter (fun c : C => (c : ι → F) i ≠ 0)).card
      ≤ (Fintype.card F - 1) * Fintype.card C := by
  -- Consider the `F`-linear evaluation map `e : C →ₗ[F] F`, `e c = (c : ι → F) i` (build it as `(LinearMap.proj i).comp C.subtype`).
  set e : C →ₗ[F] F := (LinearMap.proj i).comp C.subtype;
  -- The number of elements in the kernel of `e` is at least the number of elements in `C` divided by the number of elements in `F`.
  have h_kernel_card : Fintype.card (LinearMap.ker e) * Fintype.card F ≥ Fintype.card C := by
    have := Submodule.card_eq_card_quotient_mul_card ( LinearMap.ker e );
    simp +zetaDelta at *;
    rw [ this ];
    exact Nat.mul_le_mul_left _ ( Fintype.card_le_of_injective _ ( show Function.Injective ( LinearMap.quotKerEquivRange e |> LinearEquiv.toLinearMap ) from LinearMap.quotKerEquivRange e |> LinearEquiv.injective ) |> le_trans <| Fintype.card_le_of_injective _ <| show Function.Injective ( LinearMap.range e ).subtype from Subtype.coe_injective );
  -- The number of elements in `C` that are nonzero in the `i`-th coordinate is equal to the total number of elements in `C` minus the number of elements in the kernel of `e`.
  have h_nonzero_card : (Finset.univ.filter (fun c : C => (c : ι → F) i ≠ 0)).card = Fintype.card C - Fintype.card (LinearMap.ker e) := by
    rw [ Fintype.card_subtype, Fintype.card_subtype ];
    rw [ show ( Finset.univ.filter fun x : ι → F => x ∈ C ) = Finset.image ( fun x : C => x.val ) Finset.univ from ?_, Finset.card_image_of_injective _ Subtype.coe_injective ];
    · rw [ Finset.filter_not, Finset.card_sdiff ] ; aesop;
    · aesop;
  nlinarith [ Nat.sub_add_cancel ( show 1 ≤ Fintype.card F from Fintype.card_pos ), Nat.sub_add_cancel ( show Fintype.card ( LinearMap.ker e ) ≤ Fintype.card C from Fintype.card_le_of_injective _ Subtype.coe_injective ) ]

/-
**Upper bound on the total weight.**
`q · Σ_{c} wt c ≤ n · (q − 1) · |C|`.
-/
theorem card_mul_sum_weight_le (C : Submodule F (ι → F)) :
    Fintype.card F * (∑ c : C, hammingNorm (c : ι → F))
      ≤ codeLength C * ((Fintype.card F - 1) * Fintype.card C) := by
  convert Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => coord_count_bound C i;
  · rw [ ← Finset.mul_sum _ _ _, sum_weight_eq_sum_coord ];
  · simp +decide [ codeLength ]

/-
**Lower bound on the total weight.**  Each of the `|C| − 1` nonzero codewords
has weight at least the minimum weight, so `(|C| − 1)·d ≤ Σ_{c} wt c`.
-/
theorem pred_card_mul_minWeight_le (C : Submodule F (ι → F)) :
    (Fintype.card C - 1) * minWeight C ≤ ∑ c : C, hammingNorm (c : ι → F) := by
  have h_lower_bound : ∑ c ∈ Finset.univ.erase (0 : C), hammingNorm (c : ι → F) ≥ ∑ c ∈ Finset.univ.erase (0 : C), minWeight C := by
    refine Finset.sum_le_sum fun c hc => ?_;
    exact minWeight_le ( Subtype.mem c ) ( by aesop );
  simp_all +decide [ Finset.sum_erase ]

/-
**The Plotkin bound (Ch. 2, Thm 1), cleared-denominator form.**
`q · (|C| − 1) · d ≤ n · (q − 1) · |C|`.
-/
theorem plotkin_bound (C : Submodule F (ι → F)) :
    Fintype.card F * ((Fintype.card C - 1) * minWeight C)
      ≤ codeLength C * ((Fintype.card F - 1) * Fintype.card C) := by
  refine' le_trans ( Nat.mul_le_mul_left _ ( pred_card_mul_minWeight_le _ ) ) ( card_mul_sum_weight_le _ )

end CodingTheory