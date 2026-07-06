import RequestProject.CodingTheory.MDSWeightDistribution

/-!
# MDS codes have minimum-weight codewords

This module continues the coding-theory track of
`RequestProject/CodingTheory/MDSWeightDistribution.lean`, which proves the
closed-form minimum-weight count `A_d = (q-1)·C(n, d)` of an `[n, k, d]` MDS code
(`IsMDS.weightDistribution_minDist`).

Here we record the immediate but useful corollary that this count is *positive*
for every MDS code of positive dimension: an MDS code always has codewords of
minimum weight `d = n - k + 1`.  This is exactly what makes the bound `d` tight
(the Singleton bound is met *with equality*, and the equality is witnessed).

## Main results

* `IsMDS.weightDistribution_minDist_pos` — for an MDS code `C` with
  `1 ≤ dim C`, `0 < A_d` where `d = n - k + 1`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-
**An MDS code of positive dimension has minimum-weight codewords.**  For an
MDS code `C` with `1 ≤ codeDim C`, the number `A_d = (q-1)·C(n,d)` of
minimum-weight codewords (`d = n - k + 1`) is strictly positive.
-/
theorem IsMDS.weightDistribution_minDist_pos {C : Submodule F (ι → F)} (h : IsMDS C)
    (hk : 1 ≤ codeDim C) :
    0 < weightDistribution C (codeLength C - codeDim C + 1) := by
  rw [ IsMDS.weightDistribution_minDist h ];
  refine' mul_pos _ ( Nat.choose_pos _ );
  · exact Nat.sub_pos_of_lt ( Fintype.one_lt_card );
  · have h_card : codeDim C ≤ Fintype.card ι := by
      exact le_trans ( Submodule.finrank_le _ ) ( by simp +decide [ Module.finrank_pi ] );
    lia

end CodingTheory