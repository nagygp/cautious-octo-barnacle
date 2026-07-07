import RequestProject.Walsh.ChabaudVaudenay

/-!
# ZK / symmetric-crypto track: the global second-moment characterization of APN

This module advances the symmetric/ZK cryptanalysis track by summing the *local*
(per-direction) second-moment analysis of `RequestProject/Walsh/ChabaudVaudenay.lean`
over **all** nonzero derivative directions.  For a vectorial Boolean function
`f : F → F` over a finite field of characteristic two, write
`N_f(a, b) = #{x : f(x+a) + f(x) = b}` for the differential spectrum.  Chabaud and
Vaudenay's global second moment is
`∑_{a ≠ 0} ∑_b N_f(a, b)²`, and:

> `∑_{a ≠ 0} ∑_b N_f(a, b)² ≥ 2|F|(|F| − 1)`, with **equality iff `f` is APN**.

The lower bound is the sum of the local bounds `∑_b N_f(a, b)² ≥ 2|F|`
(`WalshAB.sum_diffCount_sq_ge`) over the `|F| − 1` nonzero directions, and the
equality case is the global form of the local APN characterization
(`WalshAB.local_apn_iff_sum_sq`).  This is the differential-spectrum side of the
Chabaud–Vaudenay characterization of almost perfect nonlinearity as a single
global quadratic quantity.

## Main results

* `sum_diffCount_sq_global_ge` — the global second-moment lower bound
  `2|F|(|F| − 1) ≤ ∑_{a ≠ 0} ∑_b N_f(a, b)²`.
* `isAPN_iff_sum_diffCount_sq_global` — `f` is APN **iff** the global second
  moment attains its minimum `2|F|(|F| − 1)`.
-/

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Global second-moment lower bound.** Summing the local bound
`∑_b N_f(a, b)² ≥ 2|F|` over the `|F| − 1` nonzero directions `a`.
-/
theorem sum_diffCount_sq_global_ge (f : F → F) :
    2 * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ≤
      ∑ a ∈ ({0}ᶜ : Finset F), ∑ b : F, (diffCount f a b : ℤ) ^ 2 := by
  refine' le_trans _ ( Finset.sum_le_sum fun a ha => WalshAB.sum_diffCount_sq_ge f a _ );
  · simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_compl ];
    rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring_nf ; norm_num;
  · exact Finset.mem_singleton.not.mp ( Finset.mem_compl.mp ha )

/-
**Global second-moment characterization of APN.** `f` is APN iff its global
differential second moment attains the minimum `2|F|(|F| − 1)`.
-/
theorem isAPN_iff_sum_diffCount_sq_global (f : F → F) :
    IsAPN f ↔
      ∑ a ∈ ({0}ᶜ : Finset F), ∑ b : F, (diffCount f a b : ℤ) ^ 2
        = 2 * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · convert WalshAB.isAPN_iff_sum_diffCount_sq f |>.1 h |> fun h' => ?_;
    rw [ Finset.sum_congr rfl fun a ha => h' a <| by simpa using ha ] ; simp +decide [ mul_comm, Finset.card_compl ];
    rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring;
  · have h_eq : ∀ a ∈ ({0}ᶜ : Finset F), ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
      have h_eq : ∑ a ∈ ({0}ᶜ : Finset F), (∑ b : F, (diffCount f a b : ℤ) ^ 2 - 2 * (Fintype.card F : ℤ)) = 0 := by
        simp_all +decide [ Finset.card_compl ];
        rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring;
      rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_eq;
      · exact fun a ha => eq_of_sub_eq_zero ( h_eq a ha );
      · exact fun a ha => sub_nonneg_of_le <| sum_diffCount_sq_ge f a <| by simpa using ha;
    exact isAPN_iff_sum_diffCount_sq f |>.2 fun a ha => h_eq a <| by simpa using ha;

end WalshAB