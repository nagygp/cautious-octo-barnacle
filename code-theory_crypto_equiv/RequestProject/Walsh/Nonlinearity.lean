import RequestProject.Walsh.Sidelnikov

/-!
# The Sidelnikov–Chabaud–Vaudenay nonlinearity bound

This module continues `RequestProject/Walsh/Sidelnikov.lean`.  From the SCV
fourth-moment bound `scv_fourth_moment_bound` and the Parseval identity
`parseval_perm`, we derive the **SCV nonlinearity bound**: for any permutation
`f` of `GF(2ⁿ)` (`n ≥ 1`) there is a nonzero input mask `a` and an output mask
`b` with

  `W(a, b)² ≥ 2|F|`,

i.e. the maximal Walsh modulus is at least `√(2|F|) = 2^{(n+1)/2}`.  Equivalently
the nonlinearity satisfies `NL(f) ≤ 2^{n-1} - 2^{(n-1)/2}`; almost-bent functions
meet this bound with equality.

## Proof

Let `S = {a ≠ 0}`.  Parseval (`parseval_perm`) gives `Σ_b W(a,b)² = |F|²` for each
`a ∈ S`, hence `Σ_{a∈S} Σ_b W² = |F|²(|F|-1)`.  The SCV bound gives
`Σ_{a∈S} Σ_b W⁴ ≥ 2|F|³(|F|-1)`.  If every `W(a,b)²` (over `a ∈ S`) were
`< 2|F|`, then since the squares are integers `W² ≤ 2|F| - 1`, so
`Σ W⁴ = Σ W²·W² ≤ (2|F|-1)·Σ W² = (2|F|-1)|F|²(|F|-1) < 2|F|³(|F|-1)`, a
contradiction.

## Main results

* `walsh_sq_sum_nonzero` — `Σ_{a≠0} Σ_b W(a,b)² = |F|²(|F|-1)`.
* `scv_max_walsh_sq_ge` — the **SCV nonlinearity bound**: `∃ a ≠ 0, ∃ b,
  2|F| ≤ W(a,b)²`.
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
The total Walsh second moment over nonzero input masks: each direction
contributes `|F|²` by Parseval, and there are `|F|-1` nonzero directions.
-/
theorem walsh_sq_sum_nonzero {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) :
    ∑ a ∈ Finset.univ.filter (fun a : F => a ≠ 0), ∑ b : F, walsh f a b ^ 2
      = (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) - 1) := by
  rw [ Finset.sum_congr rfl fun x hx => parseval_perm hcard f hf x <| by simpa using hx ] ; simp +decide [ Finset.filter_ne' ] ; ring;
  rw [ Nat.cast_pred ] <;> ring ; exact Fintype.card_pos_iff.mpr ⟨ 0 ⟩

/-
**The Sidelnikov–Chabaud–Vaudenay nonlinearity bound.**  For any permutation
`f` of `GF(2ⁿ)` with `n ≥ 1`, there is a nonzero input mask `a` and an output
mask `b` with `W(a, b)² ≥ 2|F|`.
-/
theorem scv_max_walsh_sq_ge {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : 1 ≤ n)
    {f : F → F} (hf : Function.Bijective f) :
    ∃ a : F, a ≠ 0 ∧ ∃ b : F, 2 * (Fintype.card F : ℤ) ≤ walsh f a b ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : F, a ≠ 0 ∧ ∑ b : F, walsh f a b ^ 4 ≥ 2 * (Fintype.card F : ℤ) ^ 3 := by
    have h_sum_fourth_moment : ∑ a ∈ Finset.univ.filter (fun a : F => a ≠ 0), ∑ b : F, walsh f a b ^ 4 ≥ 2 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) - 1) := by
      convert scv_fourth_moment_bound hcard hf using 1;
    contrapose! h_sum_fourth_moment;
    refine' lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty _ fun a ha => h_sum_fourth_moment a <| Finset.mem_filter.mp ha |>.2 ) _;
    · exact ⟨ 1, by simp +decide ⟩;
    · simp +decide [ Finset.filter_ne', mul_comm ];
      rw [ Nat.cast_pred ( Fintype.card_pos ) ];
  contrapose! ha;
  intro ha_nonzero
  have h_sum_lt : ∑ b : F, walsh f a b ^ 4 ≤ (2 * (Fintype.card F : ℤ) - 1) * ∑ b : F, walsh f a b ^ 2 := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun b _ => by nlinarith only [ ha a ha_nonzero b, show walsh f a b ^ 2 ≥ 0 by positivity ] ;
  exact lt_of_le_of_lt h_sum_lt ( by rw [ WalshAB.parseval_perm hcard f hf a ha_nonzero ] ; nlinarith [ show ( Fintype.card F : ℤ ) ≥ 2 by exact_mod_cast hcard.symm ▸ Nat.le_self_pow ( by linarith ) _ ] )

end WalshAB