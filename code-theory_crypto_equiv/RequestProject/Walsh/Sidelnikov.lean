import RequestProject.Walsh.Moments
import RequestProject.Walsh.ChabaudVaudenay

/-!
# The Sidelnikov–Chabaud–Vaudenay bound and AB ⇒ APN

This module completes the **symmetric/ZK cryptanalysis** triangle linking the
Walsh (linear) and differential pictures.  Building on the fourth-moment
identity `WalshAB.double_sum_fourth_moment`
(`Σ_{a,b} W⁴ = |F|² Σ_{a,b} N²`), the differential second-moment bound
`WalshAB.sum_diffCount_sq_ge` (`Σ_b N(a,b)² ≥ 2|F|` for `a ≠ 0`) and the
Parseval identity `WalshAB.parseval_perm`, we prove:

* `scv_fourth_moment_bound` — the **Sidelnikov–Chabaud–Vaudenay (SCV) bound**:
  for any permutation `f` of `F = GF(2ⁿ)`,
  `Σ_{a≠0} Σ_b W(a,b)⁴ ≥ 2|F|³(|F|−1)`.
* `scv_fourth_moment_eq_iff_isAPN` — equality holds **iff** `f` is APN.
* `IsAB.isAPN` — **AB ⇒ APN**: an almost-bent permutation is APN (the AB end of
  the SCV chain, where the bound is met with equality and the spectrum is
  optimal).

These are the Walsh-spectral complements of `Walsh/ChabaudVaudenay.lean` (the
differential-spectrum half of the same Chabaud–Vaudenay relation).
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
For an AB function, every Walsh square in a nonzero direction is `0` or
`2|F|`.
-/
theorem walsh_sq_zero_or_two_card {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hab : IsAB hcard f) (a : F) (ha : a ≠ 0) (b : F) :
    walsh f a b ^ 2 = 0 ∨ walsh f a b ^ 2 = 2 * (Fintype.card F : ℤ) := by
  specialize hab a ha b;
  grind

/-
**Local fourth moment of an AB permutation.**  For `a ≠ 0`,
`Σ_b W(a,b)⁴ = 2|F|³`.  (Each `W²` is `0` or `2|F|`, so `W⁴ = 2|F|·W²`, and
`Σ_b W² = |F|²` by Parseval.)
-/
theorem ab_local_fourth_moment {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hab : IsAB hcard f)
    (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
  have h_fourth_moment : ∑ b, (walsh f a b : ℤ) ^ 4 = ∑ b, (2 * (Fintype.card F : ℤ) * (walsh f a b : ℤ) ^ 2) := by
    grind +suggestions;
  rw [ h_fourth_moment, ← Finset.mul_sum _ _ _, WalshAB.parseval_perm hcard f hf a ha ] ; ring

/-
For a permutation, the fourth moment in the zero direction is `|F|⁴`:
`W(0,0) = |F|` and `W(0,b) = 0` for `b ≠ 0`.
-/
theorem walsh_zero_fourth_moment {f : F → F} (hf : Function.Bijective f) :
    ∑ b : F, walsh f 0 b ^ 4 = (Fintype.card F : ℤ) ^ 4 := by
  convert Finset.sum_eq_single ( 0 : F ) _ _ using 1;
  · rw [ walsh_zero_zero ];
  · exact fun b _ hb => by rw [ WalshAB.walsh_a_zero_perm f hf b hb ] ; simp +decide ;
  · exact fun h => False.elim <| h <| Finset.mem_univ _

/-
**The Sidelnikov–Chabaud–Vaudenay bound.**  For any permutation `f` of
`GF(2ⁿ)`, the total fourth moment over nonzero input masks is bounded below:
`Σ_{a≠0} Σ_b W(a,b)⁴ ≥ 2|F|³(|F|−1)`.
-/
theorem scv_fourth_moment_bound {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) :
    2 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) - 1)
      ≤ ∑ a ∈ Finset.univ.filter (fun a : F => a ≠ 0), ∑ b : F, walsh f a b ^ 4 := by
  have h_double_sum_fourth_moment : ∑ a : F, ∑ b : F, (walsh f a b : ℤ) ^ 4 = (Fintype.card F : ℤ) ^ 2 * (∑ a : F, ∑ b : F, (diffCount f a b : ℤ) ^ 2) := by
    convert double_sum_fourth_moment hcard f using 1;
  have h_sum_diffCount_sq_ge : ∑ a ∈ Finset.univ.filter (· ≠ 0), ∑ b : F, (diffCount f a b : ℤ) ^ 2 ≥ 2 * (Fintype.card F : ℤ) * (Fintype.card F - 1) := by
    refine' le_trans _ ( Finset.sum_le_sum fun a ha => show ∑ b : F, ( diffCount f a b : ℤ ) ^ 2 ≥ 2 * ( Fintype.card F : ℤ ) from _ );
    · simp +decide [ Finset.filter_ne' ];
      rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring_nf ; norm_num;
    · exact_mod_cast sum_diffCount_sq_ge f a ( by simpa using ha );
  convert mul_le_mul_of_nonneg_left h_sum_diffCount_sq_ge ( sq_nonneg ( Fintype.card F : ℤ ) ) using 1;
  · ring;
  · convert congr_arg ( fun x : ℤ => x - ∑ b : F, walsh f 0 b ^ 4 ) h_double_sum_fourth_moment using 1 <;> norm_num [ Finset.filter_ne' ];
    rw [ mul_sub, walsh_zero_fourth_moment hf ];
    rw [ show ( ∑ b : F, ( diffCount f 0 b : ℤ ) ^ 2 ) = ( Fintype.card F : ℤ ) ^ 2 by exact_mod_cast diffCount_zero_sq_sum f ] ; ring

/-
**Equality in the SCV bound characterizes APN.**  For a permutation `f`,
`Σ_{a≠0} Σ_b W(a,b)⁴ = 2|F|³(|F|−1)` **iff** `f` is APN.
-/
theorem scv_fourth_moment_eq_iff_isAPN {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) :
    (∑ a ∈ Finset.univ.filter (fun a : F => a ≠ 0), ∑ b : F, walsh f a b ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3 * ((Fintype.card F : ℤ) - 1))
      ↔ IsAPN f := by
  have h_eq : (∑ a ∈ Finset.univ.filter (· ≠ 0), ∑ b : F, walsh f a b ^ 4) = (Fintype.card F : ℤ) ^ 2 * (∑ a ∈ Finset.univ.filter (· ≠ 0), ∑ b : F, (diffCount f a b : ℤ) ^ 2) := by
    have h_sum_sq : ∑ a ∈ Finset.univ, ∑ b : F, walsh f a b ^ 4 = (Fintype.card F : ℤ) ^ 2 * ∑ a ∈ Finset.univ, ∑ b : F, (diffCount f a b : ℤ) ^ 2 := by
      convert double_sum_fourth_moment hcard f using 1;
    convert congr_arg ( fun x : ℤ => x - ∑ b : F, walsh f 0 b ^ 4 ) h_sum_sq using 1 <;> norm_num [ Finset.filter_ne' ];
    rw [ mul_sub, walsh_zero_fourth_moment hf, show ( ∑ b : F, ( diffCount f 0 b : ℤ ) ^ 2 ) = ( Fintype.card F : ℤ ) ^ 2 by exact_mod_cast diffCount_zero_sq_sum f ] ; ring;
  constructor <;> intro h;
  · apply (isAPN_iff_sum_diffCount_sq f).mpr;
    intro a ha
    have h_sum : ∑ a ∈ Finset.univ.filter (· ≠ 0), ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) := by
      exact mul_left_cancel₀ ( pow_ne_zero 2 ( Nat.cast_ne_zero.mpr ( ne_of_gt ( Fintype.card_pos ) ) ) ) ( by linarith );
    have h_sum : ∑ a ∈ Finset.univ.filter (· ≠ 0), (∑ b : F, (diffCount f a b : ℤ) ^ 2 - 2 * (Fintype.card F : ℤ)) = 0 := by
      simp_all +decide [ Finset.sum_sub_distrib ];
      simp +decide [ Finset.filter_ne', Finset.card_univ, hcard ] ; ring;
    rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum;
    · exact eq_of_sub_eq_zero ( h_sum a ( by simpa ) );
    · exact fun x hx => sub_nonneg_of_le <| mod_cast sum_diffCount_sq_ge f x <| by simpa using hx;
  · have := isAPN_iff_sum_diffCount_sq f;
    rw [ h_eq, Finset.sum_congr rfl fun x hx => this.mp h x ( Finset.mem_filter.mp hx |>.2 ) ] ; norm_num [ Finset.filter_ne' ] ; ring;
    grind

/-
**AB ⇒ APN.**  An almost-bent permutation of `GF(2ⁿ)` is APN.  This is the
optimal end of the SCV chain: the AB spectrum meets the SCV bound with equality,
forcing every nonzero-direction differential second moment to its minimum `2|F|`,
which is exactly the APN condition.
-/
theorem IsAB.isAPN {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hab : IsAB hcard f) :
    IsAPN f := by
  refine' ( scv_fourth_moment_eq_iff_isAPN hcard hf ).mp _;
  rw [ Finset.sum_congr rfl fun a ha => ab_local_fourth_moment hcard hf hab a ( Finset.mem_filter.mp ha |>.2 ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
  simp +decide [ Finset.filter_ne' ];
  rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring

end WalshAB