/-
# AB implies APN — Infrastructure

Helper lemmas for the proof that Almost Bent functions are Almost Perfect Nonlinear.

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.2
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Key identity: Walsh fourth moment equals derivative second moment -/

/-- The derivative distribution sums to |F|. -/
theorem derivCount_sum' {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, (derivCount f a b : ℤ) = (Fintype.card (F2n n) : ℤ) := by
  simp only [derivCount, Finset.card_filter]
  push_cast
  rw [← Finset.card_univ]
  rw [Finset.sum_comm]
  simp

/-! ### Parseval-type identity for derivatives -/

/-- The autocorrelation ∑_x χ(c·D_a·f(x)) at a=0 gives 2^n. -/
theorem autocorr_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (c : F2n n) :
    ∑ x : F2n n, chi n (c * (f (x + 0) + f x)) = (2 ^ n : ℤ) := by
  simp [F2n.add_self, chi_zero, F2n.card n hn]

/-- The key Wiener-Khinchin relation:
    ∑_c W(c)² χ(ca) = 2^n · ∑_x χ(f(x+a) + f(x)). -/
theorem wht_sq_chi_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    ∑ c : F2n n, wht f c ^ 2 * chi n (c * a) =
    (2 ^ n : ℤ) * ∑ x : F2n n, chi n (f (x + a) + f x) := by
  have h_expand : ∑ c, (∑ x, chi n (c * x + f x)) ^ 2 * chi n (c * a) =
      ∑ x, ∑ y, ∑ c, chi n (c * (x + y + a)) * chi n (f x + f y) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, Finset.sum_mul]
    simp +decide only [← chi_add, add_assoc]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring))
  have h_inner : ∀ x y : F2n n, ∑ c, chi n (c * (x + y + a)) =
      if x + y + a = 0 then (2 ^ n : ℤ) else 0 := by
    intro x y; split_ifs with h; simp_all +decide [mul_comm]
    · rw [F2n.card n hn, chi_zero]; norm_num
    · convert Kasami.chi_orthogonality hn (x + y + a) h using 1; ac_rfl
  convert h_expand using 1
  rw [Finset.mul_sum _ _ _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (x + a)]
    <;> simp_all +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul]
  · simp +decide [add_comm, add_left_comm, add_assoc]
  · grind

end
end Kasami
