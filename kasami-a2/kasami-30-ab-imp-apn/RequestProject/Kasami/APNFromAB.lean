/-
# AB implies APN — Infrastructure and Derivative Analysis

This module provides infrastructure for the derivative distribution of
functions over F_{2^n}, including the Parseval identity for derivatives.

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

/-! ### Parseval identity for the derivative distribution -/

/-
Parseval identity for derivatives:
    `2^n · ∑_b N_a(b)² = ∑_c (∑_x χ(c · D_a f(x)))²`.
-/
theorem deriv_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    (2 ^ n : ℤ) * ∑ b : F2n n, (derivCount f a b : ℤ) ^ 2 =
    ∑ c : F2n n, (∑ x : F2n n, chi n (c * (f (x + a) + f x))) ^ 2 := by
  -- Apply the orthogonality of the characters to simplify the double sum.
  have h_ortho : ∀ b₁ b₂ : F2n n, ∑ c : F2n n, chi n (c * (b₁ + b₂)) = if b₁ = b₂ then (2 ^ n : ℤ) else 0 := by
    intro b₁ b₂;
    convert chi_sum hn ( b₁ + b₂ ) using 1;
    · ac_rfl;
    · grind +qlia;
  -- Expand the square and apply the orthogonality of the characters.
  have h_expand : ∑ c : F2n n, (∑ b : F2n n, derivCount f a b * chi n (c * b)) ^ 2 = ∑ b₁ : F2n n, ∑ b₂ : F2n n, derivCount f a b₁ * derivCount f a b₂ * ∑ c : F2n n, chi n (c * (b₁ + b₂)) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun y hy => Finset.sum_comm.trans ( Finset.sum_congr rfl fun x hx => _ );
    simp +decide [ mul_add, chi_add ];
  convert h_expand.symm using 1;
  · simp +decide [ h_ortho, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm];
  · congr! 2;
    simp +decide [ derivCount ];
    simp +decide only [Finset.card_filter];
    simp +decide only [Nat.cast_sum, Finset.sum_mul _ _ _];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_congr rfl ] ; aesop

/-- For any function, |∑_x χ(c · D_a f(x))| ≤ 2^n. -/
theorem deriv_char_sum_abs_le {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a c : F2n n) :
    |∑ x : F2n n, chi n (c * (f (x + a) + f x))| ≤ 2 ^ n := by
  refine' le_trans (Finset.abs_sum_le_sum_abs _ _) _
  simp only [Finset.sum_congr rfl fun _ _ => chi_abs _]
  simp [F2n.card n hn]

end
end Kasami