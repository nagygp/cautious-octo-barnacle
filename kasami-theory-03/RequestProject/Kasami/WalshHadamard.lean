/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walsh–Hadamard Transform

Defines the Walsh–Hadamard transform (WHT) of a function `f : F_{2^n} → F_{2^n}`:
  `W_f(a) = ∑_{x ∈ F} χ(a·x + f(x))`

## Main results
- Parseval: `∑_a W_f(a)^2 = (2^n)^2`
- Inversion formula

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §4.1
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter

set_option maxHeartbeats 800000

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

/-! ### Definition -/

/-- The Walsh–Hadamard transform of `f : F_{2^n} → F_{2^n}` at point `a`.
    `W_f(a) = ∑_{x ∈ F_{2^n}} χ(a·x + f(x))` -/
def wht {n : ℕ} (f : F2n n → F2n n) (a : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + f x)

/-- WHT at `a = 0`: `W_f(0) = ∑_x χ(f(x))`. -/
theorem wht_zero {n : ℕ} (f : F2n n → F2n n) :
    wht f 0 = ∑ x : F2n n, chi n (f x) := by
  simp [wht]

/-- WHT of the zero function. -/
theorem wht_zero_fun {n : ℕ} (hn : n ≠ 0) (a : F2n n) :
    wht (fun _ : F2n n => (0 : F2n n)) a = if a = 0 then (2 ^ n : ℤ) else 0 := by
  simp only [wht, add_zero]
  have : ∑ x : F2n n, chi n (a * x) = ∑ x : F2n n, chi n (x * a) := by
    congr 1; ext x; ring_nf
  rw [this]
  exact chi_sum hn a

/-! ### Parseval identity -/

/-
**Parseval identity**: `∑_a W_f(a)^2 = (2^n)^2 = 4^n`.
-/
theorem wht_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  -- Expand W_f(a)^2 using the definition of WHT.
  have h_expand : ∀ a : F2n n, (wht f a) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, chi n ((a * x + f x) + (a * y + f y)) := by
    intro a
    simp [wht];
    simp +decide only [chi_add, pow_two, Finset.sum_mul _ _ _];
    simp +decide only [Finset.mul_sum _ _ _];
  -- Sum over all $a$ and use the fact that $\chi(a(x + y) + f(x) + f(y))$ is $2^n$ if $x = y$ and $0$ otherwise.
  have h_sum : ∀ x y : F2n n, ∑ a : F2n n, chi n (a * (x + y) + (f x + f y)) = if x = y then (2 ^ n : ℤ) else 0 := by
    intro x y;
    by_cases hxy : x = y <;> simp +decide [ hxy, chi_add ];
    · exact mod_cast F2n.card n hn;
    · rw [ ← Finset.sum_mul _ _ _ ];
      have := chi_orthogonality hn ( x + y ) ( add_eq_zero_iff_eq_neg.not.mpr <| by aesop ) ; simp_all +decide [ mul_comm ] ;
  simp_all +decide [ Finset.sum_add_distrib, mul_add, add_assoc ];
  rw [ Finset.sum_comm ];
  simp_all +decide [ add_comm, add_left_comm, add_assoc ];
  rw [ Finset.sum_congr rfl fun x hx => Finset.sum_comm ];
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  rw [ sq, F2n.card n hn ];
  norm_cast

/-
The sum of `W_f(a)` over all `a` equals `2^n · χ(f(0))`.
-/
theorem wht_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a = (2 ^ n : ℤ) * chi n (f 0) := by
  have h_sum_wht : ∑ a : F2n n, wht f a = ∑ x : F2n n, chi n (f x) * ∑ a : F2n n, chi n (a * x) := by
    have h_sum_wht : ∑ a : F2n n, wht f a = ∑ x : F2n n, ∑ a : F2n n, chi n (a * x + f x) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    simp +decide only [h_sum_wht, Finset.mul_sum _ _ _];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← chi_add ] ; ring;
  rw [ h_sum_wht, Finset.sum_eq_single 0 ];
  · simp +decide [ mul_comm, F2n.card n hn ];
  · exact fun x _ hx => by rw [ chi_sum hn x, if_neg hx ] ; ring;
  · aesop

/-! ### Inversion formula -/

/-
**Inversion formula**: `∑_a W_f(a) · χ(a·x) = 2^n · χ(f(x))`.
-/
theorem wht_inversion {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (x : F2n n) :
    ∑ a : F2n n, wht f a * chi n (a * x) = (2 ^ n : ℤ) * chi n (f x) := by
  unfold wht;
  simp +decide only [Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun y hy => ?_ ];
  rotate_left;
  use fun y => chi n ( f y ) * ∑ a : F2n n, chi n ( a * ( y + x ) );
  · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; rw [ ← chi_add ] ; ring;
    rw [ ← chi_add ] ; ring;
  · rw [ Finset.sum_eq_single x ];
    · simp_all +decide [ ← two_mul, F2n.add_self ];
      rw [ mul_comm ];
      rw [ show 2 * x = 0 by rw [ two_mul, F2n.add_self ] ] ; norm_num;
      exact Or.inl ( mod_cast F2n.card n hn );
    · intro b _ hb; rw [ chi_sum hn ] ; simp +decide [ hb ] ;
      grind;
    · grind +qlia

/-! ### WHT and function composition -/

/-- WHT of `f + g` (pointwise). -/
theorem wht_add {n : ℕ} (f g : F2n n → F2n n) (a : F2n n) :
    wht (fun x => f x + g x) a = ∑ x : F2n n, chi n (a * x + f x) * chi n (g x) := by
  simp only [wht]
  congr 1; ext x
  rw [← chi_add]
  congr 1; ring

/-! ### WHT value bounds -/

/-
Trivial bound: `|W_f(a)| ≤ 2^n`.
-/
theorem wht_abs_le {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    |wht f a| ≤ 2 ^ n := by
  refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
  simp +decide [ chi_abs ];
  exact_mod_cast F2n.card n hn |> le_of_eq

/-! ### Fourth moment -/

/-- The fourth moment `∑_a W_f(a)^4`. -/
def whtFourthMoment {n : ℕ} (f : F2n n → F2n n) : ℤ :=
  ∑ a : F2n n, wht f a ^ 4

end
end Kasami