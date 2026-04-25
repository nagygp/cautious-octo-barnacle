/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walsh–Hadamard Transform

Defines the Walsh–Hadamard transform (WHT) of a function `f : F_{2^n} → F_{2^n}`:
  `W_f(a) = ∑_{x ∈ F} χ(a·x + f(x))`

and proves fundamental identities:
- Parseval: `∑_a W_f(a)^2 = (2^n)^2`
- Inversion formula

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §4.1
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 5
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter

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
  exact chi_sum hn a

/-! ### Parseval identity -/

/-
**Parseval identity**: `∑_a W_f(a)^2 = (2^n)^2 = 4^n`.
-/
theorem wht_parseval {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ x : F2n n, ∑ y : F2n n, chi n (a * x + f x) * chi n (a * y + f y) = ∑ x : F2n n, ∑ y : F2n n, chi n (f x) * chi n (f y) * ∑ a : F2n n, chi n (a * (x + y)) := by
    simp +decide only [Finset.mul_sum _ _ _];
    simp +decide only [chi_add, mul_comm, mul_add];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By chi_sum, we know that $\sum_{a} \chi(a(x+y)) = 2^n$ if $x = y$ and $0$ otherwise.
  have h_chi_sum : ∀ x y : F2n n, ∑ a : F2n n, chi n (a * (x + y)) = if x = y then (2 ^ n : ℤ) else 0 := by
    intro x y;
    have := chi_sum hn ( x + y );
    simp_all +decide [ mul_comm, add_eq_zero_iff_eq_neg ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sq, wht ];
  simp_all +decide [ ← sq, chi_sq ];
  exact_mod_cast F2n.card n hn

/-! ### Inversion formula -/

/-
**Inversion formula**: `∑_a W_f(a) · χ(a·x) = 2^n · χ(f(x))`.
-/
theorem wht_inversion {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (x : F2n n) :
    ∑ a : F2n n, wht f a * chi n (a * x) = (2 ^ n : ℤ) * chi n (f x) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ y : F2n n, chi n (a * y + f y) * chi n (a * x) = ∑ y : F2n n, ∑ a : F2n n, chi n (a * (y + x)) * chi n (f y) := by
    convert Finset.sum_comm using 3 ; ring;
    rw [ ← chi_add, ← chi_add ] ; ring;
  -- Apply the orthogonality relation to the inner sum.
  have h_inner : ∀ y : F2n n, ∑ a : F2n n, chi n (a * (y + x)) = if y + x = 0 then (2 ^ n : ℤ) else 0 := by
    intro y; split_ifs <;> simp_all +decide [ mul_comm ] ;
    · rw [ F2n.card n hn, chi_zero ] ; norm_num;
    · convert Kasami.chi_orthogonality hn ( y + x ) ‹_› using 1;
      ac_rfl;
  convert h_fubini using 1;
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_mul _ _ _;
  · simp_all +decide [ ← Finset.sum_mul _ _ _, add_eq_zero_iff_eq_neg ]

/-! ### WHT value bounds -/

/-
Trivial bound: `|W_f(a)| ≤ 2^n`.
-/
theorem wht_abs_le {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    |wht f a| ≤ 2 ^ n := by
  exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => ( show |chi n _| ≤ 1 by norm_cast; exact ( chi_abs _ ) ▸ le_rfl ) ) ( by norm_num [ F2n.card n hn ] ) )

/-! ### Fourth moment -/

/-- The fourth moment `∑_a W_f(a)^4`. -/
def whtFourthMoment {n : ℕ} (f : F2n n → F2n n) : ℤ :=
  ∑ a : F2n n, wht f a ^ 4

end
end Kasami