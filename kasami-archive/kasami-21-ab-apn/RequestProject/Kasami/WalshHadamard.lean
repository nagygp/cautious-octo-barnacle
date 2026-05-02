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
  have h_fubini : ∑ a : F2n n, ∑ x : F2n n, ∑ y : F2n n, chi n (a * x + f x) * chi n (a * y + f y) = ∑ x : F2n n, ∑ y : F2n n, chi n (f x + f y) * ∑ a : F2n n, chi n (a * (x + y)) := by
    simp +decide only [mul_add, mul_comm, Finset.mul_sum _ _ _];
    simp +decide only [add_comm, ← chi_add, add_left_comm];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  convert h_fubini using 1;
  · simp +decide only [wht, sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul];
  · -- By the orthogonality of the characters, we know that $\sum_{a \in \mathbb{F}_{2^n}} \chi(a(x+y)) = 2^n$ if $x = y$ and $0$ otherwise.
    have h_orthogonality : ∀ x y : F2n n, ∑ a : F2n n, chi n (a * (x + y)) = if x = y then (2 ^ n : ℤ) else 0 := by
      intro x y; split_ifs with h; simp_all +decide [ ← mul_add ] ;
      · rw [ F2n.card n hn, chi_zero ] ; norm_num;
      · convert chi_orthogonality hn ( x + y ) ( add_eq_zero_iff_eq_neg.not.mpr <| by aesop ) using 1;
        ac_rfl;
    simp +decide [ h_orthogonality, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
    rw [ F2n.card n hn, chi_zero ] ; ring;
    norm_cast ; ring

/-
The sum of `W_f(a)` over all `a` equals `2^n · χ(f(0))`.
-/
theorem wht_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a = (2 ^ n : ℤ) * chi n (f 0) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ x : F2n n, chi n (a * x + f x) = ∑ x : F2n n, ∑ a : F2n n, chi n (a * x + f x) := by
    exact Finset.sum_comm;
  convert h_fubini using 1;
  rw [ Finset.sum_eq_single 0 ] <;> norm_num;
  · exact Or.inl ( mod_cast F2n.card n hn ▸ rfl );
  · intro b hb; have := chi_orthogonality hn b hb; simp_all +decide [ mul_comm ] ;
    convert congr_arg ( fun x : ℤ => x * chi n ( f b ) ) this using 1;
    · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; rw [ chi_add ] ;
    · ring

/-! ### Inversion formula -/

/-
**Inversion formula**: `∑_a W_f(a) · χ(a·x) = 2^n · χ(f(x))`.
-/
theorem wht_inversion {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (x : F2n n) :
    ∑ a : F2n n, wht f a * chi n (a * x) = (2 ^ n : ℤ) * chi n (f x) := by
  -- Expand the definition of `wht f a` and apply the chi_sum lemma.
  have h_expand : ∑ a : F2n n, (∑ y : F2n n, chi n (a * y + f y)) * chi n (a * x) =
    ∑ y : F2n n, ∑ a : F2n n, chi n (a * (x + y)) * chi n (f y) := by
      simp +decide only [Finset.sum_mul _ _ _];
      rw [ Finset.sum_comm ];
      simp +decide only [mul_comm, chi_add, mul_add];
      ac_rfl;
  convert h_expand using 1;
  rw [ Finset.sum_eq_single x ] <;> simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  · rw [ Kasami.F2n.card n hn ] ; norm_num [ chi_zero ];
  · intro b hb; specialize hb; have := chi_sum hn ( x + b ) ; simp_all +decide [ add_comm x ] ;
    simp_all +decide [ mul_comm, add_eq_zero_iff_eq_neg ]

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
  convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| ?_;
  · infer_instance;
  · rw [ Finset.sum_congr rfl fun _ _ => chi_abs _ ] ; norm_num [ F2n.card n hn ]

/-! ### Extended Walsh–Hadamard transform -/

/-- The extended (two-argument) WHT: `W_f(a, b) = ∑_x χ(a·x + b·f(x))`. -/
def wht2 {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + b * f x)

/-- `wht2 f a 1 = wht f a`. -/
theorem wht2_one {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    wht2 f a 1 = wht f a := by
  simp [wht2, wht, mul_one]

/-! ### Fourth moment -/

/-- The fourth moment `∑_a W_f(a)^4`. -/
def whtFourthMoment {n : ℕ} (f : F2n n → F2n n) : ℤ :=
  ∑ a : F2n n, wht f a ^ 4

end
end Kasami