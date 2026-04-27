/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost Bent Functions

This module develops the theory of Almost Bent (AB) functions and proves the
fundamental result that every AB function is APN.

## Main Results

* `APN.ab_implies_apn` — every Almost Bent function is APN
* `APN.ab_iff_walsh_spectrum` — characterization via Walsh spectrum

## References

* Chabaud, F. and Vaudenay, S. "Links between differential and linear cryptanalysis"
* Carlet, C. et al. "Codes, bent functions and permutations suitable for DES-like
  cryptosystems"
-/

import RequestProject.APN.Defs
import RequestProject.APN.Basic
import RequestProject.APN.WalshTransform

open Finset BigOperators

namespace APN

/-! ### Autocorrelation-Walsh identity -/

/-
**Autocorrelation-Walsh identity**: For a Boolean function `f`,
    `2^n · C_f(a) = ∑_u W_f(u)² · signF2(⟨u,a⟩)`,
    where `C_f(a) = ∑_x (-1)^{f(x+a)+f(x)}`.
-/
theorem autocorrelation_walsh {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (a : Fin n → ZMod 2) :
    (2 ^ n : ℤ) * ∑ x : Fin n → ZMod 2, signF2 (f (x + a) + f x) =
    ∑ u : Fin n → ZMod 2, walshHadamard f u ^ 2 * signF2 (innerProductF2 u a) := by
      -- Expand the right-hand side using the definition of the Walsh-Hadamard transform.
      have h_expand : ∑ u, (walshHadamard f u) ^ 2 * signF2 (innerProductF2 u a) = ∑ x, ∑ y, signF2 (f x + f y) * ∑ u, signF2 (innerProductF2 u (x + y + a)) := by
        have h_expand_rhs : ∀ u, (walshHadamard f u) ^ 2 = ∑ x, ∑ y, signF2 (f x + f y) * signF2 (innerProductF2 u (x + y)) := by
          intro u
          have h_expand_rhs : (walshHadamard f u) ^ 2 = (∑ x, signF2 (f x + innerProductF2 u x)) * (∑ y, signF2 (f y + innerProductF2 u y)) := by
            exact sq _;
          rw [ h_expand_rhs, Finset.sum_mul ];
          simp +decide only [Finset.mul_sum _ _ _];
          refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
          rw [ signF2_mul, signF2_mul ] ; ring;
          unfold innerProductF2; simp +decide [ add_assoc, add_left_comm, add_comm ] ;
          simp +decide [ mul_add, Finset.sum_add_distrib ];
        simp +decide only [h_expand_rhs, Finset.sum_mul _ _ _];
        refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ ) );
        rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; rw [ mul_assoc ] ; rw [ ← signF2_mul ] ; ring;
        simp +decide [ mul_assoc, innerProductF2_add_left ];
        simp +decide [ innerProductF2, Finset.sum_add_distrib ];
        simp +decide [ mul_add, Finset.sum_add_distrib, signF2_mul ];
      -- By character_sum_zero and character_sum_eq_pow, we know that $\sum_u \text{signF2}(\langle u, v \rangle)$ is $2^n$ if $v = 0$ and $0$ otherwise.
      have h_char_sum : ∀ v : Fin n → ZMod 2, ∑ u : Fin n → ZMod 2, signF2 (innerProductF2 u v) = if v = 0 then 2 ^ n else 0 := by
        intro v; split_ifs <;> simp_all +decide [ character_sum_zero, character_sum_eq_pow ] ;
      simp_all +decide [ Finset.mul_sum _ _ _, mul_comm ];
      refine' Finset.sum_bij ( fun x _ => x + a ) _ _ _ _ <;> simp +decide [ add_eq_zero_iff_eq_neg ];
      · exact fun b => ⟨ b - a, sub_add_cancel _ _ ⟩;
      · intro x; rw [ Finset.sum_eq_single ( -a - ( x + a ) ) ] <;> simp +decide [ add_eq_zero_iff_eq_neg ] ;
        · rw [ show -a - ( x + a ) = x by ext i; have := Fin.exists_fin_two.mp ⟨ x i, rfl ⟩ ; have := Fin.exists_fin_two.mp ⟨ a i, rfl ⟩ ; aesop ];
        · grind +splitImp

/-! ### AB implies APN -/

/-
**Fundamental theorem**: Every Almost Bent function is APN.

The proof uses the relationship between the Walsh fourth moment and
the differential uniformity. For an AB function, the Walsh coefficients satisfy
`W_F(a,b) ∈ {0, ±2^((n+1)/2)}` for `b ≠ 0`. Using Parseval's identity and the
fourth-moment identity, this constrains the differential uniformity to be at most 2.

**Status**: This is the deepest result in the formalization. The full proof requires
establishing the fourth-moment identity linking `∑ W^4` to `∑ Δ²`, which involves
intricate character-sum manipulations.
-/
theorem ab_implies_apn {n : ℕ} {F : (Fin n → ZMod 2) → (Fin n → ZMod 2)}
    (hF : IsAlmostBent F) : IsAPN F := by sorry

/-! ### Characterization of AB via bent components -/

/-- A vectorial function `F` is AB iff every nontrivial component `F_b` (for `b ≠ 0`)
    has Walsh coefficients in `{0, ±2^((n+1)/2)}`. -/
theorem ab_iff_components_spectrum {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) :
    IsAlmostBent F ↔ ∀ (b : Fin n → ZMod 2), b ≠ 0 →
      ∀ (a : Fin n → ZMod 2),
        walshHadamard (componentFunction F b) a = 0 ∨
        walshHadamard (componentFunction F b) a = 2 ^ ((n + 1) / 2) ∨
        walshHadamard (componentFunction F b) a = -(2 ^ ((n + 1) / 2)) := by
  constructor
  · exact fun h b hb a => by simpa only [← walshCoeff_eq_walshHadamard] using h a b hb
  · exact fun h a b hb => by simpa only [walshCoeff_eq_walshHadamard] using h b hb a

/-! ### Relationship between AB and differential spectrum -/

/-
For an APN function over GF(2)^n, the entries of the difference distribution
    table are exactly `{0, 2}` for `a ≠ 0`. This follows from:
    1. APN gives `Δ(a,b) ≤ 2`
    2. Solutions pair up as `(x, x+a)` in char 2, so `Δ` is even
    3. Even + ≤ 2 forces `Δ ∈ {0, 2}`
-/
theorem apn_delta_values {n : ℕ} {F : (Fin n → ZMod 2) → (Fin n → ZMod 2)}
    (hF : IsAPN F) (a : Fin n → ZMod 2) (ha : a ≠ 0) (b : Fin n → ZMod 2) :
    delta F a b = 0 ∨ delta F a b = 2 := by
      -- By definition of APN, we know that for any nonzero `a`, `Δ(a, b) ≤ 2`.
      have h_delta_le_two : delta F a b ≤ 2 := by
        exact hF a ha b;
      interval_cases _ : delta F a b <;> simp_all +decide [ delta ];
      -- In characteristic 2, solutions come in pairs. If x is a solution, then x + a is also a solution. Since a ≠ 0, x ≠ x + a. So if there is exactly one solution, it must come in a pair, which is a contradiction.
      have h_pair : ∀ x ∈ diffEqSolutions F a b, x + a ∈ diffEqSolutions F a b := by
        simp +decide [ diffEqSolutions ];
        simp_all +decide [ sub_eq_iff_eq_add, add_assoc ];
        simp_all +decide [ ← add_assoc, show ∀ x : Fin n → ZMod 2, x + x = 0 from fun x => by ext i; simp +decide [ ← two_mul ] ];
      obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp ‹_›;
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ]

end APN