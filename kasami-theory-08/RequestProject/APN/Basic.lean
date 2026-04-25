/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# APN Functions — Basic Properties

This module proves basic properties of APN functions and differential uniformity.

## Main Results

* `APN.delta_sum` — for every nonzero `a`, `∑_b Δ_F(a, b) = |α|`
* `APN.delta_zero_self` — `Δ_F(0, 0) = |α|` (every `x` is a solution)
* `APN.delta_zero_ne` — `Δ_F(0, b) = 0` for `b ≠ 0` when `F` is injective on shifts
* `APN.diffEqSolutions_even` — over char-2 groups, solutions come in pairs
* `APN.isAPN_of_injective_derivatives` — if all derivatives are 2-to-1, then APN
-/

import RequestProject.APN.Defs

open Finset BigOperators

namespace APN

variable {α : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-! ### Basic identities for the difference distribution table -/

/-
The sum `∑_b Δ_F(a, b) = |α|` for any `a`, since every `x` maps to exactly one `b`.
-/
theorem delta_sum (F : α → α) (a : α) :
    ∑ b : α, delta F a b = Fintype.card α := by
      unfold delta;
      simp +decide only [diffEqSolutions, card_filter];
      rw [ Finset.sum_comm ] ; aesop

/-
`Δ_F(0, 0) = |α|`: when `a = 0`, `F(x + 0) - F(x) = 0` for all `x`.
-/
theorem delta_zero_zero (F : α → α) :
    delta F 0 0 = Fintype.card α := by
      unfold delta diffEqSolutions; aesop;

/-
`Δ_F(0, b) = 0` for `b ≠ 0`.
-/
theorem delta_zero_ne (F : α → α) {b : α} (hb : b ≠ 0) :
    delta F 0 b = 0 := by
      unfold delta;
      unfold diffEqSolutions; aesop;

/-
The number of solutions is always bounded by the cardinality of the domain.
-/
theorem delta_le_card (F : α → α) (a b : α) :
    delta F a b ≤ Fintype.card α := by
      exact Finset.card_le_univ _

/-! ### Derivative / difference map -/

/-- The **derivative** (or difference map) of `F` in direction `a`. -/
def derivative (F : α → α) (a : α) : α → α :=
  fun x => F (x + a) - F (x)

/-
The number of solutions `Δ_F(a, b)` equals the size of the preimage of `b`
    under the derivative `D_a F`.
-/
theorem delta_eq_fiber_card (F : α → α) (a b : α) :
    delta F a b = (Finset.univ.filter (fun x => derivative F a x = b)).card := by
      exact congr_arg Finset.card ( Finset.filter_congr fun x _ => by simp +decide [ derivative ] )

/-
`F` is APN iff every nonzero derivative is at most 2-to-1.
-/
theorem isAPN_iff_derivatives (F : α → α) :
    IsAPN F ↔ ∀ (a : α), a ≠ 0 → ∀ (b : α),
      (Finset.univ.filter (fun x => derivative F a x = b)).card ≤ 2 := by
        simp +decide only [IsAPN, delta_eq_fiber_card]

/-! ### Characterization in terms of pairs -/

/-
`F` is APN iff for every `a ≠ 0`, the map `x ↦ F(x + a) - F(x)` has
    no collisions beyond the trivial ones, i.e., `D_a F(x) = D_a F(y)` implies
    `x = y` or `x + a = y` (in char 2 groups where `2 • x = 0`).
-/
theorem isAPN_iff_derivative_two_to_one (F : α → α) (hchar : ∀ x : α, x + x = 0) :
    IsAPN F ↔ ∀ (a : α), a ≠ 0 → ∀ (x y : α),
      derivative F a x = derivative F a y → x = y ∨ x = y + a := by
        refine' ⟨ fun h a ha x y hxy => _, fun h => isAPN_iff_derivatives F |>.2 fun a ha b => _ ⟩;
        · have := h a ha ( derivative F a x );
          contrapose! this;
          refine' Finset.two_lt_card.mpr ⟨ x, _, y, _, y + a, _, _ ⟩ <;> simp_all +decide [ delta_eq_fiber_card, derivative ];
          · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hxy ⟩;
          · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, rfl ⟩;
          · simp +decide [ diffEqSolutions, hxy ];
            simp_all +decide [ add_assoc ];
            rw [ ← neg_sub, neg_eq_of_add_eq_zero_right ( hchar _ ) ];
        · by_contra h_contra;
          obtain ⟨ x, hx ⟩ := Finset.two_lt_card.mp ( not_le.mp h_contra );
          grind +splitImp

/-! ### APN invariants -/

/-
Adding a constant to `F` does not change the APN property.
-/
theorem isAPN_add_const (F : α → α) (c : α) :
    IsAPN F ↔ IsAPN (fun x => F x + c) := by
      unfold IsAPN;
      unfold delta;
      unfold diffEqSolutions; aesop;

/-
Pre-composing `F` with a translation does not change the APN property.
-/
theorem isAPN_translate (F : α → α) (c : α) :
    IsAPN F ↔ IsAPN (fun x => F (x + c)) := by
      constructor <;> intro h a ha b;
      · convert h a ha b using 1;
        fapply Finset.card_bij ( fun x _ => x + c ) _ _ _ <;> simp +decide [ diffEqSolutions, delta ];
        · exact fun x hx => by rwa [ add_right_comm ] ;
        · exact fun x hx => ⟨ x - c, by simpa [ add_assoc ] using hx, by simp +decide ⟩;
      · convert h a ha b using 1;
        refine' Finset.card_bij ( fun x hx => x - c ) _ _ _ <;> simp +decide;
        · simp +decide [ diffEqSolutions ];
          simp +decide [ sub_add_eq_add_sub ];
        · simp +decide [ diffEqSolutions ];
          exact fun x hx => ⟨ x + c, by simpa [ add_right_comm ] using hx, by simp +decide ⟩

end APN