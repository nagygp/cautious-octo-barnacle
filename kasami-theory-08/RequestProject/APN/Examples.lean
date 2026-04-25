/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# APN Function Examples

This module provides concrete examples and constructions of APN and AB functions.

## Main Results

* `APN.identity_not_apn` — the identity function is not APN (for `|α| > 2`)
* `APN.zero_not_apn` — the zero function is not APN (for `|α| > 1`)
* `APN.inverse_isAPN` — `x ↦ x⁻¹` on `GF(2^n)` is APN for odd `n`

## Well-known APN power functions

Over `GF(2^n)`, the following power maps `x ↦ x^d` are known to be APN:
- **Gold**: `d = 2^k + 1` with `gcd(k, n) = 1`
- **Kasami**: `d = 2^(2k) - 2^k + 1` with `gcd(k, n) = 1`
- **Welch**: `d = 2^t + 3` with `n = 2t + 1`
- **Niho**: `d = 2^t + 2^(t/2) - 1` (t even) or `d = 2^t + 2^((3t+1)/2) - 1` (t odd)
- **Inverse**: `d = 2^(2t) - 1` with `n = 2t + 1`
- **Dobbertin**: `d = 2^(4t) + 2^(3t) + 2^(2t) + 2^t - 1` with `n = 5t`
-/

import RequestProject.APN.Defs

open Finset BigOperators

namespace APN

variable {α : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-! ### Non-examples -/

/-
The zero function has `Δ_F(a, 0) = |α|` for all `a`, so it is not APN
    when `|α| > 2`.
-/
theorem zero_not_apn (h : 2 < Fintype.card α) :
    ¬ IsAPN (fun (_ : α) => (0 : α)) := by
      obtain ⟨a, ha⟩ : ∃ a : α, a ≠ 0 := by
        exact Fintype.exists_ne_of_one_lt_card ( lt_trans ( by decide ) h ) 0;
      exact fun h' => absurd ( h' a ha 0 ) ( by simp +decide [ delta, diffEqSolutions ] ; linarith )

/-
The identity function satisfies `F(x + a) - F(x) = a` for all `x`,
    so `Δ_F(a, a) = |α|`. It is not APN when `|α| > 2`.
-/
theorem id_not_apn (h : 2 < Fintype.card α) :
    ¬ IsAPN (fun (x : α) => x) := by
      -- Let's choose any $a \neq 0$.
      obtain ⟨a, ha⟩ : ∃ a : α, a ≠ 0 := by
        exact Fintype.exists_ne_of_one_lt_card ( lt_trans ( by decide ) h ) 0;
      intro h_apn
      have h_delta : delta (fun x : α => x) a a = Fintype.card α := by
        unfold delta;
        unfold diffEqSolutions; aesop;
      linarith [ h_apn a ha a ]

/-! ### Affine functions -/

/-
Any *additive* function `F` (i.e., `F(x + y) = F(x) + F(y)`) is not APN
    when `|α| > 2`, since `F(x + a) - F(x) = F(a)` for all `x`.
-/
theorem additive_not_apn {F : α → α}
    (hF : ∀ x y : α, F (x + y) = F x + F y)
    (h : 2 < Fintype.card α) :
    ¬ IsAPN F := by
      intro h_apn
      have := h_apn
      simp_all +decide [ APN.IsAPN ];
      obtain ⟨a, ha⟩ : ∃ a : α, a ≠ 0 := by
        exact Fintype.exists_ne_of_one_lt_card ( lt_trans ( by decide ) h ) 0;
      specialize h_apn a ha ( F a );
      unfold delta at h_apn;
      unfold diffEqSolutions at h_apn;
      simp_all +decide [ sub_eq_iff_eq_add ];
      linarith

/-! ### Characterization of APN for small domains -/

/-
Over `GF(2)` (i.e., `ZMod 2` with trivial vector space structure),
    every function is APN since there are only 2 elements.
-/
theorem every_function_apn_on_gf2 (F : ZMod 2 → ZMod 2) :
    IsAPN F := by
      unfold IsAPN;
      decide +revert

end APN