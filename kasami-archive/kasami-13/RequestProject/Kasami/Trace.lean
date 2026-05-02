/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace map for F_{2^n} / F_2

This module specializes `Algebra.trace` to the extension `GaloisField 2 n / ZMod 2`:
- `tr2 n : F2n n →ₗ[ZMod 2] ZMod 2` — the absolute trace
- `tr2_sq`: `Tr(x²) = Tr(x)` in characteristic 2
- `tr2_surjective`: the trace is surjective (for `n ≥ 1`)

## References
- [Lidl, Niederreiter, *Finite Fields*][lidl1997], Chapter 2, §2.3
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], Chapter 2
-/

import Mathlib
import RequestProject.Kasami.Basic

namespace Kasami

open scoped BigOperators

/-- The absolute trace `Tr : F_{2^n} → F_2`. -/
noncomputable abbrev tr2 (n : ℕ) : F2n n →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (F2n n)

/-- The trace is F₂-linear (inherited from `Algebra.trace`). -/
theorem tr2_add {n : ℕ} (x y : F2n n) : tr2 n (x + y) = tr2 n x + tr2 n y :=
  map_add (tr2 n) x y

/-- `Tr(0) = 0`. -/
@[simp]
theorem tr2_zero (n : ℕ) : tr2 n 0 = 0 :=
  map_zero (tr2 n)

/-
`Tr(x²) = Tr(x)` in characteristic 2.
-/
theorem tr2_sq {n : ℕ} (hn : n ≠ 0) (x : F2n n) : tr2 n (x ^ 2) = tr2 n x := by
  have h_trace_map : tr2 n (x ^ 2) = tr2 n x := by
    have h_iso : ∃ (f : F2n n ≃ₐ[ZMod 2] F2n n), f x = x ^ 2 := by
      refine' ⟨ _, _ ⟩;
      refine' { Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ _, _ ⟩ with .. };
      all_goals norm_num [ Function.Injective, Function.Surjective ];
      · grind;
      · have h_iso : Function.Bijective (fun x : F2n n => x ^ 2) := by
          have h_frobenius : Function.Injective (fun x : F2n n => x ^ 2) := by
            exact?;
          exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
        exact h_iso.surjective;
      · exact fun x y => mul_pow x y 2;
      · exact?;
      · exact fun r => by fin_cases r <;> simp +decide ;
    obtain ⟨ f, hf ⟩ := h_iso;
    rw [ ← hf ];
    exact?;
  exact h_trace_map

/-- More generally, `Tr(x^{2^k}) = Tr(x)` for any `k`. -/
theorem tr2_pow2 {n : ℕ} (hn : n ≠ 0) (x : F2n n) (k : ℕ) :
    tr2 n (x ^ (2 ^ k)) = tr2 n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) ^ 2 := by ring
    rw [this, tr2_sq hn, ih]

/-
The trace map is surjective for `n ≥ 1`.
-/
theorem tr2_surjective {n : ℕ} (hn : n ≠ 0) : Function.Surjective (tr2 n) := by
  exact?

/-- There exists an element with `Tr(x) = 1`. -/
theorem tr2_exists_one {n : ℕ} (hn : n ≠ 0) : ∃ x : F2n n, tr2 n x = 1 := by
  exact tr2_surjective hn 1

/-
Exactly half the elements of F_{2^n} have trace 0.
-/
theorem tr2_kernel_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 0).card = 2 ^ (n - 1) := by
  -- The kernel of the trace map is a subspace of F_{2^n} with dimension n-1.
  have h_ker_dim : Module.finrank (ZMod 2) (LinearMap.ker (tr2 n)) = n - 1 := by
    have h_ker_dim : Module.finrank (ZMod 2) (LinearMap.range (tr2 n)) = 1 := by
      rw [ LinearMap.range_eq_top.mpr ] <;> norm_num [ tr2_surjective hn ];
    have := LinearMap.finrank_range_add_finrank_ker ( tr2 n );
    exact eq_tsub_of_add_eq ( by linarith! [ show Module.finrank ( ZMod 2 ) ( F2n n ) = n from by { exact? } ] );
  -- The cardinality of a finite-dimensional vector space over a finite field is the cardinality of the field raised to the power of the dimension.
  have h_card : Nat.card (LinearMap.ker (tr2 n)) = (Nat.card (ZMod 2)) ^ (Module.finrank (ZMod 2) (LinearMap.ker (tr2 n))) := by
    exact?;
  simp_all +decide [ Fintype.card_subtype ]

/-
Exactly half the elements of F_{2^n} have trace 1.
-/
theorem tr2_fiber_one_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  obtain ⟨ x, hx ⟩ := tr2_exists_one hn;
  fapply Finset.card_bij;
  use fun a ha => a + x;
  · grind;
  · aesop;
  · intro b hb; use b - x; aesop;

/-
`Tr(ax)` as `a` varies gives a balanced function when `x ≠ 0`.
-/
theorem tr2_balanced {n : ℕ} (hn : n ≠ 0) (x : F2n n) (hx : x ≠ 0) :
    (Finset.univ.filter fun a : F2n n => tr2 n (a * x) = 0).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  refine' Finset.card_bij _ _ _ _;
  use fun a ha => a * x;
  · aesop;
  · aesop;
  · exact fun b hb => ⟨ b / x, by simpa [ hx ] using hb, div_mul_cancel₀ _ hx ⟩

end Kasami