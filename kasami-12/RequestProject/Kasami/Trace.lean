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

theorem tr2_sq {n : ℕ} (hn : n ≠ 0) (x : F2n n) : tr2 n (x ^ 2) = tr2 n x := by
  have h_frobenius : Function.Bijective (fun x : F2n n => x ^ 2) := by
    have h_frobenius : Function.Injective (fun x : F2n n => x ^ 2) := by
      exact?;
    exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
  obtain ⟨ σ, hσ ⟩ := h_frobenius;
  have h_trace_frobenius : ∀ x : F2n n, (tr2 n) (x ^ 2) = (tr2 n) x := by
    intro x
    have h_frobenius_hom : ∃ (f : F2n n ≃ₐ[ZMod 2] F2n n), ∀ x : F2n n, f x = x ^ 2 := by
      refine' ⟨ { Equiv.ofBijective _ ⟨ σ, hσ ⟩ with .. }, _ ⟩;
      all_goals norm_num [ mul_pow, add_sq ];
      · exact fun x y => Or.inl <| Or.inl <| by exact?;
      · exact fun r => by fin_cases r <;> simp +decide ;
    obtain ⟨ f, hf ⟩ := h_frobenius_hom;
    rw [ ← hf ];
    exact?;
  exact h_trace_frobenius x

theorem tr2_surjective {n : ℕ} (hn : n ≠ 0) : Function.Surjective (tr2 n) := by
  exact?

/-- There exists an element with `Tr(x) = 1`. -/
theorem tr2_exists_one {n : ℕ} (hn : n ≠ 0) : ∃ x : F2n n, tr2 n x = 1 := by
  exact tr2_surjective hn 1

theorem tr2_kernel_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 0).card = 2 ^ (n - 1) := by
      -- The kernel of `tr2` is a subspace of dimension `n - 1`.
      have h_ker_dim : Module.finrank (ZMod 2) (LinearMap.ker (tr2 n)) = n - 1 := by
        have h_finrank : Module.finrank (ZMod 2) (F2n n) = n := by
          exact?;
        have := LinearMap.finrank_range_add_finrank_ker ( tr2 n );
        rw [ show ( tr2 n |> LinearMap.range ) = ⊤ from _ ] at this;
        · exact eq_tsub_of_add_eq ( by norm_num at this; linarith );
        · exact LinearMap.range_eq_top.mpr ( tr2_surjective hn );
      have h_ker_card : Nat.card (LinearMap.ker (tr2 n)) = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (LinearMap.ker (tr2 n)) := by
        exact?;
      rw [ ← Nat.card_eq_finsetCard ] ; congr ; aesop

theorem tr2_fiber_one_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = 2 ^ (n - 1) := by
      -- Since the trace map is surjective, the preimage of 1 is a coset of the kernel.
      have h_coset : (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = (Finset.univ.filter fun x : F2n n => tr2 n x = 0).card := by
        obtain ⟨ x, hx ⟩ := tr2_exists_one hn;
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Equiv.sum_comp ( Equiv.addRight x ) ] ; aesop;
      rw [ h_coset, tr2_kernel_card hn ]

theorem tr2_balanced {n : ℕ} (hn : n ≠ 0) (x : F2n n) (hx : x ≠ 0) :
    (Finset.univ.filter fun a : F2n n => tr2 n (a * x) = 0).card = 2 ^ (n - 1) := by
      convert tr2_kernel_card hn using 1;
      fapply Finset.card_bij (fun a ha => a * x);
      · aesop;
      · grobner;
      · exact fun b hb => ⟨ b / x, by simpa [ hx, div_mul_cancel₀ _ hx ] using hb, div_mul_cancel₀ _ hx ⟩

end Kasami