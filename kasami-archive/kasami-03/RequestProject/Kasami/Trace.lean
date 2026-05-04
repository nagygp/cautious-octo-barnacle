/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace map for F_{2^n} / F_2

This module specializes `Algebra.trace` to the extension `GaloisField 2 n / ZMod 2`:
- `tr2 n : F2n n →ₗ[ZMod 2] ZMod 2` — the absolute trace
- `tr2_sq`: `Tr(x²) = Tr(x)` in characteristic 2
- `tr2_surjective`: the trace is surjective (for `n ≥ 1`)
- `tr2_frob`: `Tr(x^2) = Tr(x)` via Frobenius

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

/-- `Tr(1)` is well-defined and is in F₂. -/
theorem tr2_one_val (n : ℕ) : tr2 n 1 ∈ ({0, 1} : Set (ZMod 2)) := by
  exact Fin.exists_fin_two.mp ⟨_, rfl⟩

/-
`Tr(x²) = Tr(x)` in characteristic 2.
-/
theorem tr2_sq {n : ℕ} (hn : n ≠ 0) (x : F2n n) : tr2 n (x ^ 2) = tr2 n x := by
  -- The Frobenius endomorphism $x \mapsto x^2$ is an automorphism of $F_{2^n}$.
  have h_frobenius : ∃ (σ : F2n n ≃ₐ[ZMod 2] F2n n), ∀ x : F2n n, σ x = x^2 := by
    have h_frobenius : Function.Bijective (fun x : F2n n => x^2) := by
      have h_frobenius : Function.Injective (fun x : F2n n => x^2) := by
        intro x y hxy;
        grind +qlia;
      exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
    refine' ⟨ { Equiv.ofBijective _ h_frobenius with map_add' := _, map_mul' := _, commutes' := _ }, fun x => rfl ⟩;
    · simp +decide [ mul_pow ];
    · simp +decide [ add_sq ];
      exact fun x y => Or.inl <| Or.inl <| by exact?;
    · intro r; fin_cases r <;> simp +decide ;
  obtain ⟨ σ, hσ ⟩ := h_frobenius;
  simp +decide [ ← hσ ];
  exact?

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
  refine' ( LinearMap.surjective_of_ne_zero _ );
  convert Algebra.trace_ne_zero ( ZMod 2 ) ( F2n n )

/-- There exists an element with `Tr(x) = 1`. -/
theorem tr2_exists_one {n : ℕ} (hn : n ≠ 0) : ∃ x : F2n n, tr2 n x = 1 := by
  exact tr2_surjective hn 1

/-
Exactly half the elements of F_{2^n} have trace 0.
-/
theorem tr2_kernel_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 0).card = 2 ^ (n - 1) := by
  have h_kernel_card : LinearMap.ker (tr2 n) ≃ₗ[ZMod 2] Fin (n - 1) → ZMod 2 := by
    refine' ( LinearEquiv.ofFinrankEq .. );
    have h_dim : Module.finrank (ZMod 2) (F2n n) = n := by
      rw [ GaloisField.finrank ] ; aesop;
    have := LinearMap.finrank_range_add_finrank_ker ( tr2 n );
    rw [ show ( tr2 n |> LinearMap.range ) = ⊤ from _ ] at this;
    · cases n <;> simp_all +decide [ Module.finrank_self ];
      linarith;
    · exact LinearMap.range_eq_top.mpr ( tr2_surjective hn );
  have := h_kernel_card.cardinal_eq;
  simp +zetaDelta at *;
  rw [ ← Fintype.card_subtype ] at * ; norm_cast at *

/-
Exactly half the elements of F_{2^n} have trace 1.
-/
theorem tr2_fiber_one_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  obtain ⟨ t, ht ⟩ := tr2_exists_one hn;
  rw [ Finset.card_filter, Finset.card_filter ];
  rw [ ← Equiv.sum_comp ( Equiv.addRight t ) ] ; aesop

/-
`Tr(ax)` as `a` varies gives a balanced function when `x ≠ 0`.
-/
theorem tr2_balanced {n : ℕ} (hn : n ≠ 0) (x : F2n n) (hx : x ≠ 0) :
    (Finset.univ.filter fun a : F2n n => tr2 n (a * x) = 0).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  rw [ Finset.card_filter, Finset.card_filter ];
  conv_rhs => rw [ ← Equiv.sum_comp ( Equiv.mulRight₀ x hx ) ] ;
  rfl

end Kasami