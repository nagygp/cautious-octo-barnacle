/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace map for F_{2^n} / F_2

This module specializes `Algebra.trace` to the extension `GaloisField 2 n / ZMod 2`:
- `tr2 n : F2n n →ₗ[ZMod 2] ZMod 2` — the absolute trace
- `tr2_sq`: `Tr(x²) = Tr(x)` in characteristic 2
- `tr2_surjective`: the trace is surjective (for `n ≥ 1`)
- `tr2_kernel_card`: exactly 2^{n-1} elements have trace 0

## References
- [Lidl, Niederreiter, *Finite Fields*], Chapter 2, §2.3
-/

import Mathlib
import RequestProject.WalshHadamard.Basic

namespace WalshHadamardTheory

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
    This follows because the Frobenius `x ↦ x²` is an automorphism
    that fixes F₂, permuting the Galois group elements.
-/
theorem tr2_sq {n : ℕ} (hn : n ≠ 0) (x : F2n n) : tr2 n (x ^ 2) = tr2 n x := by
  -- The trace is invariant under the Frobenius automorphism $x \mapsto x^2$, which is a consequence of the fact that $x^n$ is a $2$-power polynomial.
  have trace_frobenius : ∀ (σ : F2n n ≃ₐ[ZMod 2] F2n n), (tr2 n) (σ x) = (tr2 n) x := by
    exact fun σ => Algebra.trace_eq_of_algEquiv σ x;
  convert trace_frobenius ( _ );
  swap;
  constructor;
  case toEquiv => exact Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y h => by simpa [ sq_eq_sq_iff_eq_or_eq_neg ] using h, Finite.injective_iff_surjective.mp ( fun x y h => by simpa [ sq_eq_sq_iff_eq_or_eq_neg ] using h ) ⟩;
  all_goals norm_num [ sq ];
  · exact fun x y => by ring;
  · grind;
  · exact fun r => by rw [ ← map_mul ] ; fin_cases r <;> rfl;

/-- More generally, `Tr(x^{2^k}) = Tr(x)` for any `k`. -/
theorem tr2_pow2 {n : ℕ} (hn : n ≠ 0) (x : F2n n) (k : ℕ) :
    tr2 n (x ^ (2 ^ k)) = tr2 n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (2 ^ (k + 1)) = (x ^ (2 ^ k)) ^ 2 := by ring
    rw [this, tr2_sq hn, ih]

/-
The trace map `Tr : F_{2^n} → F₂` is surjective for `n ≥ 1`.
-/
theorem tr2_surjective {n : ℕ} (hn : n ≠ 0) : Function.Surjective (tr2 n) := by
  convert ( Algebra.trace_surjective ( ZMod 2 ) ( GaloisField 2 n ) )

/-- There exists an element with `Tr(x) = 1`. -/
theorem tr2_exists_one {n : ℕ} (hn : n ≠ 0) : ∃ x : F2n n, tr2 n x = 1 :=
  tr2_surjective hn 1

/-- The trace is nonzero (as a linear map). -/
theorem tr2_ne_zero {n : ℕ} (hn : n ≠ 0) : tr2 n ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := tr2_exists_one hn
  simp [h] at hx

/-
Exactly half the elements of F_{2^n} have trace 0.
-/
theorem tr2_kernel_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 0).card = 2 ^ (n - 1) := by
  -- The kernel of the trace map tr2 : F_{2^n} →ₗ[ZMod 2] ZMod 2 is a codimension-1 subspace (since tr2 is surjective, its range has dimension 1).
  have h_kernel : (LinearMap.ker (tr2 n)).toAddSubgroup.index = 2 := by
    have := tr2_surjective hn;
    convert AddSubgroup.index_ker ( tr2 n |> LinearMap.toAddMonoidHom );
    rw [ show ( tr2 n |> LinearMap.toAddMonoidHom |> AddMonoidHom.range ) = ⊤ from by ext; aesop ] ; simp +decide [ Nat.card_eq_fintype_card ];
  have := AddSubgroup.index_mul_card ( LinearMap.ker ( tr2 n ) |> Submodule.toAddSubgroup ) ; simp_all +decide [ Fintype.card_subtype ] ;
  -- Since the cardinality of $F_{2^n}$ is $2^n$, we can substitute this into our equation.
  have h_card : Fintype.card (F2n n) = 2 ^ n := by
    exact F2n.card n hn
  rw [h_card] at this
  exact mul_left_cancel₀ two_ne_zero (by rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at *; linarith)

/-
Exactly half the elements of F_{2^n} have trace 1.
-/
theorem tr2_fiber_one_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  obtain ⟨ x, hx ⟩ := tr2_exists_one hn;
  rw [ Finset.card_filter, Finset.card_filter ];
  rw [ ← Equiv.sum_comp ( Equiv.addRight x ) ] ; aesop

/-
`Tr(ax)` as `a` varies gives a balanced function when `x ≠ 0`.
-/
theorem tr2_balanced {n : ℕ} (hn : n ≠ 0) (x : F2n n) (hx : x ≠ 0) :
    (Finset.univ.filter fun a : F2n n => tr2 n (a * x) = 0).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card hn using 1;
  fapply Finset.card_bij';
  use fun a ha => a * x;
  use fun a ha => a * x⁻¹;
  · aesop;
  · aesop;
  · aesop;
  · aesop

end WalshHadamardTheory