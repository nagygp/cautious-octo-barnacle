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

/-
`Tr(1)` is well-defined and is in F₂.
-/
theorem tr2_one_val (n : ℕ) : tr2 n 1 ∈ ({0, 1} : Set (ZMod 2)) := by
  exact Fin.exists_fin_two.mp ⟨ _, rfl ⟩

/-
`Tr(x²) = Tr(x)` in characteristic 2.
    This follows because the Frobenius `x ↦ x²` is a ring automorphism that fixes F₂,
    so it permutes the Galois group elements, leaving the trace invariant.
    Alternatively: `Tr(x) = ∑_{i=0}^{n-1} x^{2^i}`, so
    `Tr(x²) = ∑_{i=0}^{n-1} x^{2^{i+1}} = ∑_{i=1}^{n} x^{2^i} = Tr(x)`
    (since `x^{2^n} = x` in F_{2^n}).
-/
theorem tr2_sq {n : ℕ} (hn : n ≠ 0) (x : F2n n) : tr2 n (x ^ 2) = tr2 n x := by
  -- The trace is invariant under the Frobenius automorphism.
  have h_trace_frob : ∀ x : F2n n, (tr2 n) (x ^ 2) = (tr2 n) x := by
    intro x
    have h_trace_invariant : (tr2 n) (x ^ 2) = (tr2 n) x := by
      have h_tr : ∀ σ : F2n n →ₐ[ZMod 2] F2n n, (tr2 n) (σ x) = (tr2 n) x := by
        intro σ
        have h_tr : (tr2 n) (σ x) = (tr2 n) x := by
          have h_alg : IsGalois (ZMod 2) (F2n n) := by
            exact?
          have h_trace_frob : ∀ σ : F2n n ≃ₐ[ZMod 2] F2n n, (tr2 n) (σ x) = (tr2 n) x := by
            exact?;
          convert h_trace_frob ( AlgEquiv.ofBijective σ ?_ ) using 1;
          exact?;
        exact h_tr
      convert h_tr ( AlgHom.mk' ( RingHom.comp ( RingEquiv.toRingHom ( show F2n n ≃+* F2n n from RingEquiv.refl _ ) ) ( frobenius ( F2n n ) 2 ) ) _ ) using 1;
      intro c x; fin_cases c <;> simp +decide ;
    exact h_trace_invariant;
  exact h_trace_frob x

/-
More generally, `Tr(x^{2^k}) = Tr(x)` for any `k`.
-/
theorem tr2_pow2 {n : ℕ} (hn : n ≠ 0) (x : F2n n) (k : ℕ) :
    tr2 n (x ^ (2 ^ k)) = tr2 n x := by
  induction' k with k ih;
  · norm_num;
  · convert tr2_sq hn ( x ^ 2 ^ k ) using 1 ; ring;
    exact ih.symm

/-
The trace map `Tr : F_{2^n} → F₂` is surjective for `n ≥ 1`.
    This follows from the fact that `Tr` is a nonzero F₂-linear functional
    on a vector space over F₂ (a nonzero linear functional is always surjective
    when the codomain is F₂).
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
  -- The kernel of `tr2` is a subspace of dimension `n - 1`.
  have h_ker_dim : Module.finrank (ZMod 2) (LinearMap.ker (tr2 n)) = n - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker ( tr2 n : F2n n →ₗ[ZMod 2] ZMod 2 );
    -- Since the range of `tr2` is all of `ZMod 2`, its dimension is 1.
    have h_range : Module.finrank (ZMod 2) (LinearMap.range (tr2 n)) = 1 := by
      rw [ LinearMap.range_eq_top.mpr ] <;> norm_num;
      exact?;
    exact eq_tsub_of_add_eq ( by linarith! [ show Module.finrank ( ZMod 2 ) ( F2n n ) = n from by rw [ @GaloisField.finrank ] ; aesop ] );
  convert congr_arg ( fun x : ℕ => 2 ^ x ) h_ker_dim using 1;
  convert ( Fintype.card_eq_nat_card );
  any_goals exact { x : F2n n // tr2 n x = 0 };
  all_goals exact?

/-
Exactly half the elements of F_{2^n} have trace 1.
-/
theorem tr2_fiber_one_card {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ.filter fun x : F2n n => tr2 n x = 1).card = 2 ^ (n - 1) := by
  -- Since these two sets are complementary within the set of all elements in F_{2^n}, their cardinalities are equal.
  have h_compl : (Finset.univ.filter (fun x => tr2 n x = 1)).card + (Finset.univ.filter (fun x => tr2 n x = 0)).card = 2 ^ n := by
    convert F2n.card n hn using 1;
    rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases tr2 n x with ( _ | _ | m ) <;> trivial;
  linarith [ tr2_kernel_card hn, show 2 ^ n = 2 * 2 ^ ( n - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hn ) ] ]

/-
`Tr(ax)` as `a` varies gives a balanced function when `x ≠ 0`.
-/
theorem tr2_balanced {n : ℕ} (hn : n ≠ 0) (x : F2n n) (hx : x ≠ 0) :
    (Finset.univ.filter fun a : F2n n => tr2 n (a * x) = 0).card = 2 ^ (n - 1) := by
  convert tr2_kernel_card ( n := n ) hn using 1;
  refine' Finset.card_bij ( fun a ha => a * x ) _ _ _ <;> simp_all +decide;
  exact fun b hb => ⟨ b / x, by simpa [ hx ] using hb, div_mul_cancel₀ _ hx ⟩

end Kasami