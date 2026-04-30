/-
# Artin-Schreier Theory and Trace Connection

This module establishes the connection between the Artin-Schreier map `x ↦ x² + x`
and the trace function `Tr : GF(2^n) → GF(2)`.

## Main results

* `artinSchreier_image_card` : |Im(AS)| = |F|/2
* `artinSchreier_fiber_card` : Every fiber of AS (over its image) has size 2
* `artinSchreier_image_eq_trace_ker` : Im(AS) = ker(Tr)
* `trace_frobenius` : Tr(x²) = Tr(x)

## References

* Lidl, Niederreiter, *Finite Fields*, Theorem 2.25
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

attribute [local instance] ZMod.algebra

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Fiber structure of the Artin-Schreier map -/

/-
If `artinSchreier(x₀) = y`, then the fiber over `y` is `{x₀, x₀ + 1}`.
-/
theorem artinSchreier_fiber (x₀ : F) :
    (Finset.univ.filter (fun x : F => artinSchreier x = artinSchreier x₀)) =
      {x₀, x₀ + 1} := by
  unfold artinSchreier;
  grind

/-
The Artin-Schreier map is exactly 2-to-1 onto its image.
-/
theorem artinSchreier_fiber_card (y : F) (hy : y ∈ Finset.univ.image (artinSchreier (F := F))) :
    (Finset.univ.filter (fun x : F => artinSchreier x = y)).card = 2 := by
  obtain ⟨ x₀, _, rfl ⟩ := Finset.mem_image.mp hy;
  convert congr_arg Finset.card ( artinSchreier_fiber x₀ ) using 2;
  rw [ Finset.card_pair ] ; simp +decide [ CharTwo.add_self_eq_zero ]

/-
The image of the Artin-Schreier map has `|F|/2` elements.
-/
theorem artinSchreier_image_card :
    (Finset.univ.image (artinSchreier (F := F))).card = Fintype.card F / 2 := by
  -- Use the 2-to-1 fiber structure. We have ∑_{y ∈ Im} |fiber(y)| = |F|.
  have h_sum_fiber : ∑ y ∈ Finset.image (artinSchreier (F := F)) Finset.univ, (Finset.univ.filter (fun x : F => artinSchreier x = y)).card = Fintype.card F := by
    rw [ ← Finset.card_eq_sum_card_fiberwise ];
    · rfl;
    · exact fun x _ => Finset.mem_image_of_mem _ ( Finset.mem_univ x );
  rw [ ← h_sum_fiber, Finset.sum_const_nat ];
  rw [ Nat.mul_div_cancel _ two_pos ];
  exact?

/-! ### Connection to the Trace -/

/-- The Frobenius as a `ZMod 2`-algebra automorphism of `F`. -/
private noncomputable def frobAlgEquiv : F ≃ₐ[ZMod 2] F := by
  refine AlgEquiv.ofBijective ?_ ?_
  · exact { frobenius F 2 with
      commutes' := fun r => by
        simp [frobenius_def]; rw [← map_pow]; congr 1; fin_cases r <;> simp }
  · exact (frobenius F 2).injective.bijective_of_finite

/-- The trace commutes with Frobenius: `Tr(x²) = Tr(x)` in char 2.
    This uses the fact that Frobenius is a `ZMod 2`-algebra automorphism,
    and `Algebra.trace_eq_of_algEquiv`. -/
theorem trace_frobenius (x : F) :
    Algebra.trace (ZMod 2) F (x ^ 2) = Algebra.trace (ZMod 2) F x := by
  have h := Algebra.trace_eq_of_algEquiv (frobAlgEquiv (F := F)) x
  simp [frobAlgEquiv, frobenius_def, AlgEquiv.ofBijective] at h
  exact h

/-- The Artin-Schreier image is contained in the trace kernel:
    `Tr(x² + x) = Tr(x²) + Tr(x) = 2·Tr(x) = 0`. -/
theorem artinSchreier_image_subset_trace_ker (y : F)
    (hy : y ∈ Finset.univ.image (artinSchreier (F := F))) :
    Algebra.trace (ZMod 2) F y = 0 := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  unfold artinSchreier
  rw [map_add, trace_frobenius]
  simp [CharTwo.add_self_eq_zero]

/-- The trace kernel has `|F|/2` elements (trace is a surjective
    `GF(2)`-linear map, so its kernel has index 2). -/
theorem trace_ker_card :
    (Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0)).card =
      Fintype.card F / 2 := by
  have hsurj := Algebra.trace_surjective (ZMod 2) F
  obtain ⟨a, ha⟩ := hsurj 1
  set K := Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0) with hK_def
  set K1 := Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 1) with hK1_def
  have zmod2_cases : ∀ (b : ZMod 2), b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  have h_eq : K1.card = K.card := by
    refine Finset.card_bij (fun x _ => x + a) ?_ ?_ ?_
    · intro x hx
      simp only [hK1_def, hK_def, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have := (Algebra.trace (ZMod 2) F).map_add x a
      rw [ha, hx] at this; simp only [this]; decide
    · intro x₁ _ x₂ _ h; exact add_right_cancel h
    · intro y hy
      simp only [hK_def, hK1_def, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨y + a, ?_, by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩
      have := (Algebra.trace (ZMod 2) F).map_add y a
      rw [ha, hy] at this; simp only [this]; decide
  have h_union : K ∪ K1 = Finset.univ := by
    ext x; simp only [hK_def, hK1_def, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact zmod2_cases _
  have h_disj : Disjoint K K1 :=
    Finset.disjoint_filter.mpr fun x _ h0 h1 => by simp_all
  have h_card : Fintype.card F = K.card + K1.card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ]
  rw [h_eq] at h_card; omega

/-- **Artin-Schreier image equals trace kernel**:
    `Im(x ↦ x² + x) = ker(Tr : F → 𝔽₂)`.

    Both have cardinality `|F|/2`, and the image is contained in the kernel. -/
theorem artinSchreier_image_eq_trace_ker :
    Finset.univ.image (artinSchreier (F := F)) =
      Finset.univ.filter (fun x : F => Algebra.trace (ZMod 2) F x = 0) := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact artinSchreier_image_subset_trace_ker y hy
  · rw [trace_ker_card, artinSchreier_image_card]

end