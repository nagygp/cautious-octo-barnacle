import Mathlib
import RequestProject.DiffUniformity.CCZEquivalence
import RequestProject.DiffUniformity.Flystel

/-!
# CCZ-equivalence as an equivalence relation

This module advances the CCZ-equivalence (Carlet–Charpin–Zinoviev) track of
`CODING_THEORY_DIRECTIONS.md`.  The previous layers
(`RequestProject/DiffUniformity/CCZEquivalence.lean`) proved that differential
uniformity is invariant under an affine permutation of the graph
(`APN.differentialUniformity_ccz`) and that the extended-affine (EA) moves are a
special case.  This file packages the relation itself.

Two functions `f, g : V → W` are **CCZ-equivalent** (`CCZEquiv f g`) when the
graph `{(x, g x)}` is the image of `{(x, f x)}` under some affine permutation
`z ↦ A z + t` of `V × W` (`A : (V × W) ≃+ (V × W)`, `t : V × W`).  We show:

* `CCZEquiv` is an **equivalence relation** (`cczEquiv_equivalence`), with the
  individual `CCZEquiv.refl` / `CCZEquiv.symm` / `CCZEquiv.trans`;
* it is a **refinement of EA-equivalence**: the EA image
  `x ↦ σ (f (τ x)) + L x` is CCZ-equivalent to `f` (`cczEquiv_ea`), and the
  inverse of a permutation is CCZ-equivalent to it (`cczEquiv_inverse`);
* every CCZ-equivalent pair shares its **differential uniformity**
  (`CCZEquiv.differentialUniformity_eq`) and its APN / PN status
  (`CCZEquiv.isAPN`, `CCZEquiv.isPN`).

## Main results

* `CCZEquiv` — the CCZ-equivalence relation on functions `V → W`.
* `cczEquiv_equivalence` — `CCZEquiv` is an equivalence relation.
* `cczEquiv_ea`, `cczEquiv_inverse` — concrete CCZ-equivalences.
* `CCZEquiv.differentialUniformity_eq`, `CCZEquiv.isAPN`, `CCZEquiv.isPN`.
-/

open Finset

namespace APN

section Def
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- **CCZ-equivalence.**  `f` and `g` are CCZ-equivalent when the graph of `g` is
the image of the graph of `f` under an affine permutation `z ↦ A z + t` of
`V × W`. -/
def CCZEquiv (f g : V → W) : Prop :=
  ∃ (A : (V × W) ≃+ (V × W)) (t : V × W),
    graph g = (fun z => A z + t) '' graph f

/-
CCZ-equivalence is reflexive (identity affine map).
-/
theorem CCZEquiv.refl (f : V → W) : CCZEquiv f f := by
  refine' ⟨ AddEquiv.refl _, 0, _ ⟩ ; aesop

/-
CCZ-equivalence is symmetric (invert the affine permutation).
-/
theorem CCZEquiv.symm {f g : V → W} (h : CCZEquiv f g) : CCZEquiv g f := by
  obtain ⟨ A, t, h ⟩ := h;
  refine' ⟨ A.symm, -A.symm t, _ ⟩;
  convert congr_arg ( fun s => ( fun z => A.symm z + -A.symm t ) '' s ) h.symm using 1;
  ext ⟨ x, y ⟩ ; simp +decide [ graph ] ;
  exact eq_comm

/-
CCZ-equivalence is transitive (compose the affine permutations).
-/
theorem CCZEquiv.trans {f g h : V → W} (hfg : CCZEquiv f g) (hgh : CCZEquiv g h) :
    CCZEquiv f h := by
      obtain ⟨A, t, hAB⟩ := hfg
      obtain ⟨B, s, hBC⟩ := hgh
      use A.trans B, B t + s
      rw [hBC, hAB]
      simp [Set.image_image];
      simp +decide only [add_assoc]

/-- **CCZ-equivalence is an equivalence relation.** -/
theorem cczEquiv_equivalence : Equivalence (CCZEquiv (V := V) (W := W)) :=
  ⟨CCZEquiv.refl, CCZEquiv.symm, CCZEquiv.trans⟩

end Def

/-! ### EA-equivalence and inverse permutations refine to CCZ-equivalence -/

section Refine
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-
**EA-equivalence refines CCZ-equivalence.**  The extended-affine image
`x ↦ σ (f (τ x)) + L x` (with `τ : V ≃+ V`, `σ : W ≃+ W`, `L : V →+ W`) is
CCZ-equivalent to `f`.
-/
theorem cczEquiv_ea (f : V → W) (τ : V ≃+ V) (σ : W ≃+ W) (L : V →+ W) :
    CCZEquiv f (fun x => σ (f (τ x)) + L x) := by
      refine' ⟨ _, 0, _ ⟩;
      refine' { Equiv.ofBijective ( fun p => ( τ.symm p.1, σ p.2 + L ( τ.symm p.1 ) ) ) ⟨ fun p q h => _, fun p => _ ⟩ with .. } <;> simp_all +decide;
      all_goals norm_num [ Set.ext_iff, graph ];
      · aesop;
      · exact ⟨ τ p.1, σ.symm ( p.2 - L p.1 ), by simp +decide ⟩;
      · exact fun _ _ _ _ => by abel1;
      · exact fun a b => ⟨ fun h => ⟨ τ a, by simp +decide, by simpa using h.symm ⟩, by rintro ⟨ a', rfl, rfl ⟩ ; simp +decide ⟩

/-- **The inverse of a permutation is CCZ-equivalent to it.**  The graph of
`e⁻¹` is the coordinate-swap image of the graph of `e`. -/
theorem cczEquiv_inverse (e : Equiv.Perm V) : CCZEquiv (⇑e) (⇑e.symm) :=
  ⟨AddEquiv.prodComm, 0, graph_inverse_eq e⟩

end Refine

/-! ### Differential-uniformity / APN / PN transfer along CCZ-equivalence -/

section Transfer
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W]

/-- CCZ-equivalent functions have the same differential uniformity. -/
theorem CCZEquiv.differentialUniformity_eq {f g : V → W} (h : CCZEquiv f g) :
    differentialUniformity g = differentialUniformity f := by
  obtain ⟨A, t, hgf⟩ := h
  exact differentialUniformity_ccz f g A t hgf

/-- APN-ness transfers along CCZ-equivalence. -/
theorem CCZEquiv.isAPN {f g : V → W} (h : CCZEquiv f g) (hf : IsAPN f) : IsAPN g := by
  unfold IsAPN at *; rw [h.differentialUniformity_eq]; exact hf

/-- PN-ness transfers along CCZ-equivalence. -/
theorem CCZEquiv.isPN {f g : V → W} (h : CCZEquiv f g) (hf : IsPN f) : IsPN g := by
  unfold IsPN at *; rw [h.differentialUniformity_eq]; exact hf

end Transfer

end APN