import Mathlib

/-!
# Differential uniformity and APN / PN functions

The **differential uniformity** of a function `f` between finite additive groups is the
maximum fibre size of its derivative maps `x ↦ f (x + a) - f x` over all `a ≠ 0`.
It is characteristic-free: `IsAPN f` means it equals `2`, `IsPN f` (planar) means it equals `1`.

## Main results

* `differentialUniformity_comp_addEquiv`: differential uniformity is invariant under
  post-composition with an additive equivalence, hence `IsAPN.comp_addEquiv` and `IsPN.comp_addEquiv`.
* `IsAPN.comp_frobenius`: over a finite field of characteristic two, post-composing an APN
  function with `x ↦ x ^ (2 ^ j)` is again APN.
* `atMostTwoToOne_charTwo_collision`: in characteristic two, uniformity `≤ 2` recovers the
  classical collision form `y = x ∨ y = x + a`.
-/

open Finset

namespace APNLib

section Defs
variable {V W : Type*} [AddGroup V] [AddGroup W]

/-- The discrete derivative of `f` in direction `a`: `x ↦ f (x + a) - f x`. -/
def derivMap (f : V → W) (a x : V) : W := f (x + a) - f x

variable [Fintype V] [DecidableEq W]

/-- The number of solutions `x` of `derivMap f a x = b`. -/
def fiberCard (f : V → W) (a : V) (b : W) : ℕ :=
  (univ.filter fun x => derivMap f a x = b).card

end Defs

section Numeric
variable {V W : Type*} [AddGroup V] [AddGroup W]
  [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The maximum fibre size of `f`'s derivative maps over all nonzero directions. -/
def differentialUniformity (f : V → W) : ℕ :=
  (univ.filter fun a : V => a ≠ 0).sup fun a => univ.sup fun b => fiberCard f a b

lemma diffUnif_le_iff (f : V → W) (n : ℕ) :
    differentialUniformity f ≤ n ↔ ∀ a : V, a ≠ 0 → ∀ b : W, fiberCard f a b ≤ n := by
  simp +decide [differentialUniformity, Finset.sup_le_iff]

lemma fiberCard_le_diffUnif (f : V → W) {a : V} (ha : a ≠ 0) (b : W) :
    fiberCard f a b ≤ differentialUniformity f :=
  le_trans (Finset.le_sup (f := fun b => fiberCard f a b) (Finset.mem_univ b))
    (Finset.le_sup (f := fun a => Finset.sup (Finset.univ : Finset W) fun b => fiberCard f a b)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩))

/-- Among any three points sharing a derivative value, at least two coincide. -/
def IsAtMostTwoToOne (f : V → W) : Prop :=
  ∀ a : V, a ≠ 0 → ∀ x y z : V,
    derivMap f a x = derivMap f a y → derivMap f a x = derivMap f a z →
      x = y ∨ x = z ∨ y = z

lemma isAtMostTwoToOne_iff_diffUnif_le_two (f : V → W) :
    IsAtMostTwoToOne f ↔ differentialUniformity f ≤ 2 := by
  rw [diffUnif_le_iff]
  constructor <;> intro h a ha b <;> contrapose! h
  · obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ :
        ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
          derivMap f a x = b ∧ derivMap f a y = b ∧ derivMap f a z = b := by
      obtain ⟨s, hs⟩ := Finset.two_lt_card.mp h
      grind
    exact fun h => by have := h a ha x y z; aesop
  · obtain ⟨y, z, hy, hz, hyz⟩ := h
    exact ⟨a, ha, derivMap f a b, Finset.two_lt_card.2 ⟨b, by aesop, y, by aesop, z, by aesop⟩⟩

/-- **APN**: differential uniformity exactly `2`. -/
def IsAPN (f : V → W) : Prop := differentialUniformity f = 2

/-- **PN** (planar / perfect nonlinear): differential uniformity exactly `1`. -/
def IsPN (f : V → W) : Prop := differentialUniformity f = 1

end Numeric

section Closure
variable {V W W' : Type*} [AddGroup V] [AddGroup W] [AddGroup W']
  [Fintype V] [Fintype W] [Fintype W'] [DecidableEq V] [DecidableEq W] [DecidableEq W']

omit [Fintype V] [Fintype W] [Fintype W'] [DecidableEq V] [DecidableEq W] [DecidableEq W'] in
lemma derivMap_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a x : V) :
    derivMap (σ ∘ f) a x = σ (derivMap f a x) := by
  simp [derivMap, map_sub]

omit [Fintype W] [Fintype W'] [DecidableEq V] in
lemma fiberCard_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a : V) (b : W') :
    fiberCard (σ ∘ f) a b = fiberCard f a (σ.symm b) := by
  convert congr_arg Finset.card (Finset.ext fun x => ?_) using 2
  simp +decide [derivMap, ← σ.injective.eq_iff]

/-- Differential uniformity is invariant under post-composition with an additive equivalence. -/
lemma differentialUniformity_comp_addEquiv (f : V → W) (σ : W ≃+ W') :
    differentialUniformity (σ ∘ f) = differentialUniformity f := by
  refine le_antisymm ((diffUnif_le_iff _ _).2 ?_) ((diffUnif_le_iff _ _).2 ?_)
  · exact fun a ha b => fiberCard_comp_addEquiv f σ a b ▸ fiberCard_le_diffUnif f ha _
  · intro a ha b
    convert fiberCard_le_diffUnif (σ ∘ f) ha (σ b) using 1
    convert (fiberCard_comp_addEquiv f σ a (σ b)).symm using 1
    simp +decide

theorem IsAPN.comp_addEquiv {f : V → W} (hf : IsAPN f) (σ : W ≃+ W') : IsAPN (σ ∘ f) := by
  unfold IsAPN at *; rw [differentialUniformity_comp_addEquiv]; exact hf

theorem IsPN.comp_addEquiv {f : V → W} (hf : IsPN f) (σ : W ≃+ W') : IsPN (σ ∘ f) := by
  unfold IsPN at *; rw [differentialUniformity_comp_addEquiv]; exact hf

end Closure

section Frobenius
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Over a finite field of characteristic two, post-composing an APN function with the
Frobenius power map `x ↦ x ^ (2 ^ j)` is again APN. -/
theorem IsAPN.comp_frobenius {f : F → F} (hf : IsAPN f) (j : ℕ) :
    IsAPN (fun x => (f x) ^ (2 ^ j)) := by
  have hbij : Function.Bijective (fun x : F => x ^ (2 ^ j)) := by
    have hfrob : (fun x : F => x ^ (2 ^ j)) = iterateFrobenius F 2 j := by
      ext x; simp [iterateFrobenius_def]
    rw [hfrob]
    exact Finite.injective_iff_bijective.mp (iterateFrobenius F 2 j).injective
  let σ : F ≃+ F :=
    { toFun := fun x => x ^ (2 ^ j)
      invFun := (Equiv.ofBijective _ hbij).symm
      left_inv := (Equiv.ofBijective _ hbij).left_inv
      right_inv := (Equiv.ofBijective _ hbij).right_inv
      map_add' := fun x y => add_pow_char_pow (p := 2) (n := j) x y }
  exact hf.comp_addEquiv σ

end Frobenius

section CharTwo
variable {F : Type*} [Ring F] [Fintype F] [DecidableEq F] [CharP F 2] [Nontrivial F]

omit [Fintype F] [DecidableEq F] [Nontrivial F] in
lemma derivMap_shift (f : F → F) (a x : F) : derivMap f a (x + a) = derivMap f a x := by
  convert sub_eq_sub_iff_add_eq_add.mpr _ using 1
  norm_num [add_assoc, CharTwo.add_self_eq_zero]

omit [Fintype F] [DecidableEq F] [CharP F 2] [Nontrivial F] in
lemma ne_add_right {a : F} (x : F) (ha : a ≠ 0) : x ≠ x + a := by grind

lemma two_le_diffUnif_charTwo (f : F → F) : 2 ≤ differentialUniformity f := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  refine le_trans ?_ (fiberCard_le_diffUnif f ha (derivMap f a 0))
  refine Finset.one_lt_card.mpr ⟨0, ?_, a, ?_, ?_⟩ <;> simp +decide [derivMap]
  · simp +decide [← two_smul F, CharTwo.two_eq_zero]
    grind +suggestions
  · exact Ne.symm ha

omit [Nontrivial F] in
/-- In characteristic two, uniformity `≤ 2` is the classical collision form `y = x ∨ y = x + a`. -/
lemma atMostTwoToOne_charTwo_collision (f : F → F) (h : differentialUniformity f ≤ 2) :
    ∀ a : F, a ≠ 0 → ∀ x y : F,
      f (x + a) - f x = f (y + a) - f y → y = x ∨ y = x + a := by
  intro a ha x y hxy
  have := (isAtMostTwoToOne_iff_diffUnif_le_two f).mpr h a ha x y (x + a)
  simp_all +decide [derivMap]
  simp_all +decide [← hxy, add_assoc]
  simp_all +decide [CharTwo.add_self_eq_zero]
  grind +qlia

end CharTwo

end APNLib
