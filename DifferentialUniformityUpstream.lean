import Mathlib

/-!
# Differential uniformity, APN and PN functions

The *differential uniformity* of a function `f` between additive groups is the
largest number of solutions `x` of `f (x + a) - f x = b`, taken over all
directions `a ≠ 0` and all targets `b`.  It is the central measure of resistance
to differential cryptanalysis: `f` is **APN** (almost perfect nonlinear) when the
uniformity is `2`, and **PN** (planar / perfect nonlinear) when it is `1`.

The development is deliberately assumption-minimal: each notion is introduced
with only the structure it needs.

* `derivMap` and `IsAtMostTwoToOne` need just `[Add V]` / `[Sub W]`.
* `fiberCard` counts solutions with `Nat.card`, so it needs no `DecidableEq` or
  `Fintype` on the codomain (it is `0` on an infinite fibre).
* `differentialUniformity` requires only the *domain* to be finite; the codomain
  may be infinite, since the supremum ranges over the achieved derivative values.

## Main results

* `card_le_two_iff`: a finite type has at most two elements iff among any three
  of them two coincide.  This is the combinatorial core of APN-ness.
* `isAtMostTwoToOne_iff_diffUnif_le_two`: the collision characterisation of
  uniformity `≤ 2`.
* `differentialUniformity_comp_addEquiv`, `IsAPN.comp_addEquiv`,
  `IsPN.comp_addEquiv`: invariance under post-composition with an additive
  equivalence.
* `IsAPN.comp_frobenius`: over a finite field of characteristic two,
  post-composing an APN function with `x ↦ x ^ (2 ^ j)` is again APN.
* `atMostTwoToOne_charTwo_collision`: in characteristic two, uniformity `≤ 2`
  is the classical collision form `y = x ∨ y = x + a`.
-/

open Finset

namespace APN

/-! ### A combinatorial counting lemma -/

/-- A finite type has at most two elements precisely when, among any three of
them, two already coincide. -/
theorem card_le_two_iff {α : Type*} [Finite α] :
    Nat.card α ≤ 2 ↔ ∀ x y z : α, x = y ∨ x = z ∨ y = z := by
  classical
  cases nonempty_fintype α
  rw [Nat.card_eq_fintype_card, ← not_lt, ← Finset.card_univ, Finset.two_lt_card_iff]
  push_neg
  refine ⟨fun h x y z => ?_, fun h x y z _ _ _ hxy hxz => ?_⟩
  · by_contra hc
    push_neg at hc
    exact hc.2.2 (h x y z (mem_univ _) (mem_univ _) (mem_univ _) hc.1 hc.2.1)
  · rcases h x y z with rfl | rfl | rfl <;> simp_all

/-! ### Basic definitions -/

section Defs
variable {V W : Type*} [Add V] [Zero V] [Sub W]

/-- The discrete derivative of `f` in direction `a`: `x ↦ f (x + a) - f x`. -/
def derivMap (f : V → W) (a x : V) : W := f (x + a) - f x

/-- The number of solutions `x` of `derivMap f a x = b`, counted with `Nat.card`
(hence `0` on an infinite fibre). -/
noncomputable def fiberCard (f : V → W) (a : V) (b : W) : ℕ :=
  Nat.card {x : V // derivMap f a x = b}

/-- Among any three points sharing a derivative value, two coincide. -/
def IsAtMostTwoToOne (f : V → W) : Prop :=
  ∀ a : V, a ≠ 0 → ∀ x y z : V,
    derivMap f a x = derivMap f a y → derivMap f a x = derivMap f a z →
      x = y ∨ x = z ∨ y = z

end Defs

/-! ### Differential uniformity over a finite domain -/

section Numeric
variable {V W : Type*} [AddGroup V] [Sub W] [Fintype V]

open scoped Classical in
/-- The largest fibre of `f`'s derivative maps over all nonzero directions.  Only
the domain is required finite: the inner supremum ranges over the *achieved*
derivative values `derivMap f a x`, which are exactly those with a nonzero
fibre. -/
noncomputable def differentialUniformity (f : V → W) : ℕ :=
  univ.sup fun a : V =>
    if a = 0 then 0 else univ.sup fun x : V => fiberCard f a (derivMap f a x)

/-- `differentialUniformity f ≤ n` unfolds to a uniform bound on every fibre. -/
lemma diffUnif_le_iff (f : V → W) (n : ℕ) :
    differentialUniformity f ≤ n ↔ ∀ a : V, a ≠ 0 → ∀ b : W, fiberCard f a b ≤ n := by
  simp only [differentialUniformity, Finset.sup_le_iff, mem_univ, true_implies]
  refine ⟨fun h a ha b => ?_, fun h a => ?_⟩
  · rcases eq_or_ne (fiberCard f a b) 0 with hb | hb
    · simp [hb]
    · obtain ⟨⟨x, hx⟩, _⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hb)
      have hsup := h a
      rw [if_neg ha, Finset.sup_le_iff] at hsup
      simpa [hx] using hsup x (mem_univ x)
  · split_ifs with ha
    · exact Nat.zero_le n
    · exact Finset.sup_le fun x _ => h a ha _

lemma fiberCard_le_diffUnif (f : V → W) {a : V} (ha : a ≠ 0) (b : W) :
    fiberCard f a b ≤ differentialUniformity f :=
  (diffUnif_le_iff f _).mp le_rfl a ha b

/-- The collision characterisation: uniformity `≤ 2` is exactly two-to-one-ness. -/
lemma isAtMostTwoToOne_iff_diffUnif_le_two (f : V → W) :
    IsAtMostTwoToOne f ↔ differentialUniformity f ≤ 2 := by
  rw [diffUnif_le_iff]
  refine ⟨fun h a ha b => ?_, fun h a ha x y z hxy hxz => ?_⟩
  · rw [fiberCard, card_le_two_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simpa [Subtype.ext_iff] using h a ha x y z (hx.trans hy.symm) (hx.trans hz.symm)
  · have := (card_le_two_iff.mp (h a ha (derivMap f a x)))
      ⟨x, rfl⟩ ⟨y, hxy.symm⟩ ⟨z, hxz.symm⟩
    simpa [Subtype.ext_iff] using this

/-- **APN** (almost perfect nonlinear): differential uniformity exactly `2`. -/
def IsAPN (f : V → W) : Prop := differentialUniformity f = 2

/-- **PN** (planar / perfect nonlinear): differential uniformity exactly `1`. -/
def IsPN (f : V → W) : Prop := differentialUniformity f = 1

end Numeric

/-! ### Invariance under post-composition with an additive equivalence -/

section Closure
variable {V W W' : Type*} [AddGroup V] [AddGroup W] [AddGroup W'] [Fintype V]

omit [Fintype V] in
lemma derivMap_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a x : V) :
    derivMap (σ ∘ f) a x = σ (derivMap f a x) := by
  simp [derivMap, map_sub]

omit [Fintype V] in
lemma fiberCard_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a : V) (b : W') :
    fiberCard (σ ∘ f) a b = fiberCard f a (σ.symm b) := by
  simp only [fiberCard, derivMap_comp_addEquiv, σ.eq_symm_apply]

lemma differentialUniformity_comp_addEquiv (f : V → W) (σ : W ≃+ W') :
    differentialUniformity (σ ∘ f) = differentialUniformity f := by
  refine le_antisymm ((diffUnif_le_iff _ _).2 fun a ha b => ?_)
    ((diffUnif_le_iff _ _).2 fun a ha b => ?_)
  · rw [fiberCard_comp_addEquiv]
    exact fiberCard_le_diffUnif f ha _
  · have := fiberCard_le_diffUnif (σ ∘ f) ha (σ b)
    rwa [fiberCard_comp_addEquiv, σ.symm_apply_apply] at this

theorem IsAPN.comp_addEquiv {f : V → W} (hf : IsAPN f) (σ : W ≃+ W') : IsAPN (σ ∘ f) := by
  rw [IsAPN, differentialUniformity_comp_addEquiv]; exact hf

theorem IsPN.comp_addEquiv {f : V → W} (hf : IsPN f) (σ : W ≃+ W') : IsPN (σ ∘ f) := by
  rw [IsPN, differentialUniformity_comp_addEquiv]; exact hf

end Closure

/-! ### Post-composition with a Frobenius power in characteristic two -/

section Frobenius
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Over a finite field of characteristic two, post-composing an APN function
with the Frobenius power `x ↦ x ^ (2 ^ j)` stays APN: that power is an additive
equivalence, so this is an instance of `IsAPN.comp_addEquiv`. -/
theorem IsAPN.comp_frobenius {f : F → F} (hf : IsAPN f) (j : ℕ) :
    IsAPN (fun x => (f x) ^ (2 ^ j)) := by
  have hbij : Function.Bijective (fun x : F => x ^ (2 ^ j)) := by
    have : (fun x : F => x ^ (2 ^ j)) = iterateFrobenius F 2 j := by
      ext x; simp [iterateFrobenius_def]
    rw [this]
    exact Finite.injective_iff_bijective.mp (iterateFrobenius F 2 j).injective
  let σ : F ≃+ F :=
    { Equiv.ofBijective _ hbij with
      map_add' := fun x y => add_pow_char_pow (p := 2) (n := j) x y }
  exact hf.comp_addEquiv σ

end Frobenius

/-! ### The collision form in characteristic two -/

section CharTwo
variable {F : Type*} [Ring F] [Fintype F] [CharP F 2]

omit [Fintype F] in
/-- In characteristic two the derivative is invariant under shifting by `a`. -/
lemma derivMap_shift (f : F → F) (a x : F) : derivMap f a (x + a) = derivMap f a x := by
  simp only [derivMap]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, CharTwo.sub_eq_add, CharTwo.sub_eq_add,
    add_comm]

omit [Fintype F] [CharP F 2] in
lemma ne_add_right {a : F} (x : F) (ha : a ≠ 0) : x ≠ x + a := by
  intro h; exact ha (by simpa using sub_eq_zero.mpr h.symm)

/-- Every derivative map is at least two-to-one in characteristic two: `0` and
`a` share the value `derivMap f a 0`. -/
lemma two_le_diffUnif_charTwo [Nontrivial F] (f : F → F) :
    2 ≤ differentialUniformity f := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  refine le_trans ?_ (fiberCard_le_diffUnif f ha (derivMap f a 0))
  have h : derivMap f a a = derivMap f a 0 := by simpa using derivMap_shift f a 0
  have hinj : Function.Injective
      (fun b : Bool => if b then (⟨a, h⟩ : {x : F // derivMap f a x = derivMap f a 0})
        else ⟨0, rfl⟩) := by
    intro p q hpq
    cases p <;> cases q <;> simp_all [Subtype.ext_iff, eq_comm]
  calc (2 : ℕ) = Nat.card Bool := by simp
    _ ≤ fiberCard f a (derivMap f a 0) := Nat.card_le_card_of_injective _ hinj

/-- In characteristic two, uniformity `≤ 2` is the classical collision form:
two inputs with the same derivative differ by `0` or `a`. -/
lemma atMostTwoToOne_charTwo_collision (f : F → F) (h : differentialUniformity f ≤ 2) :
    ∀ a : F, a ≠ 0 → ∀ x y : F,
      f (x + a) - f x = f (y + a) - f y → y = x ∨ y = x + a := by
  intro a ha x y hxy
  have hcol := (isAtMostTwoToOne_iff_diffUnif_le_two f).2 h a ha x y (x + a)
    hxy (derivMap_shift f a x).symm
  rcases hcol with h1 | h2 | h3
  · exact Or.inl h1.symm
  · exact absurd h2 (ne_add_right x ha)
  · exact Or.inr h3

end CharTwo

end APN
