import Mathlib

/-!
# Differential uniformity and APN / PN functions (upstreaming candidate)

This file is a generalized, dependency-free reformulation of the abstract
differential-uniformity foundation, intended as a candidate for upstreaming to
Mathlib.  Compared to the project-internal version
(`RequestProject/DiffUniformity/DifferentialUniformity.lean`) the typeclass
assumptions have been weakened to the minimum each declaration needs:

* `derivMap` and `IsAtMostTwoToOne` use only `[Add V]` / `[Sub W]`; there is no
  finiteness or decidability hypothesis on the codomain.
* `fiberCard` is phrased with `Nat.card` of a fibre subtype, so it needs no
  `DecidableEq` and no `Fintype` (it is `0` on infinite fibres).
* `differentialUniformity` keeps only `[Fintype V]` on the *domain*; in
  particular the codomain `W` may be **infinite**, because the supremum over the
  target value `b` is taken over the (finite) set of achieved derivative values
  rather than over a `Fintype W`.

The **differential uniformity** of a function `f` between additive groups is the
maximum fibre size of its derivative maps `x ↦ f (x + a) - f x` over all `a ≠ 0`.
It is characteristic-free: `IsAPN f` means it equals `2`, `IsPN f` (planar) means
it equals `1`.

## Main results

* `differentialUniformity_comp_addEquiv`: differential uniformity is invariant
  under post-composition with an additive equivalence, hence
  `IsAPN.comp_addEquiv` and `IsPN.comp_addEquiv`.
* `IsAPN.comp_frobenius`: over a finite field of characteristic two,
  post-composing an APN function with `x ↦ x ^ (2 ^ j)` is again APN.
* `atMostTwoToOne_charTwo_collision`: in characteristic two, uniformity `≤ 2`
  recovers the classical collision form `y = x ∨ y = x + a`.
-/

open Finset

namespace APN

/-! ### Definitions with minimal assumptions -/

section Defs
variable {V W : Type*} [Add V] [Zero V] [Sub W]

/-- The discrete derivative of `f` in direction `a`: `x ↦ f (x + a) - f x`.

This needs only `[Add V]` on the domain and `[Sub W]` on the codomain. -/
def derivMap (f : V → W) (a x : V) : W := f (x + a) - f x

/-- The number of solutions `x` of `derivMap f a x = b`, as the cardinality of the
fibre subtype.  Using `Nat.card` avoids any `DecidableEq`/`Fintype` assumption on
`W`; it equals `0` when the fibre is infinite. -/
noncomputable def fiberCard (f : V → W) (a : V) (b : W) : ℕ :=
  Nat.card {x : V // derivMap f a x = b}

/-- Among any three points sharing a derivative value, at least two coincide.

Needs only `[Add V]` / `[Sub W]`; no finiteness. -/
def IsAtMostTwoToOne (f : V → W) : Prop :=
  ∀ a : V, a ≠ 0 → ∀ x y z : V,
    derivMap f a x = derivMap f a y → derivMap f a x = derivMap f a z →
      x = y ∨ x = z ∨ y = z

end Defs

/-! ### The numeric differential uniformity over a finite domain -/

section Numeric
variable {V W : Type*} [AddGroup V] [Sub W] [Fintype V]

open scoped Classical in
/-- The maximum fibre size of `f`'s derivative maps over all nonzero directions.

Only the domain `V` is required to be finite; the codomain `W` may be infinite.
The inner supremum ranges over the achieved derivative values
`derivMap f a x` (`x : V`), which are exactly the values `b` with nonzero fibre,
so no `Fintype W` is needed. -/
noncomputable def differentialUniformity (f : V → W) : ℕ :=
  univ.sup fun a : V =>
    if a = 0 then 0 else univ.sup fun x : V => fiberCard f a (derivMap f a x)

lemma diffUnif_le_iff (f : V → W) (n : ℕ) :
    differentialUniformity f ≤ n ↔ ∀ a : V, a ≠ 0 → ∀ b : W, fiberCard f a b ≤ n := by
  refine' ⟨ fun h a ha b => _, fun h => _ ⟩;
  · by_cases hb : fiberCard f a b = 0;
    · exact hb.symm ▸ Nat.zero_le _;
    · obtain ⟨ x, hx ⟩ := Nat.card_pos_iff.mp ( Nat.pos_of_ne_zero hb );
      obtain ⟨ x, hx ⟩ := x; have := h; simp_all +decide [ differentialUniformity ] ;
      specialize h a ; aesop;
  · refine' Finset.sup_le _;
    intro a _; split_ifs <;> [ simp +decide ; exact Finset.sup_le fun x _ => h a ( by aesop ) _ ] ;

lemma fiberCard_le_diffUnif (f : V → W) {a : V} (ha : a ≠ 0) (b : W) :
    fiberCard f a b ≤ differentialUniformity f := by
  -- Apply the already-stated `diffUnif_le_iff` at `n = differentialUniformity f`.
  apply (diffUnif_le_iff f (differentialUniformity f)).mp (le_refl _) a ha b

lemma isAtMostTwoToOne_iff_diffUnif_le_two (f : V → W) :
    IsAtMostTwoToOne f ↔ differentialUniformity f ≤ 2 := by
  rw [ diffUnif_le_iff ];
  constructor <;> intro h a ha b <;> contrapose! h;
  · -- By definition of `fiberCard`, there exist distinct elements `x, y, z` in `V` such that `derivMap f a x = derivMap f a y = derivMap f a z = b`.
    obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ : ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ derivMap f a x = b ∧ derivMap f a y = b ∧ derivMap f a z = b := by
      obtain ⟨ s, hs ⟩ := Nat.card_pos_iff.mp ( pos_of_gt h );
      have := Nat.card_eq_finsetCard ( Set.Finite.toFinset ( Set.finite_coe_iff.mp hs ) ) ; simp_all +decide ;
      obtain ⟨ t, ht ⟩ := Finset.two_lt_card.1 ( by linarith! : 2 < Finset.card ( Set.Finite.toFinset ( Set.finite_coe_iff.mp hs ) ) );
      rcases ht with ⟨ ht₁, u, hu₁, v, hv₁, htu, htv, huv ⟩ ; use t, u, by aesop, v; aesop;
    exact fun h => by have := h a ha x y z; aesop;
  · obtain ⟨ y, z, hy, hz, hby, hbz, hyz ⟩ := h;
    refine' ⟨ a, ha, derivMap f a b, _ ⟩;
    refine' ( Nat.lt_of_lt_of_le _ ( Set.ncard_le_ncard ( show { b, y, z } ⊆ { x : V | derivMap f a x = derivMap f a b } from _ ) ) );
    · rw [ Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton ] <;> aesop;
    · grind +qlia

/-- **APN**: differential uniformity exactly `2`. -/
def IsAPN (f : V → W) : Prop := differentialUniformity f = 2

/-- **PN** (planar / perfect nonlinear): differential uniformity exactly `1`. -/
def IsPN (f : V → W) : Prop := differentialUniformity f = 1

end Numeric

/-! ### Closure under post-composition with an additive equivalence -/

section Closure
variable {V W W' : Type*} [AddGroup V] [AddGroup W] [AddGroup W'] [Fintype V]

lemma derivMap_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a x : V) :
    derivMap (σ ∘ f) a x = σ (derivMap f a x) := by
  unfold derivMap;
  simp +decide [ sub_eq_add_neg, map_add, map_neg ]

lemma fiberCard_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a : V) (b : W') :
    fiberCard (σ ∘ f) a b = fiberCard f a (σ.symm b) := by
  simp [fiberCard, derivMap_comp_addEquiv];
  simp +decide only [σ.eq_symm_apply]

/-
Differential uniformity is invariant under post-composition with an additive
equivalence.
-/
lemma differentialUniformity_comp_addEquiv (f : V → W) (σ : W ≃+ W') :
    differentialUniformity (σ ∘ f) = differentialUniformity f := by
  refine' le_antisymm _ _;
  · refine' diffUnif_le_iff _ _ |>.2 fun a ha b => _;
    convert fiberCard_le_diffUnif f ha ( σ.symm b ) using 1;
    convert fiberCard_comp_addEquiv f σ a b using 1;
  · refine' ( diffUnif_le_iff _ _ ).2 fun a ha b => _;
    convert fiberCard_le_diffUnif ( σ ∘ f ) ha ( σ b ) using 1;
    convert fiberCard_comp_addEquiv f σ a ( σ b ) |> Eq.symm using 1;
    rw [ σ.symm_apply_apply ]

theorem IsAPN.comp_addEquiv {f : V → W} (hf : IsAPN f) (σ : W ≃+ W') : IsAPN (σ ∘ f) := by
  unfold IsAPN at *; rw [differentialUniformity_comp_addEquiv]; exact hf

theorem IsPN.comp_addEquiv {f : V → W} (hf : IsPN f) (σ : W ≃+ W') : IsPN (σ ∘ f) := by
  unfold IsPN at *; rw [differentialUniformity_comp_addEquiv]; exact hf

end Closure

/-! ### Post-composition with a Frobenius power in characteristic two -/

section Frobenius
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

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

/-! ### Characteristic two -/

section CharTwo
variable {F : Type*} [Ring F] [Fintype F] [CharP F 2]

lemma derivMap_shift (f : F → F) (a x : F) : derivMap f a (x + a) = derivMap f a x := by
  convert sub_eq_sub_iff_add_eq_add.mpr _ using 1;
  simp +decide [ add_assoc, CharTwo.add_self_eq_zero ]

lemma ne_add_right {a : F} (x : F) (ha : a ≠ 0) : x ≠ x + a := by
  simp +decide [ ha ]

lemma two_le_diffUnif_charTwo [Nontrivial F] (f : F → F) :
    2 ≤ differentialUniformity f := by
  -- Fix a nonzero `a : F`.
  obtain ⟨a, ha⟩ : ∃ a : F, a ≠ 0 := exists_ne 0;
  -- The fibre subtype `{x // derivMap f a x = derivMap f a 0}` contains two distinct elements: `⟨0, rfl⟩` and `⟨a, h⟩`, where `h : derivMap f a a = derivMap f a 0` follows from `derivMap_shift f a 0` (since `0 + a = a`).
  have h_fibre_card : Nat.card {x : F | derivMap f a x = derivMap f a 0} ≥ 2 := by
    have h_sub : ∃ x y : F, x ≠ y ∧ derivMap f a x = derivMap f a 0 ∧ derivMap f a y = derivMap f a 0 := by
      -- By definition of `derivMap`, we have `derivMap f a (x + a) = derivMap f a x`.
      have h_deriv_shift : derivMap f a (0 + a) = derivMap f a 0 := derivMap_shift f a 0
      exact ⟨ 0, a, by aesop ⟩;
    obtain ⟨ x, y, hxy, hx, hy ⟩ := h_sub; exact le_trans ( by simp +decide [ hxy ] ) ( Set.ncard_le_ncard ( show { x, y } ⊆ { x | derivMap f a x = derivMap f a 0 } from by aesop_cat ) ) ;
  refine' le_trans _ ( fiberCard_le_diffUnif f ha ( derivMap f a 0 ) );
  exact h_fibre_card

/-
In characteristic two, uniformity `≤ 2` is the classical collision form
`y = x ∨ y = x + a`.
-/
lemma atMostTwoToOne_charTwo_collision (f : F → F) (h : differentialUniformity f ≤ 2) :
    ∀ a : F, a ≠ 0 → ∀ x y : F,
      f (x + a) - f x = f (y + a) - f y → y = x ∨ y = x + a := by
  intro a ha x y hxy;
  have hcollision : IsAtMostTwoToOne f := by
    exact isAtMostTwoToOne_iff_diffUnif_le_two f |>.2 h;
  have := hcollision a ha x y ( x + a ) ; simp_all +decide [ derivMap ] ;
  simp_all +decide [ add_assoc, sub_eq_iff_eq_add ];
  simp_all +decide [ ← add_assoc, CharTwo.add_self_eq_zero ];
  grind

end CharTwo

end APN