import Mathlib

/-!
# Differential uniformity and APN / PN functions (skeleton / `sorry` version)

This is a statement-only skeleton twin of
`RequestProject/DiffUniformity/DifferentialUniformityUpstream.lean`: it contains
exactly the same generalized definitions and lemma/theorem **statements**, but
every proof is left as `sorry`.  It is intended as a clean starting point for
re-deriving the proofs (e.g. when adapting the material for upstreaming).

See the companion file for the fully proved versions.

The **differential uniformity** of a function `f` between additive groups is the
maximum fibre size of its derivative maps `x ↦ f (x + a) - f x` over all `a ≠ 0`.
It is characteristic-free: `IsAPN f` means it equals `2`, `IsPN f` (planar) means
it equals `1`.
-/

open Finset

namespace APNSkeleton

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
  sorry

lemma fiberCard_le_diffUnif (f : V → W) {a : V} (ha : a ≠ 0) (b : W) :
    fiberCard f a b ≤ differentialUniformity f := by
  sorry

lemma isAtMostTwoToOne_iff_diffUnif_le_two (f : V → W) :
    IsAtMostTwoToOne f ↔ differentialUniformity f ≤ 2 := by
  sorry

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
  sorry

lemma fiberCard_comp_addEquiv (f : V → W) (σ : W ≃+ W') (a : V) (b : W') :
    fiberCard (σ ∘ f) a b = fiberCard f a (σ.symm b) := by
  sorry

/-- Differential uniformity is invariant under post-composition with an additive
equivalence. -/
lemma differentialUniformity_comp_addEquiv (f : V → W) (σ : W ≃+ W') :
    differentialUniformity (σ ∘ f) = differentialUniformity f := by
  sorry

theorem IsAPN.comp_addEquiv {f : V → W} (hf : IsAPN f) (σ : W ≃+ W') : IsAPN (σ ∘ f) := by
  sorry

theorem IsPN.comp_addEquiv {f : V → W} (hf : IsPN f) (σ : W ≃+ W') : IsPN (σ ∘ f) := by
  sorry

end Closure

/-! ### Post-composition with a Frobenius power in characteristic two -/

section Frobenius
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Over a finite field of characteristic two, post-composing an APN function with the
Frobenius power map `x ↦ x ^ (2 ^ j)` is again APN. -/
theorem IsAPN.comp_frobenius {f : F → F} (hf : IsAPN f) (j : ℕ) :
    IsAPN (fun x => (f x) ^ (2 ^ j)) := by
  sorry

end Frobenius

/-! ### Characteristic two -/

section CharTwo
variable {F : Type*} [Ring F] [Fintype F] [CharP F 2]

lemma derivMap_shift (f : F → F) (a x : F) : derivMap f a (x + a) = derivMap f a x := by
  sorry

lemma ne_add_right {a : F} (x : F) (ha : a ≠ 0) : x ≠ x + a := by
  sorry

lemma two_le_diffUnif_charTwo [Nontrivial F] (f : F → F) :
    2 ≤ differentialUniformity f := by
  sorry

/-- In characteristic two, uniformity `≤ 2` is the classical collision form
`y = x ∨ y = x + a`. -/
lemma atMostTwoToOne_charTwo_collision (f : F → F) (h : differentialUniformity f ≤ 2) :
    ∀ a : F, a ≠ 0 → ∀ x y : F,
      f (x + a) - f x = f (y + a) - f y → y = x ∨ y = x + a := by
  sorry

end CharTwo

end APNSkeleton
