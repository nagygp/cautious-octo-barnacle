/-
# Quadratic Forms over F₂-Vector Spaces

This file develops the theory of quadratic forms on finite F₂-vector spaces,
focused on the characteristic-2 setting relevant to Kasami codes and
the quadratic form → Gauss sum connection.

## Main Definitions

- `QuadFormF2`: A quadratic form Q : V → ZMod 2 on an F₂-vector space V
- `QuadFormF2.polar`: The associated symplectic bilinear form B(x,y) = Q(x+y) + Q(x) + Q(y)
- `QuadFormF2.radical`: The radical of the associated bilinear form
- `QuadFormF2.radicalRestriction`: Q restricted to the radical as a linear map

## Main Results

- `QuadFormF2.polar_self`: B(x,x) = 0 (alternating / symplectic)
- `QuadFormF2.polar_add_left/right`: B is bilinear
- `QuadFormF2.additive_on_radical`: Q(x + w) = Q(x) + Q(w) for w ∈ rad(B)
- `QuadFormF2.radicalRestriction`: Q|_rad is F₂-linear
-/

import Mathlib

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Characteristic 2 module lemmas -/
section Char2Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

lemma ZMod2.add_self (x : V) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = (2 : ZMod 2) • x := (two_smul (ZMod 2) x).symm
    _ = (0 : ZMod 2) • x := by rw [h2]
    _ = 0 := zero_smul _ _

lemma ZMod2.neg_eq (x : V) : -x = x := by
  have h : x + x = 0 := ZMod2.add_self x
  have : -x = -x + (x + x) := by rw [h, add_zero]
  rw [this, ← add_assoc, neg_add_cancel, zero_add]

lemma ZMod2.sub_eq_add (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, ZMod2.neg_eq]

end Char2Module

/-! ## Quadratic Form Structure -/

/-- A quadratic form over F₂ on a type V.
    Q : V → ZMod 2 satisfying:
    (1) Q(0) = 0
    (2) The polar form B(x,y) = Q(x+y) + Q(x) + Q(y) is biadditive -/
structure QuadFormF2 (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  /-- The underlying function -/
  toFun : V → ZMod 2
  /-- Q vanishes at zero -/
  map_zero' : toFun 0 = 0
  /-- The polar form B(x,y) = Q(x+y)+Q(x)+Q(y) is additive in the first variable.
      Concretely: B(x₁+x₂, y) = B(x₁, y) + B(x₂, y), which after expanding becomes
      Q(x₁+x₂+y) + Q(x₁+x₂) + Q(y) = Q(x₁+y) + Q(x₁) + Q(x₂+y) + Q(x₂) -/
  polar_add_left' : ∀ (x₁ x₂ y : V),
    toFun (x₁ + x₂ + y) + toFun (x₁ + x₂) + toFun y =
    toFun (x₁ + y) + toFun x₁ + (toFun (x₂ + y) + toFun x₂)

namespace QuadFormF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

instance : FunLike (QuadFormF2 V) V (ZMod 2) where
  coe := QuadFormF2.toFun
  coe_injective' := by intro Q₁ Q₂ h; cases Q₁; cases Q₂; congr

@[simp] lemma coe_toFun (Q : QuadFormF2 V) : Q.toFun = Q := rfl

@[simp] lemma map_zero (Q : QuadFormF2 V) : Q 0 = 0 := Q.map_zero'

/-! ## Polar / Bilinear Form -/

/-- The polar/associated bilinear form: B(x,y) = Q(x+y) + Q(x) + Q(y).
    In characteristic 2, this is symmetric and alternating (symplectic). -/
def polar (Q : QuadFormF2 V) (x y : V) : ZMod 2 :=
  Q (x + y) + Q x + Q y

/-- The polar form is alternating: B(x,x) = 0.
    Uses x + x = 0 in characteristic 2. -/
@[simp]
lemma polar_self (Q : QuadFormF2 V) (x : V) :
    Q.polar x x = 0 := by
  simp only [polar, ZMod2.add_self x, Q.map_zero, zero_add]
  exact CharTwo.add_self_eq_zero (Q x)

/-
The polar form is additive in the first argument:
    B(x₁ + x₂, y) = B(x₁, y) + B(x₂, y)
-/
lemma polar_add_left (Q : QuadFormF2 V) (x₁ x₂ y : V) :
    Q.polar (x₁ + x₂) y = Q.polar x₁ y + Q.polar x₂ y := by
  simp only [polar]
  -- Need: Q((x₁+x₂)+y) + Q(x₁+x₂) + Q(y) = (Q(x₁+y)+Q(x₁)+Q(y)) + (Q(x₂+y)+Q(x₂)+Q(y))
  -- RHS = Q(x₁+y)+Q(x₁)+Q(x₂+y)+Q(x₂) + Q(y)+Q(y)  [after rearranging]
  -- = Q(x₁+y)+Q(x₁)+Q(x₂+y)+Q(x₂) [since Q(y)+Q(y)=0]
  -- = Q(x₁+x₂+y)+Q(x₁+x₂)+Q(y)  [by polar_add_left']
  -- Apply the polar_add_left' axiom to rewrite the left-hand side.
  have h_lhs : Q (x₁ + x₂ + y) + Q (x₁ + x₂) + Q y = Q (x₁ + y) + Q x₁ + (Q (x₂ + y) + Q x₂) := by
    exact Q.polar_add_left' x₁ x₂ y;
  grind

/-- The polar form is symmetric: B(x,y) = B(y,x) -/
lemma polar_comm (Q : QuadFormF2 V) (x y : V) :
    Q.polar x y = Q.polar y x := by
  simp only [polar, add_comm x y, add_comm (Q (y + x))]
  ring

/-- The polar form is additive in the second argument -/
lemma polar_add_right (Q : QuadFormF2 V) (x y₁ y₂ : V) :
    Q.polar x (y₁ + y₂) = Q.polar x y₁ + Q.polar x y₂ := by
  rw [polar_comm, polar_add_left, polar_comm Q y₁, polar_comm Q y₂]

@[simp]
lemma polar_zero_left (Q : QuadFormF2 V) (y : V) :
    Q.polar 0 y = 0 := by
  have h := Q.polar_add_left 0 0 y
  simp [ZMod2.add_self] at h
  exact h

@[simp]
lemma polar_zero_right (Q : QuadFormF2 V) (x : V) :
    Q.polar x 0 = 0 := by
  rw [polar_comm, polar_zero_left]

/-- The polar form respects scalar multiplication -/
lemma polar_smul_left (Q : QuadFormF2 V) (c : ZMod 2) (x y : V) :
    Q.polar (c • x) y = c * Q.polar x y := by
  fin_cases c <;> simp [zero_smul, one_smul]

lemma polar_smul_right (Q : QuadFormF2 V) (c : ZMod 2) (x y : V) :
    Q.polar x (c • y) = c * Q.polar x y := by
  rw [polar_comm, polar_smul_left, polar_comm]

/-! ## Radical -/

/-- The radical of Q is the kernel of the associated bilinear form:
    rad(Q) = {x : V | ∀ y, B(x,y) = 0} -/
def radical (Q : QuadFormF2 V) : Submodule (ZMod 2) V where
  carrier := {x : V | ∀ y : V, Q.polar x y = 0}
  add_mem' := by
    intro a b ha hb y
    rw [polar_add_left, ha, hb, add_zero]
  zero_mem' := by
    intro y; exact polar_zero_left Q y
  smul_mem' := by
    intro c x hx y
    rw [polar_smul_left, hx, mul_zero]

lemma mem_radical (Q : QuadFormF2 V) (x : V) :
    x ∈ Q.radical ↔ ∀ y : V, Q.polar x y = 0 :=
  Iff.rfl

/-! ## Q is additive on the radical -/

/-
Q(x + w) = Q(x) + Q(w) when w ∈ rad(Q).
    This follows because B(x,w) = Q(x+w) + Q(x) + Q(w) = 0.
-/
lemma additive_on_radical (Q : QuadFormF2 V) {w : V} (hw : w ∈ Q.radical) (x : V) :
    Q (x + w) = Q x + Q w := by
  have h : Q.polar x w = 0 := by rw [polar_comm]; exact hw x
  -- polar x w = Q(x+w) + Q(x) + Q(w) = 0
  -- So Q(x+w) = Q(x) + Q(w) (in ZMod 2, a+b+c=0 ↔ a=b+c)
  simp only [polar] at h
  grind +qlia

/-- Q is additive when both arguments are in the radical -/
lemma additive_radical_radical (Q : QuadFormF2 V) {w₁ w₂ : V}
    (_hw₁ : w₁ ∈ Q.radical) (hw₂ : w₂ ∈ Q.radical) :
    Q (w₁ + w₂) = Q w₁ + Q w₂ :=
  additive_on_radical Q hw₂ w₁

/-- The restriction of Q to the radical is a linear map to ZMod 2. -/
def radicalRestriction (Q : QuadFormF2 V) : Q.radical →ₗ[ZMod 2] ZMod 2 where
  toFun w := Q w.val
  map_add' := by
    intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
    exact additive_radical_radical Q hw₁ hw₂
  map_smul' := by
    intro c ⟨w, _⟩
    simp only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul]
    fin_cases c <;> simp [zero_smul, one_smul, map_zero]

/-- Q vanishes identically on the radical iff the radical restriction is zero -/
lemma radical_vanishing_iff (Q : QuadFormF2 V) :
    (∀ w ∈ Q.radical, Q w = 0) ↔ Q.radicalRestriction = 0 := by
  constructor
  · intro h
    ext ⟨w, hw⟩
    simp [radicalRestriction, h w hw]
  · intro h w hw
    have := LinearMap.ext_iff.mp h ⟨w, hw⟩
    simpa [radicalRestriction] using this

end QuadFormF2