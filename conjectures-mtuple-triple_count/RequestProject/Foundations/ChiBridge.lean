import RequestProject.Foundations.AddCharCount
import RequestProject.MTuple.Count

/-!
# Foundations, Layer 2 — bridging the project's sign character to `AddChar`

Layer 1 (`AddCharCount.lean`) is deliberately *Mathlib-only*.  This layer is the
**bridge** that connects it to the existing Kasami development, whose Walsh
machinery uses a hand-rolled `ℤ`-valued sign character
`WalshAB.χ x = (-1)^{Tr x}` (`χ x = if Tr x = 0 then 1 else -1`).

The single insight is that, for a finite field `F` of characteristic two, this
`χ` is **already a genuine additive character** `AddChar F ℤ`: it sends `0 ↦ 1`
(`WalshAB.χ_zero`) and `x + y ↦ χ x · χ y` (`WalshAB.χ_mul`).  Packaging it as
`chiAddChar` lets us:

* obtain its **primitivity** for free (a nontrivial character of a field is
  primitive, `AddChar.IsPrimitive.of_ne_one`);
* re-derive the project's orthogonality `WalshAB.χ_sum_eq` from Mathlib's
  `AddChar.sum_mulShift`; and
* exhibit the project's Fourier-inversion identity `MTuple.card_mul_preCount` as
  a **specialization of the general pearl** `Vanish.Foundations.card_linear_tuple`
  (here `card_mul_preCount_via_foundation`).

This is the concrete demonstration that the hand-rolled character layer is an
*instance* of the general, upstreamable foundation — exactly the DRY refactoring
*The Art of Clean Code* recommends.
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The project's `ℤ`-valued sign character `χ`, packaged as a genuine additive
character `AddChar F ℤ`. -/
noncomputable def chiAddChar : AddChar F ℤ where
  toFun := χ
  map_zero_eq_one' := χ_zero
  map_add_eq_mul' := χ_mul

@[simp] theorem chiAddChar_apply (x : F) : (chiAddChar : AddChar F ℤ) x = χ x := rfl

/-- `chiAddChar` is nontrivial: the trace is surjective, so some `x` has
`Tr x ≠ 0`, hence `χ x = -1 ≠ 1`. -/
theorem chiAddChar_ne_one : (chiAddChar : AddChar F ℤ) ≠ 1 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have hval : (chiAddChar : AddChar F ℤ) y = (1 : AddChar F ℤ) y := by rw [h]
  rw [chiAddChar_apply, AddChar.one_apply] at hval
  simp only [χ, hy] at hval
  norm_num at hval

/-- A nontrivial additive character of a field is primitive. -/
theorem chiAddChar_primitive : (chiAddChar : AddChar F ℤ).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one chiAddChar_ne_one

/-- **Project orthogonality, re-derived from Mathlib.**  The project's
`WalshAB.χ_sum_eq` is the special case `ψ = chiAddChar` of
`AddChar.sum_mulShift`. -/
theorem chi_sum_eq_via_foundation (c : F) :
    ∑ x : F, χ (c * x) = if c = 0 then (Fintype.card F : ℤ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (chiAddChar : AddChar F ℤ)) c chiAddChar_primitive
  simp only [chiAddChar_apply] at h
  rw [show (∑ x : F, χ (c * x)) = ∑ x : F, χ (x * c) from
        Finset.sum_congr rfl (fun x _ => by rw [mul_comm]), h]
  push_cast
  rfl

/-- **The project's Fourier-inversion identity as a specialization of the
general pearl.**  `MTuple.card_mul_preCount` is exactly `card_linear_tuple` with
`ψ = chiAddChar`, index `Fin m`, and per-coordinate weight `w i = Δf_a`. -/
theorem card_mul_preCount_via_foundation (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) :
    (Fintype.card F : ℤ) * (MTuple.preCount m f a c : ℤ)
      = ∑ t : F, ∏ i : Fin m, autocorrScaled f (t * c i) a := by
  have h := card_linear_tuple (R' := ℤ) chiAddChar_primitive c (fun _ => MTuple.deriv f a)
  rw [MTuple.preCount]
  rw [h]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [MTuple.autocorrScaled_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [chiAddChar_apply, mul_assoc]

end Vanish.Foundations
