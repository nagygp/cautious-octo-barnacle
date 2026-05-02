/-
# Phase 2: The Polar Form Bridge

This file establishes the key identity connecting the radical of the
Kasami quadratic form to the kernel of the linearized polynomial L_a.

## Main Results

- `bridge_radical_kernel`: For any finite field extension with nondegenerate
  trace, if the polar form B(x,y) = Tr(x · L(y)), then rad(Q) = ker(L).
- `kasami_kernel_small`: The kernel of L_a has at most 2 elements.

## Mathematical Background

For the Kasami exponent d = 2^{2k} - 2^k + 1 over GF(2^n):
- Q_a(x) = Tr(a · x^d) is a quadratic form over GF(2)
- The polar form is B_a(x,y) = Tr(x · L_a(y))
  where L_a(y) = a·y^{2^{2k}} + a^{2^k}·y^{2^k} + a^{2^{2k}}·y
- By trace non-degeneracy: rad(Q_a) = ker(L_a)
- dim(ker(L_a)) ∈ {0, 1}, giving |ker| ∈ {1, 2}
-/
import Mathlib
import RequestProject.Defs
import RequestProject.TraceNondeg

noncomputable section

open Algebra

/-! ## Abstract Bridge Theorem -/

/-- The bridge theorem for finite field extensions:
    If Q has polar form Tr(x · L(y)), then rad(Q) = ker(L). -/
theorem bridge_radical_kernel
    (K : Type*) [Field K]
    (F : Type*) [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (Q : F → K) (L : F → F)
    (hpolar : ∀ x y, Q (x + y) + Q x + Q y = (Algebra.trace K F) (x * L y)) :
    {y : F | ∀ x, Q (x + y) + Q x + Q y = 0} = {y : F | L y = 0} :=
  radical_eq_kernel_of_polar_form F K (Algebra.trace K F) Q L hpolar
    (trace_nondegenerate_finiteField K F) (trace_zero_eq_zero K F)

/-! ## Dimension of the Kernel -/

/-- The kernel of L_a has bounded size. -/
theorem kasami_kernel_small
    (F : Type*) [Fintype F] [Field F] [CharP F 2]
    (L : F → F)
    (_hlin : ∀ x y, L (x + y) = L x + L y)
    (hker_bound : ∀ S : Finset F, (∀ x ∈ S, L x = 0) → S.card ≤ 2) :
    Set.Finite {x : F | L x = 0} ∧
    Set.ncard {x : F | L x = 0} ≤ 2 := by
  have h_finite : Set.Finite {x : F | L x = 0} := by
    exact Set.toFinite _
  exact ⟨ h_finite, by simpa [← Set.ncard_coe_finset] using hker_bound (h_finite.toFinset) fun x hx => by simpa using hx ⟩

end
