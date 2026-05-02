/-
# Walsh Spectrum Analysis

Formalization of Lemma 1 and the Corollary from:
  "Fourier Spectra of Binomial APN Functions"
  by C. Bracken, E. Byrne, N. Markin, G. McGuire (arXiv:0803.3781)

This file contains:
  - Lemma 1: The squared Walsh coefficient identity
  - The spectral link corollary: kernel dimension ≤ 1 implies AB
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open scoped BigOperators
open Finset Classical

variable {n : ℕ} [NeZero n]

attribute [local instance] Fintype.ofFinite

/-! ## Lemma 1: Squared Walsh Coefficient Identity

The paper states (Lemma 1):
  `W_f(a,b)² = 2^n · |{u ∈ F_{2^n} | D_u(g_b)(x) = 0 for all x}|`

where `g_b(x) = Tr(b·f(x))` and the inner sum expands via character orthogonality.

More precisely:
  `W_f(a,b)² = 2^n · ∑_u (-1)^{Tr(au)} · [∑_x (-1)^{Tr(b·(f(x+u) + f(x)))}]`

The key identity is:
  `W_f(a,b)² = ∑_u ∑_x (-1)^{Tr(au + b·D_u f(x))}`
-/

/-
The squared Walsh coefficient can be expressed as a double sum.

    `W_f(a,b)² = ∑_u ∑_x (-1)^{Tr(au)} · (-1)^{Tr(b · (f(x+u) + f(x)))}`

    This follows from expanding `W_f(a,b)² = W_f(a,b) · W_f(a,b)` and
    substituting `y = x + u`. (Lemma 1 of the paper.)
-/
theorem walsh_sq_eq_double_sum (f : GaloisField 2 n → GaloisField 2 n)
    (a b : GaloisField 2 n) :
    (walshTransform f a b) ^ 2 =
      ∑ u : GaloisField 2 n, ∑ x : GaloisField 2 n,
        chi (absTr n (a * u + b * (f (x + u) + f x))) := by
  rw [ sq, ← Finset.sum_comm ];
  rw [ ← Finset.sum_product' ];
  simp +decide [ walshTransform ];
  rw [ Finset.sum_mul_sum ];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( x.1, x.2 - x.1 ) ) _ _ _ _ <;> simp +decide [ chi_add, chi_absTr_add ];
  · aesop;
  · exact fun a b => ⟨ b + a, by ring ⟩;
  · intro x y; simp +decide [ mul_sub, mul_add, chi_absTr_add ] ; ring;
    simp +decide [ chi_add, chi_absTr_add, sub_eq_add_neg ] ; ring

/-
Reformulation using the derivative operator.
-/
theorem walsh_sq_eq_derivative_sum (f : GaloisField 2 n → GaloisField 2 n)
    (a b : GaloisField 2 n) :
    (walshTransform f a b) ^ 2 =
      ∑ u : GaloisField 2 n, ∑ x : GaloisField 2 n,
        chi (absTr n (a * u + b * derivative f u x)) := by
  exact walsh_sq_eq_double_sum f a b

/-! ## Inner sum analysis

For fixed `u` and `b`, the inner sum `∑_x (-1)^{Tr(b · D_u f(x))}` counts
solutions. By character orthogonality:
  - If `x ↦ b · D_u f(x)` is balanced (i.e., `Tr(b · D_u f(·))` takes values
    0 and 1 equally often), the sum is 0.
  - If it is constant 0 (i.e., `b · D_u f(x) ∈ ker(Tr)` for all `x`), the sum is `2^n`.
-/

/-- Inner sum for the Walsh squared identity: for a fixed `u`,
    `∑_x (-1)^{Tr(b · D_u f(x))} = 2^n` if `Tr(b · D_u f(x)) = 0` for all `x`,
    and the sum relates to the kernel of the map `x ↦ Tr(b · D_u f(x))` in general. -/
lemma inner_sum_kernel (f : GaloisField 2 n → GaloisField 2 n)
    (b u : GaloisField 2 n)
    (h : ∀ x : GaloisField 2 n, absTr n (b * derivative f u x) = 0) :
    ∑ x : GaloisField 2 n, chi (absTr n (b * derivative f u x)) =
      (Nat.card (GaloisField 2 n) : ℤ) := by
  simp only [h, chi_zero]
  simp [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-! ## Corollary: Kernel Dimension Bound implies AB

The paper observes that for quadratic functions `f`, the linearized derivative
`Δ_u f(x) = f(x+u) + f(x) + f(u)` is `F_2`-linear in `x`.

If `dim(ker(Δ_u f)) ≤ 1` for all nonzero `u`, then for each `(a,b)` with `b ≠ 0`:
  `W_f(a,b)² ∈ {0, 2^{n+1}}`

Since `W_f(a,b)` is always an integer (sum of ±1), this forces
  `W_f(a,b) ∈ {0, ±2^{(n+1)/2}}`
when `n` is odd, which is exactly the AB condition.
-/

/-- The kernel of the linearized derivative. -/
def linDerivKer (f : GaloisField 2 n → GaloisField 2 n) (u : GaloisField 2 n) :
    Set (GaloisField 2 n) :=
  {x : GaloisField 2 n | linDerivative f u x = 0}

/-- **Corollary (Spectral Link):** If for every nonzero `u`, the linearized
    derivative `Δ_u f` has kernel of dimension at most 1 over `F_2`, then `f`
    is Almost Bent (assuming `n` is odd).

    This is the key structural result connecting the algebraic property (small kernel)
    to the spectral property (three-valued Walsh spectrum). -/
theorem kernel_dim_le_one_implies_AB
    (f : GaloisField 2 n → GaloisField 2 n)
    (hodd : n % 2 = 1)
    (hker : ∀ u : GaloisField 2 n, u ≠ 0 →
      Nat.card (linDerivKer f u) ≤ 2) :
    IsAB f := by
  sorry

end