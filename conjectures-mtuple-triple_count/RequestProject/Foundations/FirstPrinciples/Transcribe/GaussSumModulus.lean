import Mathlib

/-!
# Transcription — Leaf L1, module 1: Gauss-sum modulus theory (Lidl–Niederreiter §5.2)

This is the **first rung** of the from-scratch transcription of the additive→
multiplicative character-sum bridge `GaussSumDecomp.kasami_crossCorr_eq_gaussInt`
(leaf **L1** in `FirstPrinciplesTranscriptionRoadmap.md`).

It packages the standard Gauss-sum modulus theory for a finite field, rooted
directly in Mathlib's `gaussSum` / `jacobiSum` API.  Everything here is a **real
proof** (no `sorry`): it merely re-exports and specializes Mathlib results to the
ℂ-valued finite-field setting that the Kasami bridge uses, fixing the canonical
primitive additive character once and for all.

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 5 (§5.2 Gauss sums; Thm 5.11
  `|g(χ)| = √q` for nontrivial `χ`; the Jacobi-sum relation
  `g(χ)g(φ) = J(χ,φ)·g(χφ)`).
* Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 8, 14.
* Mathlib: `Mathlib/NumberTheory/GaussSum.lean`, `Mathlib/NumberTheory/JacobiSum/Basic.lean`,
  `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- **The canonical primitive additive character** `ψ_F : F → ℂ`, obtained as the
trace composed with a primitive additive character of the prime field
(Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex`).  This is the additive
character `ψ` used throughout the Gauss-sum side of the Kasami bridge. -/
noncomputable def psiC (F : Type*) [Field F] [Fintype F] : AddChar F ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex F

/-- `psiC F` is primitive. -/
theorem psiC_isPrimitive : (psiC F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

/-- **Gauss-sum reflection / modulus (Lidl–Niederreiter Thm 5.11, card form).**
For a nontrivial multiplicative character `χ` and the primitive additive character
`ψ`, `g(χ,ψ)·g(χ⁻¹,ψ⁻¹) = #F`.  (This is `|g|² = q` once `g(χ⁻¹,ψ⁻¹)` is
identified with the complex conjugate of `g(χ,ψ)`.) -/
theorem gaussSum_mul_inv_eq_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    gaussSum χ (psiC F) * gaussSum χ⁻¹ (psiC F)⁻¹ = (Fintype.card F : ℂ) :=
  gaussSum_mul_gaussSum_eq_card hχ (psiC_isPrimitive)

/-- **Nonvanishing of the Gauss sum** of a nontrivial character (Lidl–Niederreiter
Thm 5.11 corollary). -/
theorem gaussSum_ne_zero {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    gaussSum χ (psiC F) ≠ 0 := by
  refine gaussSum_ne_zero_of_nontrivial ?_ hχ (psiC_isPrimitive)
  simp [Fintype.card_ne_zero]

/-- **The order-`n` reflection relation** `g(χ)·g(χ^{n-1}) = χ(-1)·#F` where
`n = ord χ` (Lidl–Niederreiter §5.2). -/
theorem gaussSum_mul_pow_orderOf_sub_one {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    gaussSum χ (psiC F) * gaussSum (χ ^ (orderOf χ - 1)) (psiC F)
      = χ (-1) * (Fintype.card F : ℂ) :=
  gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ (psiC_isPrimitive)

/-- **The Jacobi–Gauss relation (Lidl–Niederreiter §5.2 / Thm 5.21).**  For
`χ·φ ≠ 1`, `g(χφ)·J(χ,φ) = g(χ)·g(φ)`, hence (since `g(χφ) ≠ 0`) the Jacobi sum
factors the product of Gauss sums.  Stated in the product form, valid for any
additive character. -/
theorem gaussSum_mul_eq_jacobiSum_mul {χ φ : MulChar F ℂ} (h : χ * φ ≠ 1)
    (ψ : AddChar F ℂ) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ :=
  jacobiSum_mul_nontrivial h ψ

/-- **Gauss-sum power = product of Jacobi sums (Lidl–Niederreiter §5.2).**  For a
character `χ` of order `≥ 2`, `g(χ)^{ord χ} = χ(-1)·#F·∏ J(χ, χⁱ)`. -/
theorem gaussSum_pow_eq_jacobiSum_prod {χ : MulChar F ℂ} (hχ : 2 ≤ orderOf χ) :
    gaussSum χ (psiC F) ^ orderOf χ
      = χ (-1) * (Fintype.card F : ℂ)
        * ∏ i ∈ Finset.Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) :=
  gaussSum_pow_eq_prod_jacobiSum hχ (psiC_isPrimitive)

end Vanish.Foundations.FirstPrinciples.Transcribe
