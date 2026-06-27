/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import CodeTheoryCryptoEquiv.Upstream.LinearCode

/-!
# Dual codes and the standard dot-product bilinear form

> Intended Mathlib target paths:
> * the `dotProductBilin` lemmas below extend
>   `Mathlib/LinearAlgebra/Matrix/DotProduct.lean`;
> * the `LinearCode.dual` API extends the linear-code file
>   (`Mathlib/InformationTheory/LinearCode.lean`, cf. `Upstream/LinearCode.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in via
> `Upstream.LinearCode` should be minimised (e.g. with `shake`).

This file develops the **dual** (or **orthogonal**) code, the gateway to most of
the structural theory of linear codes (parity checks, the MacWilliams identity,
self-dual codes, …), on top of Mathlib's general theory of orthogonal complements
for a bilinear form (`Mathlib.LinearAlgebra.BilinearForm.Orthogonal`).

## The reusable kernel

The dual code is the orthogonal complement of `C` with respect to the *standard
dot-product form* `⟪x, y⟫ = ∑ i, x i * y i` on `ι → F`, which Mathlib already
packages as `dotProductBilin`.  The two facts that make the whole theory work are
genuinely general statements about that form and are stated here for an arbitrary
submodule (not just a code):

* `dotProductBilin_isSymm` — the dot-product form is symmetric;
* `dotProductBilin_nondegenerate` — over a field and a finite index type it is
  nondegenerate.

These feed the standard orthogonal-complement lemmas to give, for any submodule
`W ⊆ ι → F`, the rank identity `finrank W + finrank Wᗮ = #ι` and the involutivity
`Wᗮᗮ = W`.

## Main definitions

* `LinearCode.dual C` — the dual code `Cᗮ = {y | ∀ x ∈ C, ∑ i, x i * y i = 0}`.
* `LinearCode.IsSelfOrthogonal` / `LinearCode.IsSelfDual` — `C ⊆ Cᗮ`, resp.
  `C = Cᗮ`.

## Main results

* `LinearCode.mem_dual_iff` — membership unfolded to the parity-check equations.
* `LinearCode.dim_add_dim_dual` — `dim C + dim Cᗮ = n` (MacWilliams–Sloane,
  Ch. 1, §8: a code and its dual have complementary dimensions).
* `LinearCode.dim_dual` — `dim Cᗮ = n - dim C`.
* `LinearCode.dual_dual` — `Cᗮᗮ = C` (the dual is an involution).
* `LinearCode.dual_bot` / `LinearCode.dual_top` — the dual of the zero/full code.
* `LinearCode.dual_antitone` — taking duals reverses inclusions.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 1, §8.)

## Tags

linear code, dual code, orthogonal code, parity check, bilinear form, dot product,
self-dual code
-/

open scoped Classical

namespace Matrix

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The standard dot-product bilinear form evaluates to the dot product
`∑ i, x i * y i`. -/
theorem dotProductBilin_apply (x y : ι → F) :
    (dotProductBilin F F : LinearMap.BilinForm F (ι → F)) x y = ∑ i, x i * y i := rfl

/-- The standard dot-product bilinear form `⟪x, y⟫ = ∑ i, x i * y i` is symmetric.
-/
theorem dotProductBilin_isSymm :
    (dotProductBilin F F : LinearMap.BilinForm F (ι → F)).IsSymm :=
  ⟨fun x y => by
    simpa only [RingHom.id_apply] using dotProduct_comm x y⟩

/-- Over a field and a finite index type the standard dot-product bilinear form is
nondegenerate: a vector orthogonal to everything is zero. -/
theorem dotProductBilin_nondegenerate :
    (dotProductBilin F F : LinearMap.BilinForm F (ι → F)).Nondegenerate :=
  ⟨fun x hx => dotProduct_eq_zero x hx,
    fun y hy => dotProduct_eq_zero y fun w => by rw [dotProduct_comm]; exact hy w⟩

/-- The standard dot-product bilinear form is reflexive. -/
theorem dotProductBilin_isRefl :
    (dotProductBilin F F : LinearMap.BilinForm F (ι → F)).IsRefl :=
  dotProductBilin_isSymm.isRefl

end Matrix

namespace LinearCode

open Matrix

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The **dual code** (or **orthogonal code**) `Cᗮ` of a linear code `C ⊆ ι → F`:
the words orthogonal to every codeword with respect to the standard dot-product
form.  Equivalently, the kernel of every parity check given by a codeword. -/
def dual (C : LinearCode ι F) : LinearCode ι F :=
  LinearMap.BilinForm.orthogonal (dotProductBilin F F : LinearMap.BilinForm F (ι → F)) C

@[inherit_doc] scoped postfix:max "ᗮᶜ" => LinearCode.dual

/-- A word lies in the dual code iff it satisfies every parity-check equation
`∑ i, x i * y i = 0` coming from a codeword `x ∈ C`. -/
theorem mem_dual_iff {C : LinearCode ι F} {y : ι → F} :
    y ∈ dual C ↔ ∀ x ∈ C, ∑ i, x i * y i = 0 := by
  unfold dual
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun x _ => ?_
  rw [LinearMap.BilinForm.isOrtho_def, dotProductBilin_apply]

/-- **Complementary dimensions** (MacWilliams–Sloane, Ch. 1, §8). A code and its
dual have dimensions summing to the length: `dim C + dim Cᗮ = n`. -/
theorem dim_add_dim_dual (C : LinearCode ι F) :
    C.dim + (dual C).dim = C.length := by
  have h := LinearMap.BilinForm.finrank_orthogonal
    (B := (dotProductBilin F F : LinearMap.BilinForm F (ι → F)))
    dotProductBilin_nondegenerate dotProductBilin_isRefl C
  have hle : Module.finrank F C ≤ Module.finrank F (ι → F) := Submodule.finrank_le C
  simp only [dim, length_eq_card, dual]
  rw [h]
  simp only [Module.finrank_pi] at *
  omega

/-- The dimension of the dual code: `dim Cᗮ = n - dim C`. -/
theorem dim_dual (C : LinearCode ι F) : (dual C).dim = C.length - C.dim := by
  have := dim_add_dim_dual C; omega

/-- **The dual is an involution**: `Cᗮᗮ = C`. -/
@[simp] theorem dual_dual (C : LinearCode ι F) : dual (dual C) = C :=
  LinearMap.BilinForm.orthogonal_orthogonal
    (B := (dotProductBilin F F : LinearMap.BilinForm F (ι → F)))
    dotProductBilin_nondegenerate dotProductBilin_isRefl C

/-- Taking duals reverses inclusions. -/
theorem dual_antitone {C D : LinearCode ι F} (h : C ≤ D) : dual D ≤ dual C :=
  LinearMap.BilinForm.orthogonal_le
    (B := (dotProductBilin F F : LinearMap.BilinForm F (ι → F))) h

/-- The dual of the zero code is the whole space. -/
@[simp] theorem dual_bot : dual (⊥ : LinearCode ι F) = ⊤ := by
  ext y; simp only [mem_dual_iff, Submodule.mem_bot, Submodule.mem_top, iff_true]
  rintro x rfl; simp

/-- The dual of the whole space is the zero code. -/
@[simp] theorem dual_top : dual (⊤ : LinearCode ι F) = ⊥ := by
  have := dual_dual (⊥ : LinearCode ι F); rwa [dual_bot] at this

/-- A code is **self-orthogonal** if it is contained in its dual. -/
def IsSelfOrthogonal (C : LinearCode ι F) : Prop := C ≤ dual C

/-- A code is **self-dual** if it equals its dual. -/
def IsSelfDual (C : LinearCode ι F) : Prop := dual C = C

/-- A self-dual code is self-orthogonal. -/
theorem IsSelfDual.isSelfOrthogonal {C : LinearCode ι F} (h : IsSelfDual C) :
    IsSelfOrthogonal C := h.ge

/-- A self-dual code has dimension exactly half the length: `2 * dim C = n`. -/
theorem IsSelfDual.two_mul_dim {C : LinearCode ι F} (h : IsSelfDual C) :
    2 * C.dim = C.length := by
  have hd := dim_add_dim_dual C
  rw [IsSelfDual] at h
  rw [h] at hd; omega

end LinearCode
