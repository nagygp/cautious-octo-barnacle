import CodeTheoryCryptoEquiv.CodingTheory.LinearCode

/-!
# Dual codes: the orthogonal code and complementary dimensions

This module continues the coding-theory development of
`CodeTheoryCryptoEquiv/CodingTheory/LinearCode.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

Following the roadmap in `CODING_THEORY_DIRECTIONS.md`, the dual code is the
recommended immediate next step after the Singleton bound: it is the gateway to
parity-check matrices, the MacWilliams identity, and self-dual codes.

We keep the conventions of the foundational module: a word lives in `ι → F` with
`[Fintype ι] [Field F]`, and a linear `[n, k]` code is a subspace
`C : Submodule F (ι → F)` of length `n = #ι` (`codeLength`) and dimension
`k = dim C` (`codeDim`).

## The construction

The dual code `Cᗮ` is the orthogonal complement of `C` with respect to the
*standard dot-product form* `⟪x, y⟫ = ∑ i, x i * y i` on `ι → F` (the book's
inner product on `F^n`).  We reuse Mathlib's general orthogonal-complement theory
for a bilinear form (`Mathlib.LinearAlgebra.BilinearForm.Orthogonal`); the two
inputs it needs — symmetry and nondegeneracy of the dot-product form — are the
upstreamable lemmas in `CodeTheoryCryptoEquiv/Upstream/Dual.lean`.

## Main results

* `mem_dualCode_iff` — `y ∈ Cᗮ ↔ ∀ x ∈ C, ∑ i, x i * y i = 0` (the parity-check
  description).
* `codeDim_add_codeDim_dualCode` — `dim C + dim Cᗮ = n` (MacWilliams–Sloane,
  Ch. 1, §8: a code and its dual have complementary dimensions).
* `codeDim_dualCode` — `dim Cᗮ = n - dim C`.
* `dualCode_dualCode` — `Cᗮᗮ = C` (the dual is an involution).
* `dualCode_bot` / `dualCode_top` — the dual of the zero/full code.
* `dualCode_antitone` — taking duals reverses inclusions.
* `IsSelfDual.two_mul_codeDim` — a self-dual code has `2 · dim C = n`.

## References

* MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 1, §8.
-/

namespace CodingTheory

open scoped Classical

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- The standard dot-product bilinear form `⟪x, y⟫ = ∑ i, x i * y i` on the word
space `ι → F`, used to define orthogonality of codewords. -/
noncomputable def dualBilinForm (ι F : Type*) [Fintype ι] [Field F] :
    LinearMap.BilinForm F (ι → F) :=
  dotProductBilin F F

theorem dualBilinForm_apply (x y : ι → F) : dualBilinForm ι F x y = ∑ i, x i * y i := rfl

/-- The standard dot-product form is symmetric. -/
theorem dualBilinForm_isSymm : (dualBilinForm ι F).IsSymm :=
  ⟨fun x y => by simpa only [RingHom.id_apply, dualBilinForm_apply] using dotProduct_comm x y⟩

/-- The standard dot-product form is reflexive. -/
theorem dualBilinForm_isRefl : (dualBilinForm ι F).IsRefl := dualBilinForm_isSymm.isRefl

/-- The standard dot-product form is nondegenerate over a field. -/
theorem dualBilinForm_nondegenerate : (dualBilinForm ι F).Nondegenerate :=
  ⟨fun x hx => dotProduct_eq_zero x hx,
    fun y hy => dotProduct_eq_zero y fun w => by rw [dotProduct_comm]; exact hy w⟩

/-- The **dual code** `Cᗮ` of a linear code `C ⊆ ι → F`: the words orthogonal to
every codeword with respect to the standard dot-product form.  Equivalently, the
solutions of all parity-check equations given by codewords of `C`. -/
noncomputable def dualCode (C : Submodule F (ι → F)) : Submodule F (ι → F) :=
  LinearMap.BilinForm.orthogonal (dualBilinForm ι F) C

/-- A word lies in the dual code iff it satisfies every parity-check equation
`∑ i, x i * y i = 0` coming from a codeword `x ∈ C`. -/
theorem mem_dualCode_iff {C : Submodule F (ι → F)} {y : ι → F} :
    y ∈ dualCode C ↔ ∀ x ∈ C, ∑ i, x i * y i = 0 := by
  unfold dualCode
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun x _ => ?_
  rw [LinearMap.BilinForm.isOrtho_def, dualBilinForm_apply]

/-- **MacWilliams–Sloane, Ch. 1, §8: complementary dimensions.** A code and its
dual have dimensions summing to the length: `dim C + dim Cᗮ = n`. -/
theorem codeDim_add_codeDim_dualCode (C : Submodule F (ι → F)) :
    codeDim C + codeDim (dualCode C) = codeLength C := by
  have h := LinearMap.BilinForm.finrank_orthogonal (B := dualBilinForm ι F)
    dualBilinForm_nondegenerate dualBilinForm_isRefl C
  have hle : Module.finrank F C ≤ Module.finrank F (ι → F) := Submodule.finrank_le C
  simp only [codeDim, codeLength, dualCode]
  rw [h]
  simp only [Module.finrank_pi] at *
  omega

/-- The dimension of the dual code: `dim Cᗮ = n - dim C`. -/
theorem codeDim_dualCode (C : Submodule F (ι → F)) :
    codeDim (dualCode C) = codeLength C - codeDim C := by
  have := codeDim_add_codeDim_dualCode C; omega

/-- **The dual is an involution**: `Cᗮᗮ = C`. -/
@[simp] theorem dualCode_dualCode (C : Submodule F (ι → F)) :
    dualCode (dualCode C) = C :=
  LinearMap.BilinForm.orthogonal_orthogonal (B := dualBilinForm ι F)
    dualBilinForm_nondegenerate dualBilinForm_isRefl C

/-- Taking duals reverses inclusions. -/
theorem dualCode_antitone {C D : Submodule F (ι → F)} (h : C ≤ D) :
    dualCode D ≤ dualCode C :=
  LinearMap.BilinForm.orthogonal_le (B := dualBilinForm ι F) h

/-- The dual of the zero code is the whole space. -/
@[simp] theorem dualCode_bot : dualCode (⊥ : Submodule F (ι → F)) = ⊤ := by
  ext y; simp only [mem_dualCode_iff, Submodule.mem_bot, Submodule.mem_top, iff_true]
  rintro x rfl; simp

/-- The dual of the whole space is the zero code. -/
@[simp] theorem dualCode_top : dualCode (⊤ : Submodule F (ι → F)) = ⊥ := by
  have := dualCode_dualCode (⊥ : Submodule F (ι → F)); rwa [dualCode_bot] at this

/-- A code is **self-orthogonal** if it is contained in its dual. -/
def IsSelfOrthogonal (C : Submodule F (ι → F)) : Prop := C ≤ dualCode C

/-- A code is **self-dual** if it equals its dual. -/
def IsSelfDual (C : Submodule F (ι → F)) : Prop := dualCode C = C

/-- A self-dual code is self-orthogonal. -/
theorem IsSelfDual.isSelfOrthogonal {C : Submodule F (ι → F)} (h : IsSelfDual C) :
    IsSelfOrthogonal C := h.ge

/-- A self-dual code has dimension exactly half the length: `2 · dim C = n`. -/
theorem IsSelfDual.two_mul_codeDim {C : Submodule F (ι → F)} (h : IsSelfDual C) :
    2 * codeDim C = codeLength C := by
  have hd := codeDim_add_codeDim_dualCode C
  rw [IsSelfDual] at h; rw [h] at hd; omega

end CodingTheory
