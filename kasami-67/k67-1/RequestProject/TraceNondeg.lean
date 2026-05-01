/-
# Trace Non-Degeneracy for Finite Field Extensions

The field trace Tr : GF(2^n) → GF(2) is nondegenerate:
  ∀ z ∈ GF(2^n), (∀ x, Tr(x·z) = 0) → z = 0

This is a standard result that follows from the fact that the trace form
is a nondegenerate bilinear form on any separable field extension.
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open Algebra

/-! ## Trace surjectivity and non-degeneracy -/

/-- The algebra trace Tr : GF(2^n) → GF(2) is surjective.
    This is a special case of `Algebra.trace_surjective`. -/
lemma trace_surjective_GF2 (n : ℕ) [NeZero n] :
    Function.Surjective (Algebra.trace (ZMod 2) (GaloisField 2 n)) :=
  Algebra.trace_surjective (ZMod 2) (GaloisField 2 n)

/-
Non-degeneracy of the trace bilinear form on finite fields:
    if Tr(x·z) = 0 for all x, then z = 0.
    This follows from trace_ne_zero / trace_surjective.
-/
theorem trace_nondegenerate_finiteField
    (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    TraceNondegenerate L K (Algebra.trace K L) := by
  intro z hz;
  contrapose! hz;
  obtain ⟨x, hx⟩ : ∃ x : L, (Algebra.trace K L) x ≠ 0 := by
    exact ( Algebra.trace_surjective K L ) ( 1 : K ) |> fun ⟨ x, hx ⟩ => ⟨ x, hx.symm ▸ one_ne_zero ⟩;
  exact ⟨ x / z, by simpa [ div_mul_cancel₀ _ hz ] using hx ⟩

/-- The trace applied to 0 is 0 (it's a linear map). -/
theorem trace_zero_eq_zero
    (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] [FiniteDimensional K L] :
    (Algebra.trace K L) 0 = 0 :=
  map_zero _

end