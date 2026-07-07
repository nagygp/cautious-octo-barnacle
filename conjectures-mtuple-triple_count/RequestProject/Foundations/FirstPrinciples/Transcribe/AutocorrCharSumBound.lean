import RequestProject.MTuple.Count

/-!
# Transcription — a green bound atom for the corrected spectral rung

The disproof in `KasamiMonomialCollapseDisproof.lean` shows the Kasami
second-derivative sign-character sum `autocorrScaled f s a = ∑_x χ(s·Δf_a x)` is a
rational integer that is *not* a single monomial or single Gauss sum.  The correct
rung (`GaussSumBridge.kasami_autocorr_eq_gaussSum_sum`) expresses it as a **sum of
Gauss sums**.  Any spectral analysis of that integer starts from the elementary
`ℓ¹`/triangle bound recorded here as a real, `sorry`-free, axiom-clean atom:

* `autocorrScaled_abs_le` — `|autocorrScaled f s a| ≤ #F` (each of the `#F` summands
  is `±1`);
* `autocorrScaled_cast_abs_le` — the same bound after casting to `ℂ`.

These are rooted only in `WalshAB.χ_values` (`χ x ∈ {1, −1}`) and
`Finset.abs_sum_le_sum_abs`.

## Sources

* Project: `WalshAB.χ`, `WalshAB.χ_values`, `CollisionAnalysis.autocorrScaled`,
  `CollisionAnalysis.autocorrScaled_eq`.
* Mathlib: `Finset.abs_sum_le_sum_abs`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open Finset WalshAB CollisionAnalysis MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The `ℓ¹` bound on the Kasami cross-correlation.**  The second-derivative
sign-character sum `autocorrScaled f s a = ∑_x χ(s·Δf_a x)` is a sum of `#F` values
each equal to `±1`, so its absolute value is at most `#F`. -/
theorem autocorrScaled_abs_le (f : F → F) (s a : F) :
    |autocorrScaled f s a| ≤ (Fintype.card F : ℤ) := by
  rw [autocorrScaled_eq]
  calc |∑ x : F, χ (s * deriv f a x)|
        ≤ ∑ x : F, |χ (s * deriv f a x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _x : F, (1 : ℤ) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rcases χ_values (s * deriv f a x) with h | h <;> simp [h]
    _ = (Fintype.card F : ℤ) := by simp [Finset.card_univ]

/-- **The `ℓ¹` bound, cast to `ℂ`.**  `‖(autocorrScaled f s a : ℂ)‖ ≤ #F`.  This is
the modulus obstruction behind the single-Gauss-sum disproof: a nonzero Teichmüller
Gauss sum has modulus `√(#F)`, so a single such sum cannot realize the full range of
this integer. -/
theorem autocorrScaled_cast_abs_le (f : F → F) (s a : F) :
    ‖(autocorrScaled f s a : ℂ)‖ ≤ (Fintype.card F : ℝ) := by
  have h := autocorrScaled_abs_le f s a
  have hnorm : ‖(autocorrScaled f s a : ℂ)‖ = |(autocorrScaled f s a : ℝ)| := by
    rw [show ((autocorrScaled f s a : ℂ)) = (((autocorrScaled f s a : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have h' : |(autocorrScaled f s a : ℝ)| ≤ ((Fintype.card F : ℤ) : ℝ) := by
    exact_mod_cast h
  simpa using h'

end Vanish.Foundations.FirstPrinciples.Transcribe
