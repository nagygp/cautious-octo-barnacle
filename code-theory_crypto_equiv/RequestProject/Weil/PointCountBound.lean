import RequestProject.Weil.Stepanov

/-!
# The two-sided point-count bound for the Artin–Schreier curve

This module packages the two one-sided Stepanov bounds (`curvePointCount_le` and
`curvePointCount_ge`) into the single two-sided estimate
$$ \bigl| \#C_f(\mathbb F_q) - q \bigr| \;\le\; (d-1)(p-1)\,\sqrt q \;=\; 2g\,\sqrt q, $$
the Weil bound for point counts of the Artin–Schreier curve, with genus
`g = (d-1)(p-1)/2`.

This is a soft consequence of the two one-sided bounds via `abs_le`; it is a good early target to
fill once `curvePointCount_le` / `curvePointCount_ge` are available.

## Main statements (skeletons)
* `Weil.genus` — the genus `(d-1)(p-1)/2` of the Artin–Schreier curve of `f`.
* `Weil.abs_curvePointCount_sub_card_le` — the two-sided point-count bound.
-/

open scoped BigOperators
open Polynomial

namespace Weil

variable {F : Type*} [Field F] [Fintype F]

/-- The genus of the Artin–Schreier curve `y^p - y = f(x)`, namely `(d-1)(p-1)/2` with
`d = deg f` and `p = ringChar F`.  (Natural-number division; for the relevant `f` with `p ∤ d`
the numerator `(d-1)(p-1)` is even.) -/
noncomputable def genus (f : F[X]) : ℕ := (f.natDegree - 1) * (ringChar F - 1) / 2

/-
**Two-sided point-count bound (`|N - q| ≤ 2g√q`).**  Combining the two one-sided Stepanov
bounds gives `|#C_f(𝔽_q) - q| ≤ (d-1)(p-1)√q`, i.e. `2g√q`.
-/
lemma abs_curvePointCount_sub_card_le (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    |(asPointCount f : ℝ) - Fintype.card F|
      ≤ (f.natDegree - 1) * (ringChar F - 1) * Real.sqrt (Fintype.card F) := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · convert sub_le_sub_right ( Weil.Stepanov.curvePointCount_le f hd ) ( Fintype.card F : ℝ ) using 1 ; ring;
  · have := Stepanov.curvePointCount_ge f hd;
    linarith

end Weil