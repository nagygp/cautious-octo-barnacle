import RequestProject.Weil.CharSum

/-!
# The zeta-function route (Weil I): statements only

This module records the *alternative*, much deeper route to the Weil bound via the zeta function
of the curve and the Riemann Hypothesis for curves (Weil I).  It is **not** the recommended fill
target — see `RequestProject.Weil.Stepanov` and `RequestProject.Weil.WeilBound` for the
self-contained Stepanov route — but we record the precise *statements* so the roadmap is complete.

To avoid committing to a full extension-field / zeta-function formalisation (which is not currently
in Mathlib), we work with an *abstract* sequence of point counts `N : ℕ → ℕ`, where `N k` is
intended to be `#C(𝔽_{q^k})`.  The classical theory says:

* **Rationality.**  `Z(C/𝔽_q, T) = exp(∑_{k≥1} N k · T^k / k)` is a rational function `P(T) / ((1-T)(1-qT))`
  with `P` a polynomial of degree `2g` and `P(0) = 1`.
* **Functional equation + RH (Weil I).**  Writing `P(T) = ∏_{i} (1 - α_i T)`, the reciprocal roots
  satisfy `|α_i| = √q`.  Equivalently, `N k = q^k + 1 - ∑_i α_i^k` with `|α_i| = √q`.

The single genuinely-elementary consequence — that RH for the curve implies the point-count bound
`|N k - (q^k + 1)| ≤ 2g √(q^k)` — is recorded as `Weil.Zeta.abs_sub_le_of_satisfiesRH`; it is a
direct triangle-inequality argument and is a good fillable target.  Proving `SatisfiesRH` for an
actual curve is the deep content of Weil I and is left entirely open here.

## Main definitions / statements
* `Weil.Zeta.SatisfiesRH q g N` — the Riemann Hypothesis for the curve, phrased on point counts.
* `Weil.Zeta.abs_sub_le_of_satisfiesRH` — RH ⇒ the `2g√q` point-count bound (fillable).
-/

open scoped BigOperators

namespace Weil
namespace Zeta

/-- **The Riemann Hypothesis for a curve, phrased via point counts.**

`SatisfiesRH q g N` says there are `2g` complex "Frobenius eigenvalues" `α i`, each of absolute
value `√q`, such that `N k = q^k + 1 - ∑ i, (α i)^k` for every `k ≥ 1`.  This is the content of
Weil I (rationality + functional equation + RH) repackaged on the level of point counts. -/
def SatisfiesRH (q g : ℕ) (N : ℕ → ℕ) : Prop :=
  ∃ α : Fin (2 * g) → ℂ,
    (∀ i, ‖α i‖ = Real.sqrt q) ∧
    (∀ k, 1 ≤ k → (N k : ℂ) = (q : ℂ) ^ k + 1 - ∑ i, (α i) ^ k)

/-
**RH ⇒ point-count bound.**  If the curve satisfies the Riemann Hypothesis then
`|N k - (q^k + 1)| ≤ 2g √(q^k)` for every `k ≥ 1`.  This is the elementary triangle-inequality
consequence and a good first fill target in this module.
-/
theorem abs_sub_le_of_satisfiesRH (q g : ℕ) (N : ℕ → ℕ) (h : SatisfiesRH q g N)
    (k : ℕ) (hk : 1 ≤ k) :
    |(N k : ℝ) - ((q : ℝ) ^ k + 1)| ≤ 2 * g * Real.sqrt ((q : ℝ) ^ k) := by
  obtain ⟨ α, hα₁, hα₂ ⟩ := h;
  have h_norm : ‖(N k : ℂ) - (q ^ k + 1)‖ ≤ ∑ i, ‖α i‖ ^ k := by
    rw [ hα₂ k hk ] ; norm_num [ norm_sub_rev ] ; exact norm_sum_le _ _ |> le_trans <| by norm_num;
  convert h_norm using 1 ; norm_cast ; simp +decide [ *, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ];
  exact Or.inl <| by rw [ mul_comm ] ;

end Zeta
end Weil