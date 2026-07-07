import Mathlib
import RequestProject.DiffUniformity.FlystelWalshLinearPotential
import RequestProject.DiffUniformity.FlystelWalshGaussSumTwo

/-!
# An unconditional Walsh sandwich (ZK track) — the quadratic / `d = 2` regime

This module records the **unconditional** form of the Walsh sandwich of
`FlystelWalshSandwich.lean`. There the upper bound `(d−1)·p` on the deep entries
was supplied as a Rojas-León *hypothesis* `hdeep`. Here we remove that hypothesis
in the regime that Track 1 (`FlystelWalshGaussSumTwo.lean`) now discharges
*without* assumptions: when the deep-entry linear-approximation functions are
nondegenerate binary quadratics, the unconditional two-variable Gauss-sum bound
`rojasLeonBoundTwo_quadratic` gives `‖W‖ ≤ q` on every nonzero mask, and the
unconditional Parseval lower bound `exists_walsh_sq_ge` gives
`q⁴/(q²+1) ≤ ‖W‖²`.

Combining the two **traps the maximal Walsh coefficient with no algebraic-geometry
input at all**:

```
q⁴ / (q² + 1)  ≤  ‖W_F(ψ, a, b)‖²  ≤  q²        (for a single nonzero mask).
```

The two ends differ only by the factor `1 + 1/q²`, so the maximal coefficient is
pinned to `q · (1 + o(1))` — the linearity is asymptotically `q`, matching the
`(d−1)·p = q` value of Theorem 3.3 at `d = 2`.

For the genuine higher-degree Anemoi (`x³`) and Poseidon (`x⁵`) S-boxes the deep
entries have degree `d ≥ 3`, where the expected bound is `(d−1)·q > q`; those
conditional sandwiches stay in `FlystelWalshSandwich.lean` because their
unconditional upper bound is exactly the still-open `d ≥ 3` two-variable
Rojas-León estimate (cf. `CharSumWeilGaussSum.lean`, where the one-variable
`d ≥ 3` Gauss-sum gate is isolated).

## Main results

* `walsh_sandwich_of_uniform_bound` — the abstract sandwich: any uniform upper
  bound `B` on the nonzero-mask spectrum, combined with the Parseval lower bound,
  traps the maximal coefficient.
* `walsh_sandwich_unconditional` — the unconditional sandwich with `B = q`, valid
  for any map whose nonzero-mask coefficients all obey `‖W‖ ≤ q` (e.g. the
  quadratic / `d = 2` regime via `walsh_norm_le_of_quadratic`).
-/

open Finset

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Abstract Walsh sandwich.** Given any uniform upper bound `B` on the
nonzero-mask Walsh spectrum of `F`, the unconditional Parseval lower bound traps
the maximal coefficient: some nonzero mask `(a, b)` satisfies both
`q⁴/(q²+1) ≤ ‖W_F(ψ,a,b)‖²` (cleared form) and `‖W_F(ψ,a,b)‖ ≤ B`. -/
theorem walsh_sandwich_of_uniform_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) (hcard : 2 ≤ Fintype.card K) (B : ℝ)
    (hupper : ∀ a b : K × K, (a ≠ 0 ∨ b ≠ 0) → ‖walsh ψ F a b‖ ≤ B) :
    ∃ a b : K × K, (a, b) ≠ (0, 0) ∧
      (Fintype.card K : ℝ) ^ 4
        ≤ ((Fintype.card K : ℝ) ^ 2 + 1) * Complex.normSq (walsh ψ F a b) ∧
      ‖walsh ψ F a b‖ ≤ B := by
  obtain ⟨a, b, hab0, hlow⟩ := exists_walsh_sq_ge ψ hψ F hcard
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inr (by rintro rfl; exact hab0 (by rw [ha]))
    · exact Or.inl ha
  exact ⟨a, b, hab0, hlow, hupper a b hne⟩

/-- **Unconditional Walsh sandwich (quadratic / `d = 2` regime).** If every
nonzero-mask Walsh coefficient of `F` obeys the unconditional `d = 2` bound
`‖W_F(ψ,a,b)‖ ≤ q` — for instance because every deep-entry linear-approximation
function is a nondegenerate binary quadratic (`walsh_norm_le_of_quadratic`) and
the remaining entries vanish — then the maximal coefficient is trapped, with no
algebraic-geometry hypothesis, as

```
q⁴/(q²+1) ≤ ‖W_F(ψ,a,b)‖² ≤ q².
```
-/
theorem walsh_sandwich_unconditional (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) (hcard : 2 ≤ Fintype.card K)
    (hupper : ∀ a b : K × K, (a ≠ 0 ∨ b ≠ 0) →
      ‖walsh ψ F a b‖ ≤ (Fintype.card K : ℝ)) :
    ∃ a b : K × K, (a, b) ≠ (0, 0) ∧
      (Fintype.card K : ℝ) ^ 4
        ≤ ((Fintype.card K : ℝ) ^ 2 + 1) * Complex.normSq (walsh ψ F a b) ∧
      Complex.normSq (walsh ψ F a b) ≤ (Fintype.card K : ℝ) ^ 2 := by
  obtain ⟨a, b, hab0, hlow, hup⟩ :=
    walsh_sandwich_of_uniform_bound ψ hψ F hcard (Fintype.card K : ℝ) hupper
  refine ⟨a, b, hab0, hlow, ?_⟩
  have hsq : Complex.normSq (walsh ψ F a b) = ‖walsh ψ F a b‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hsq]
  have hnn : (0 : ℝ) ≤ ‖walsh ψ F a b‖ := norm_nonneg _
  nlinarith [hup, hnn]

end FlystelWalsh
end APN
