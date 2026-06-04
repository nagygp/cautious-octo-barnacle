import Mathlib
import RequestProject.Character

/-!
# Vanishing Conditions for Character Sum Products

Defines the m-tuple counting setup and two spectral conditions:
- `Vanish`: the product P(v) vanishes for all v ≠ 0
- `FlatSpectrum`: all nonzero character sums over T vanish

Proves: `FlatSpectrum + nonzero coefficients ⟹ Vanish`.

## Definitions
- `TupleSet m T c`: `{x ∈ Tᵐ | ∑ cᵢxᵢ = 0}`
- `κ m T c`: cardinality of `TupleSet`
- `P χ m c T v`: product `∏ᵢ S χ (v·cᵢ) T`
- `Vanish`: `∀ v ≠ 0, P(v) = 0`
- `FlatSpectrum`: `∀ w ≠ 0, S χ w T = 0`
-/

open Finset Fintype

namespace MTupleCount

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

-- ── Counting definitions ─────────────────────────────────────────

/-- The m-tuple intersection set: tuples in Tᵐ with `∑ cᵢxᵢ = 0`. -/
def TupleSet (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽) : Finset (Fin m → 𝔽) :=
  (piFinset fun _ => T).filter fun x => ∑ i, c i * x i = 0

/-- The m-tuple count `κₘ = |TupleSet|`. -/
def κ (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽) : ℕ :=
  (TupleSet m T c).card

-- ── Character sum product ────────────────────────────────────────

/-- Product of character sums: `P(v) = ∏ᵢ S(v·cᵢ, T)`. -/
def P (χ : Chi 𝔽) (m : ℕ) (c : Fin m → 𝔽) (T : Finset 𝔽) (v : 𝔽) : ℤ :=
  ∏ i, S χ (v * c i) T

-- ── Spectral conditions ──────────────────────────────────────────

/-- Vanishing: `∀ v ≠ 0, P(v) = 0`. -/
def Vanish (χ : Chi 𝔽) (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽) : Prop :=
  ∀ v : 𝔽, v ≠ 0 → P χ m c T v = 0

/-- Flat spectrum: `∀ w ≠ 0, S χ w T = 0`. -/
def FlatSpectrum (χ : Chi 𝔽) (T : Finset 𝔽) : Prop :=
  ∀ w : 𝔽, w ≠ 0 → S χ w T = 0

-- ── Implication: FlatSpectrum + nonzero coeffs ⟹ Vanish ─────────

/-- A product with a zero factor is zero. -/
lemma prod_eq_zero_of_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) (i : ι) (hi : g i = 0) : ∏ j, g j = 0 :=
  Finset.prod_eq_zero (mem_univ i) hi

/-- **FlatSpectrum + nonzero coefficients ⟹ Vanish.**

When `S χ w T = 0` for all `w ≠ 0`, and every `cᵢ ≠ 0`,
each `v ≠ 0` makes `v · c₀ ≠ 0`, so `S χ (v·c₀) T = 0`,
killing the entire product. -/
theorem vanish_of_flatSpectrum (χ : Chi 𝔽) (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽)
    (hflat : FlatSpectrum χ T) (hm : 0 < m) (hc : ∀ i, c i ≠ 0) :
    Vanish χ m T c :=
  fun _ hv => prod_eq_zero_of_factor _ ⟨0, hm⟩ (hflat _ (mul_ne_zero hv (hc ⟨0, hm⟩)))

end MTupleCount
