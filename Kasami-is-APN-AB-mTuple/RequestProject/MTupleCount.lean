import RequestProject.Core.APN
import RequestProject.Core.FourierInversion
import RequestProject.Core.ExpArith

/-!
# m-Tuple Count Theorem — Main Composition

Composes the modular components to prove:

> For APN `f : GF(2ⁿ) → GF(2ⁿ)`, under flat spectrum + nonzero coefficients,
> the m-tuple count is `κₘ = 2^{(m-1)n - m}`.

## Module dependency DAG

```
CharTwo ─→ APN ──────────────────────┐
                                     ↓
Character ─→ Vanishing ─→ FourierInversion ─→ MTupleCount
                                     ↑
ExpArith ────────────────────────────┘
```

## Theorems
- `m_tuple_count_vanish`: from `Vanish` hypothesis
- `m_tuple_count`: from `FlatSpectrum` + nonzero coefficients
- `triple_count`: specialisation to `m = 3`
-/

open Fintype

namespace MTupleCount

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- **m-Tuple Count (from Vanish).**
APN + vanishing ⟹ `κₘ = 2^{(m-1)n - m}`. -/
theorem m_tuple_count_vanish (n : ℕ) (hn : 3 ≤ n) (hcard : card 𝔽 = 2 ^ n)
    (m : ℕ) (hm : 2 ≤ m) (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0)
    (χ : Chi 𝔽) (hf : APN f) (c : Fin m → 𝔽)
    (hv : Vanish χ m (Δ f a) c) :
    κ m (Δ f a) c = 2 ^ ((m - 1) * n - m) := by
  have h1 := deriv_image_half f hf a ha n hcard
  have h2 := KR2 χ m (Δ f a) c hv
  rw [hcard, h1] at h2
  exact exp_cancel_int n m _ hn hm h2

/-- **m-Tuple Count (from FlatSpectrum + nonzero coefficients).**
APN + flat spectrum + all cᵢ ≠ 0 ⟹ `κₘ = 2^{(m-1)n - m}`.

Vanishing is *derived*, not assumed. -/
theorem m_tuple_count (n : ℕ) (hn : 3 ≤ n) (hcard : card 𝔽 = 2 ^ n)
    (m : ℕ) (hm : 2 ≤ m) (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0)
    (χ : Chi 𝔽) (hf : APN f) (c : Fin m → 𝔽)
    (hflat : FlatSpectrum χ (Δ f a)) (hc : ∀ i, c i ≠ 0) :
    κ m (Δ f a) c = 2 ^ ((m - 1) * n - m) :=
  m_tuple_count_vanish n hn hcard m hm f a ha χ hf c
    (vanish_of_flatSpectrum χ m (Δ f a) c hflat (by omega) hc)

/-- **Triple count**: `m = 3` gives `κ₃ = 2^{2n - 3}`. -/
theorem triple_count (n : ℕ) (hn : 3 ≤ n) (hcard : card 𝔽 = 2 ^ n)
    (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0) (χ : Chi 𝔽) (hf : APN f)
    (c : Fin 3 → 𝔽) (hflat : FlatSpectrum χ (Δ f a)) (hc : ∀ i, c i ≠ 0) :
    κ 3 (Δ f a) c = 2 ^ (2 * n - 3) :=
  m_tuple_count n hn hcard 3 (by norm_num) f a ha χ hf c hflat hc

end MTupleCount
