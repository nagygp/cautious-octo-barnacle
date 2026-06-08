import Mathlib
import RequestProject.Core.Vanishing

/-!
# Fourier Inversion for m-Tuple Counts

Proves the key identity connecting character sums to tuple counts:

> `|𝔽| · κ = |T|ᵐ` (under vanishing)

## Key results
- `orthogonality_collapse`: `∑ v, P(v) = |𝔽| · κ`
- `c_zero_term`: `P(0) = |T|ᵐ`
- `KR2`: vanishing ⟹ `|𝔽| · κ = |T|ᵐ`
-/

open Finset BigOperators Fintype

namespace MTupleCount

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

-- ── Product expansion ────────────────────────────────────────────

/-- Expand `P(v)` as a sum over tuples in Tᵐ. -/
private lemma P_expand (χ : Chi 𝔽) (m : ℕ) (c : Fin m → 𝔽) (T : Finset 𝔽) (v : 𝔽) :
    P χ m c T v = ∑ x ∈ piFinset fun _ => T, ∏ i, χ.app (v * c i * x i) := by
  simp [P, S]; exact prod_univ_sum (fun _ => T) fun i j => χ.app (v * c i * j)

/-- Factor character products: `∏ᵢ χ(v·cᵢ·xᵢ) = χ(v · ∑ cᵢxᵢ)`. -/
private lemma chi_factor (χ : Chi 𝔽) (m : ℕ) (c : Fin m → 𝔽) (v : 𝔽) (x : Fin m → 𝔽) :
    ∏ i, χ.app (v * c i * x i) = χ.app (v * ∑ i, c i * x i) := by
  induction' (univ : Finset (Fin m)) using Finset.induction <;>
    simp_all +decide [mul_sum, mul_assoc]
  · exact χ.app_zero.symm
  · simp +decide [mul_add, χ.app_add]; exact Or.inl (by rw [mul_sum])

-- ── Orthogonality ────────────────────────────────────────────────

/-- **Fourier inversion**: `∑ v, P(v) = |𝔽| · κ`. -/
theorem orthogonality_collapse (χ : Chi 𝔽) (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽) :
    ∑ v : 𝔽, P χ m c T v = (card 𝔽 : ℤ) * (κ m T c : ℤ) := by
  have horth : ∀ s : 𝔽, ∑ v : 𝔽, χ.app (v * s) = if s = 0 then (card 𝔽 : ℤ) else 0 :=
    fun s => by simpa [mul_comm] using χ.orth s
  simp +decide only [P_expand, chi_factor, κ]
  rw [sum_comm, sum_congr rfl fun x _ => horth _]
  simp +decide [TupleSet, sum_ite, mul_comm]

-- ── Zero-frequency term ──────────────────────────────────────────

/-- `P(0) = |T|ᵐ`. -/
lemma c_zero_term (χ : Chi 𝔽) (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽) :
    P χ m c T 0 = (T.card : ℤ) ^ m := by
  simp [P, zero_mul, char_sum_zero, prod_const]

-- ── Sum splitting ────────────────────────────────────────────────

/-- Split a sum: `∑ v, g(v) = g(0) + ∑_{v≠0} g(v)`. -/
lemma sum_split (g : 𝔽 → ℤ) :
    ∑ v : 𝔽, g v = g 0 + ∑ v ∈ univ.filter (· ≠ 0), g v := by
  rw [← add_sum_erase univ g (mem_univ 0)]
  congr 1; exact sum_congr (by ext; simp [mem_erase, mem_filter]) fun _ _ => rfl

-- ── KR2: the Fourier counting identity ──────────────────────────

/-- **KR2**: vanishing ⟹ `|𝔽| · κ = |T|ᵐ`. -/
theorem KR2 (χ : Chi 𝔽) (m : ℕ) (T : Finset 𝔽) (c : Fin m → 𝔽)
    (hv : Vanish χ m T c) :
    (card 𝔽 : ℤ) * (κ m T c : ℤ) = (T.card : ℤ) ^ m := by
  rw [← orthogonality_collapse χ m T c, sum_split, c_zero_term]
  rw [show ∑ v ∈ univ.filter (· ≠ 0), P χ m c T v = 0
    from sum_eq_zero fun v hv' => hv v (by simp at hv'; exact hv')]
  ring

end MTupleCount
