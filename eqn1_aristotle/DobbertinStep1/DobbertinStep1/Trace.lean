import Mathlib
import DobbertinStep1.Defs

/-!
# The trace is a bit

On `𝔽_{2ⁿ}` the absolute trace lands in the prime field `𝔽₂`: `Tr(x) ∈ {0, 1}`.
This is the "= 0 or 1" half of the step (1) ⟹ (2) — it makes the trace term
`α · Tr(x)` a bit `ε ∈ {0, 1}`.
-/

namespace Dobbertin.Step1

open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] in
/-- **Artin–Schreier identity** for the trace: `Tr(x)² + Tr(x) = x^{2ⁿ} + x`
(characteristic `2`; no field structure needed for the algebra). -/
lemma trace_sq_add_self (n : ℕ) (x : F) :
    trace n x ^ 2 + trace n x = x ^ (2 ^ n) + x := by
  induction n with
  | zero => simp [trace, CharTwo.add_self_eq_zero]
  | succ n ih =>
    -- peel off the top summand `x^{2^n}`
    have hsum : trace (n + 1) x = trace n x + x ^ (2 ^ n) := by
      simp [trace, Finset.sum_range_succ]
    -- squaring is additive in characteristic `2`
    have hsq : trace (n + 1) x ^ 2 = trace n x ^ 2 + (x ^ (2 ^ n)) ^ 2 := by
      rw [hsum, add_pow_char]
    have hpow : (x ^ (2 ^ n)) ^ 2 = x ^ (2 ^ (n + 1)) := by rw [← pow_mul, ← pow_succ]
    rw [hsq, hpow, hsum]
    -- regroup, apply the induction hypothesis, and cancel the repeated `x^{2^n}`
    rw [show trace n x ^ 2 + x ^ (2 ^ (n + 1)) + (trace n x + x ^ (2 ^ n))
          = (trace n x ^ 2 + trace n x) + (x ^ (2 ^ n) + x ^ (2 ^ (n + 1)))
          from by ring, ih]
    rw [show ∀ a b c : F, (a + b) + (a + c) = b + c from fun a b c => by
      rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add], add_comm]

/-- On `𝔽_{2ⁿ}` the trace is idempotent under squaring: `Tr(x)² = Tr(x)`. -/
lemma trace_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    trace n x ^ 2 = trace n x := by
  have h := trace_sq_add_self (F := F) n x
  have hpow : x ^ (2 ^ n) = x := by rw [← hn]; exact FiniteField.pow_card x
  rw [hpow, CharTwo.add_self_eq_zero] at h
  exact sub_eq_zero.mp (by rw [CharTwo.sub_eq_add]; exact h)

/-- **The trace is a bit.**  On `𝔽_{2ⁿ}`, `Tr(x) = 0 ∨ Tr(x) = 1`. -/
lemma trace_eq_zero_or_one {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    trace n x = 0 ∨ trace n x = 1 := by
  have h : trace n x * (trace n x - 1) = 0 := by
    have := trace_sq hn x; linear_combination this
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

end Dobbertin.Step1
