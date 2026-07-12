import Mathlib

/-!
# Frobenius periodicity on `𝔽_{2ⁿ}`

The single finite-field fact used by the telescoping step: on `F = 𝔽_{2ⁿ}` the
Frobenius power `x ↦ x^{2^r}` depends only on `r mod n`, because `x^{|F|} = x`.
-/

namespace Dobbertin.Step1

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [CharP F 2] in
/-- **Frobenius periodicity.**  On `𝔽_{2ⁿ}`, `x^{2^r} = x^{2^{r mod n}}`. -/
lemma pow_two_pow_mod {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) (r : ℕ) :
    x ^ (2 ^ r) = x ^ (2 ^ (r % n)) := by
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have step : ∀ j : ℕ, x ^ (2 ^ (n * j)) = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, FiniteField.pow_card, ih]
  rw [step]

end Dobbertin.Step1
