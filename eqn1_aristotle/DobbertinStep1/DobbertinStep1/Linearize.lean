import Mathlib
import DobbertinStep1.Defs
import DobbertinStep1.Telescope

/-!
# The linearized equation `ℓ(x) = 0`

The core implication behind step (1) ⟹ (2): if `x ≠ 0` solves the working form
`S(x) + ε = c·x^{2^k+1}` of equation (1) (with the trace term collapsed to a bit
`ε ∈ {0,1}`), then the linearized polynomial `ℓ(x)` of equation (2) vanishes.

Mechanism ("adding the `2^k`-th power of (1) to itself"): from `S = P^{2^k}` and
`P^{2^k} + P = x² + x` we get `P = (x² + x) + c·x^{2^k+1} + ε`; raising to the
`2^k` power, using `P^{2^k} = S = c·x^{2^k+1} + ε` and `ε^{2^k} = ε`, and dividing
by `x^{2^k}` yields `ℓ(x) = 0`.
-/

namespace Dobbertin.Step1

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-
**The linearized equation.**  For `x ≠ 0`, a bit `ε ∈ {0,1}`, and
`k·k' ≡ 1 (mod n)`, the working equation `S(x) + ε = c·x^{2^k+1}` implies
`ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0`.
-/
lemma linearized_eq_zero_of_solution {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) {c x : F} (hx : x ≠ 0)
    (hsol : numeratorSum k k' x + ε = c * x ^ (2 ^ k + 1)) :
    linearized k c x = 0 := by
  unfold linearized
  set P := partialTrace k k' x
  set S := numeratorSum k k' x
  have hS : S = P ^ (2 ^ k) := numeratorSum_eq_partialTrace_frob k k' x
  have hP : P ^ (2 ^ k) + P = x ^ 2 + x := partialTrace_telescope hn hkk' x
  -- `ε^{2^k} = ε` because `ε` is a bit
  have hεpow : ε ^ (2 ^ k) = ε := by
    rcases hε with rfl | rfl <;> simp [zero_pow (show (2 : ℕ) ^ k ≠ 0 by positivity)]
  -- solve equation (1) for `P`
  have hP_sub : P = (x ^ 2 + x) + c * x ^ (2 ^ k + 1) + ε := by grind +ring
  -- raise to the `2^k` power (Frobenius is additive), giving `S` in closed form
  have hS_pow : S = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k)
      + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + ε := by
    rw [hS, hP_sub, add_pow_char_pow, add_pow_char_pow, add_pow_char_pow, hεpow]
  -- cancel `ε` to isolate the core relation between the powers of `x`
  have h_core : c * x ^ (2 ^ k + 1)
      = (x ^ 2) ^ (2 ^ k) + x ^ (2 ^ k) + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) := by
    grind +ring
  -- divide by `x^{2^k} ≠ 0`
  apply mul_left_cancel₀ (pow_ne_zero (2 ^ k) hx)
  rw [mul_zero]
  -- reduce the compound exponents to the atoms `x^{2^k}` and `x^{2^{2k}}`
  have e1 : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ k) * x ^ (2 ^ k) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  have hexp : (2 ^ k + 1) * 2 ^ k = 2 ^ (2 * k) + 2 ^ k := by
    rw [add_mul, one_mul, ← pow_add, two_mul]
  have e2 : (c * x ^ (2 ^ k + 1)) ^ (2 ^ k)
      = c ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) * x ^ (2 ^ k)) := by
    rw [mul_pow, ← pow_mul, hexp, pow_add]
  rw [e1, e2] at h_core
  -- after substitution every term appears twice, so it vanishes in characteristic 2
  linear_combination (norm := ring_nf) h_core
  simp [CharTwo.two_eq_zero]

end Dobbertin.Step1
