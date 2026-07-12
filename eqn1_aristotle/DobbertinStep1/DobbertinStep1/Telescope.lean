import Mathlib
import DobbertinStep1.Defs
import DobbertinStep1.Frobenius

/-!
# Telescoping of the partial trace

The algebraic heart of step (1) ⟹ (2).  With `S(x) = ∑_{i=1}^{k'} x^{2^{ik}}`
and `P(x) = ∑_{j<k'} x^{2^{jk}}`:

* `S = P^{2^k}` (`numeratorSum_eq_partialTrace_frob`);
* `P^{2^k} + P = x^{2^{k'k}} + x` (pure char-2 telescoping);
* hence, when `k·k' ≡ 1 (mod n)`, `P^{2^k} + P = x² + x` (Artin–Schreier form).
-/

namespace Dobbertin.Step1

open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] in
/-- `S(x) = P(x)^{2^k}`: the numerator sum is the Frobenius-`2^k` image of the
partial trace. -/
lemma numeratorSum_eq_partialTrace_frob (k k' : ℕ) (x : F) :
    numeratorSum k k' x = partialTrace k k' x ^ (2 ^ k) := by
  unfold numeratorSum partialTrace
  rw [sum_pow_char_pow, ← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) ?_
  intro i _
  rw [← pow_mul, ← pow_add]
  ring_nf

omit [Fintype F] in
/-- **Raw telescoping** in characteristic `2`:
`P(x)^{2^k} + P(x) = x^{2^{k'k}} + x` (no finite-field hypothesis needed). -/
lemma partialTrace_telescope_raw (k k' : ℕ) (x : F) :
    partialTrace k k' x ^ (2 ^ k) + partialTrace k k' x = x ^ (2 ^ (k' * k)) + x := by
  unfold partialTrace
  rw [sum_pow_char_pow]
  induction k' with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have last : ((x ^ (2 ^ (m * k))) ^ (2 ^ k)) = x ^ (2 ^ ((m + 1) * k)) := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have regroup :
        (∑ j ∈ range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k)) + (x ^ (2 ^ (m * k))) ^ (2 ^ k)
          + ((∑ j ∈ range m, x ^ (2 ^ (j * k))) + x ^ (2 ^ (m * k)))
        = ((∑ j ∈ range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k))
            + (∑ j ∈ range m, x ^ (2 ^ (j * k))))
          + ((x ^ (2 ^ (m * k))) ^ (2 ^ k) + x ^ (2 ^ (m * k))) := by ring
    rw [regroup, ih, last]
    -- cancel the shared middle term `x^{2^{mk}}` (characteristic `2`)
    rw [show ∀ a b c : F, a + b + (c + a) = c + b from fun a b c => by
      rw [add_comm c a, ← add_assoc, add_assoc a b a, add_comm b a, ← add_assoc,
        CharTwo.add_self_eq_zero, zero_add, add_comm]]

/-- **Artin–Schreier telescoping.**  If `k·k' ≡ 1 (mod n)` on `𝔽_{2ⁿ}`, then
`P(x)^{2^k} + P(x) = x² + x`. -/
lemma partialTrace_telescope {n k k' : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * k' % n = 1) (x : F) :
    partialTrace k k' x ^ (2 ^ k) + partialTrace k k' x = x ^ 2 + x := by
  rw [partialTrace_telescope_raw]
  have : x ^ (2 ^ (k' * k)) = x ^ 2 := by
    rw [pow_two_pow_mod hn x (k' * k), Nat.mul_comm k' k, hkk', pow_one]
  rw [this]

end Dobbertin.Step1
