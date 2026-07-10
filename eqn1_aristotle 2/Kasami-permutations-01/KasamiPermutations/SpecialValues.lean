import Mathlib
import KasamiPermutations.KasamiMap

/-!
# Values of the Kasami map at `0` and `1`

The elementary evaluations that open Dobbertin's argument, before equations
(1)/(2) enter.  With the convention `0/0 = 0`:

* `qKasami_zero`            — `q_α(0) = 0`;
* `Tr_one` / `qKasami_one`  — `Tr(1) = n` and `q_α(1) = k' + α·n` (in `L`);
* `qKasami_one_eq_zero_iff` — the **"only if"** direction of the criterion at the
  point `1`: `q_α(1) = 0 ↔ k' + α·n ≡ 0 (mod 2)`.

Together with the "if" direction proved in `PermutationCriterion`, the value at
`1` is what forces the parity condition `k' + α·n ≡ 1 (mod 2)`.
-/

namespace Kasami

open scoped BigOperators
open Finset

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

omit [Fintype L] [CharP L 2] in
/-- `q_α(0) = 0`, using the convention `0/0 = 0`: the numerator of `q_α` already
vanishes at `0`. -/
theorem qKasami_zero (α : ℕ) : qKasami (L := L) n k k' α 0 = 0 := by
  unfold qKasami Tr
  have h1 : (∑ i ∈ Finset.Icc 1 k', (0 : L) ^ (2 ^ (i * k))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have : 0 < 2 ^ (i * k) := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  have h2 : (∑ i ∈ Finset.range n, (0 : L) ^ (2 ^ i)) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have : 0 < 2 ^ i := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  rw [h1, h2]; ring

omit [Fintype L] [CharP L 2] in
/-- `Tr(1) = n` in `L`. -/
theorem Tr_one : Tr (L := L) n (1 : L) = (n : L) := by
  unfold Tr; simp

omit [Fintype L] [CharP L 2] in
/-- Evaluating the generalized Kasami map at `1`:
`q_α(1) = k'·1 + α·Tr(1) = k' + α·n` (in `L`). -/
theorem qKasami_one (α : ℕ) :
    qKasami (L := L) n k k' α 1 = ((k' + α * n : ℕ) : L) := by
  unfold qKasami Tr; simp

omit [Fintype L] in
/-- **The "only if" part of the criterion** at the point `1`:
`q_α(1) = 0` if and only if `k' + α·n ≡ 0 (mod 2)`. -/
theorem qKasami_one_eq_zero_iff (α : ℕ) :
    qKasami (L := L) n k k' α 1 = 0 ↔ (k' + α * n) % 2 = 0 := by
  rw [qKasami_one]
  rw [CharP.cast_eq_zero_iff L 2]
  omega

end Kasami
