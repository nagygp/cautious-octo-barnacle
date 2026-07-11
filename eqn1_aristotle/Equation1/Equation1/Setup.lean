import Mathlib
import Equation1.Defs

/-!
# Equation (1) MVP — the elementary opening of Theorem 1's proof (engine-free)

These are the first provable statements in the proof of Dobbertin's **Theorem 1**,
which come *before* equations (1)/(2) and use only `Mathlib` — no finite-field
engine.  From the paper's proof:

> *Proof.*  First note that `(2^k − 1)⁻¹ (mod 2ⁿ−1)` exists, since `gcd(k, n) = 1`.
> We have `q_α(0) = 0`, using the convention "`0/0 = 0`".  To verify the "only if"
> part, observe that `k' + α·n ≡ 0 (mod 2)` is equivalent to
> `q_α(1) = k'·1 + α·Tr(1) = 0`.

Concretely this module proves:

* `mersenne_coprime` / `inv_mod_exists` — the multiplicative inverse of `2^k − 1`
  modulo `2ⁿ − 1` exists whenever `gcd(k, n) = 1` (pure number theory:
  `gcd(2^k−1, 2ⁿ−1) = 2^{gcd(k,n)} − 1 = 1`);
* `qKasami_zero` — `q_α(0) = 0` (the `0/0 = 0` convention: the numerator already
  vanishes at `0`);
* `Tr_one` and `qKasami_one` — evaluating at `1`: `Tr(1) = n` and
  `q_α(1) = k' + α·n` (in `L`);
* `qKasami_one_eq_zero_iff` — the **"only if"** equivalence
  `q_α(1) = 0 ↔ k' + α·n ≡ 0 (mod 2)` (char-2 cast).
-/

namespace Dobbertin1999.Paper

open scoped BigOperators
open Finset

/-! ## The inverse `(2^k − 1)⁻¹ (mod 2ⁿ − 1)` exists (pure number theory) -/

/-- Since `gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`, coprimality of `k` and `n`
makes `2^k − 1` and `2ⁿ − 1` coprime. -/
theorem mersenne_coprime {k n : ℕ} (h : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ n - 1) := by
  unfold Nat.Coprime at *
  rw [Nat.pow_sub_one_gcd_pow_sub_one]
  simp [h]

/-- The multiplicative inverse of `2^k − 1` modulo `2ⁿ − 1` exists whenever
`gcd(k, n) = 1` (and `1 < 2ⁿ − 1`). -/
theorem inv_mod_exists {k n : ℕ} (h : Nat.Coprime k n) (hn : 1 < 2 ^ n - 1) :
    ∃ b, (2 ^ k - 1) * b % (2 ^ n - 1) = 1 := by
  obtain ⟨b, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime (mersenne_coprime h) hn
  exact ⟨b, hb.2⟩

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

/-! ## Values at `0` and `1` -/

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
/-- Evaluating the generalized Kasami polynomial at `1`:
`q_α(1) = k'·1 + α·Tr(1) = k' + α·n` (in `L`). -/
theorem qKasami_one (α : ℕ) :
    qKasami (L := L) n k k' α 1 = ((k' + α * n : ℕ) : L) := by
  unfold qKasami Tr; simp

omit [Fintype L] in
/-- **The "only if" part of Theorem 1** at the level of the value at `1`:
`q_α(1) = 0` if and only if `k' + α·n ≡ 0 (mod 2)`. -/
theorem qKasami_one_eq_zero_iff (α : ℕ) :
    qKasami (L := L) n k k' α 1 = 0 ↔ (k' + α * n) % 2 = 0 := by
  rw [qKasami_one]
  rw [CharP.cast_eq_zero_iff L 2]
  omega

end Dobbertin1999.Paper
