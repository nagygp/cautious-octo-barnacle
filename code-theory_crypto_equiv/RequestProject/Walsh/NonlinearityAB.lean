import RequestProject.Walsh.Nonlinearity

/-!
# Almost-bent permutations meet the SCV nonlinearity bound with equality

This module continues `RequestProject/Walsh/Nonlinearity.lean`, which proved the
**Sidelnikov–Chabaud–Vaudenay nonlinearity bound** `scv_max_walsh_sq_ge`: for any
permutation `f` of `GF(2ⁿ)` (`n ≥ 1`) there is a nonzero input mask `a` and an
output mask `b` with `W(a, b)² ≥ 2|F|` (equivalently nonlinearity
`≤ 2^{n-1} − 2^{(n-1)/2}`).

Here we prove the **almost-bent ⇒ equality** direction: an almost-bent (AB)
permutation meets that bound with equality.  By definition an AB function has only
the two Walsh squares `0` and `2|F|` in every nonzero direction
(`walsh_sq_zero_or_two_card`), so every `W(a, b)²` (`a ≠ 0`) is `≤ 2|F|`; combined
with the SCV lower bound there is a pair attaining `W(a, b)² = 2|F|` exactly.  Thus
the maximal Walsh square of an AB permutation is exactly `2|F|`, i.e. its
nonlinearity is exactly `2^{n-1} − 2^{(n-1)/2}` — the SCV optimum.

## Main results

* `IsAB.walsh_sq_le_two_card` — every nonzero-direction Walsh square of an AB
  function is `≤ 2|F|`.
* `IsAB.exists_walsh_sq_eq_two_card` — an AB permutation attains `W(a, b)² = 2|F|`
  for some `a ≠ 0`, `b` (the SCV bound is met with equality).
* `IsAB.scv_nonlinearity_equality` — the combined statement: the SCV nonlinearity
  bound holds with equality, i.e. `2|F|` is both attained and an upper bound for
  the nonzero-direction Walsh squares.
-/

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Every nonzero-direction Walsh square of an almost-bent function is at most
`2|F|`: by definition its only values are `0` and `2|F|`. -/
theorem IsAB.walsh_sq_le_two_card {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hab : IsAB hcard f) (a : F) (ha : a ≠ 0) (b : F) :
    walsh f a b ^ 2 ≤ 2 * (Fintype.card F : ℤ) := by
  rcases walsh_sq_zero_or_two_card hcard hab a ha b with h | h
  · rw [h]; positivity
  · rw [h]

/-- **The SCV nonlinearity bound is attained by an almost-bent permutation.**
There is a nonzero input mask `a` and an output mask `b` with
`W(a, b)² = 2|F|`. -/
theorem IsAB.exists_walsh_sq_eq_two_card {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hab : IsAB hcard f) :
    ∃ a : F, a ≠ 0 ∧ ∃ b : F, walsh f a b ^ 2 = 2 * (Fintype.card F : ℤ) := by
  obtain ⟨a, ha, b, hb⟩ := scv_max_walsh_sq_ge hcard hn hf
  exact ⟨a, ha, b, le_antisymm (IsAB.walsh_sq_le_two_card hcard hab a ha b) hb⟩

/-- **Almost-bent ⇒ equality in the SCV nonlinearity bound.**  For an almost-bent
permutation of `GF(2ⁿ)` (`n ≥ 1`) the maximal nonzero-direction Walsh square is
exactly `2|F|`: it is attained (`∃ a ≠ 0, ∃ b, W² = 2|F|`) and it is an upper
bound (`∀ a ≠ 0, ∀ b, W² ≤ 2|F|`).  Equivalently the nonlinearity equals
`2^{n-1} − 2^{(n-1)/2}`, the SCV optimum. -/
theorem IsAB.scv_nonlinearity_equality {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hab : IsAB hcard f) :
    (∃ a : F, a ≠ 0 ∧ ∃ b : F, walsh f a b ^ 2 = 2 * (Fintype.card F : ℤ))
      ∧ (∀ a : F, a ≠ 0 → ∀ b : F, walsh f a b ^ 2 ≤ 2 * (Fintype.card F : ℤ)) :=
  ⟨IsAB.exists_walsh_sq_eq_two_card hcard hn hf hab,
   fun a ha b => IsAB.walsh_sq_le_two_card hcard hab a ha b⟩

end WalshAB
