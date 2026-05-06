/-
  Kasami/APN.lean

  The Kasami function is APN (Almost Perfect Nonlinear).

  This file combines the normalization and factorization results to
  prove that the Kasami function f(x) = x^{2^{2k} - 2^k + 1} is APN
  over GF(2^n) when gcd(k, n) = 1.

  The APN property means: for every nonzero a ∈ GF(2^n) and every v,
  the equation f(x + a) + f(x) = v has at most 2 solutions.

  Reference: Kasami (1971), Dobbertin (1999),
             Bracken–Byrne–Markin–McGuire, Theorem 3.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.Normalization

noncomputable section

open Finset Classical

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### The Kasami function is APN -/

/-- **Kasami APN Theorem.**
    The Kasami function `f(x) = x^{4^k - 2^k + 1}` is APN over `GF(2^n)`
    when `gcd(k, n) = 1` and `k ≥ 1`.

    Proof: By `kasami_derivative_le_two` from `Normalization.lean`, for every
    nonzero `a` and every `v`, the derivative equation has at most 2 solutions.

    Reference: Kasami (1971), Dobbertin (1999). -/
theorem kasami_is_APN (k n : ℕ) (hk : 0 < k)
    (hn : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ a : F, a ≠ 0 → ∀ v : F,
      (Finset.univ.filter fun x => kasamiDelta F k a x = v).card ≤ 2 := by
  intro a ha v
  exact kasami_derivative_le_two k F n hn hcoprime a ha v

end