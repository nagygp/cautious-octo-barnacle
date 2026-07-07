import RequestProject.Foundations.RankSpectrum
import RequestProject.Foundations.GoldQuadratic
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-4: the Gold-form radical / rank

This module is the **fourth from-scratch foundational module of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), building on the rank ⇒ spectrum substrate
(`RankSpectrum.lean`, `GoldQuadratic.lean`) and the auxiliary Gold form
`q^λ_{a}(x) = λ x^{2^{3k}+1} + a x^{2^k+1}` (`kasamiAux_isQuadraticForm`).

The rank-evaluation step of equation (12) needs to know that the auxiliary Gold
form has a **one-dimensional radical** (generically), i.e. `|radical Q| = 2`
(rank `n − 1`).  Feeding `|radical Q| = 2 = 2¹` into the rank ⇒ spectrum principle
(`rank_spectrum`, with `r = 1`) pins the Gauss sum to `{0, ±2^{(n+1)/2}}`: the
exponent equation `2m = n + 1` has the (unique, for `n` odd) solution
`m = (n+1)/2`.

This is the precise bridge that turns the radical/rank datum of the auxiliary Gold
form into the value set of each equation-(12) term.  The radical-size datum
`|radical Q| = 2` itself — the linearized-polynomial gcd computation pinning the
radical to one dimension — is carried here as a hypothesis (it is the content of
the rank-computation core DD-fp-5 below); what this module proves is the *reduction*
`|radical| = 2 ⟹ S(Q) ∈ {0, ±2^{(n+1)/2}}`.

## Results

* `quadForm_radical_two_spectrum` — for any quadratic form `Q` over `GF(2ⁿ)`
  (`n` odd) with `|radical Q| = 2`, `S(Q) ∈ {0, ±2^{(n+1)/2}}`.
* `kasamiAux_radical_two_spectrum` — its specialization to the auxiliary Gold form
  `λ x^{2^{3k}+1} + a x^{2^k+1}`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the rank ⇒ spectrum reduction for
the one-dimensional-radical case; the linearized-polynomial computation that the
radical *is* one-dimensional is the rank-computation core, carried as the
hypothesis `|radical Q| = 2`.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4; Lidl–Niederreiter, *Finite Fields*,
Ch. 6 (linearized polynomials, quadratic forms).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Rank-1 radical ⇒ the AB value set.**  A quadratic form over `GF(2ⁿ)` with
`n` odd whose radical has exactly two elements (`|radical Q| = 2`, rank `n − 1`)
has Gauss sum `S(Q) ∈ {0, ±2^{(n+1)/2}}`.  This is `rank_spectrum` with `r = 1`:
the exponent equation `2m = n + 1` forces `m = (n+1)/2`.
-/
theorem quadForm_radical_two_spectrum {n : ℕ} {Q : F → F} (hQ : IsQuadraticForm Q)
    (hcard : Fintype.card F = 2 ^ n) (hn : Odd n)
    (hr : (radical Q).card = 2) :
    quadGaussSum Q = 0
      ∨ quadGaussSum Q = 2 ^ ((n + 1) / 2)
      ∨ quadGaussSum Q = -2 ^ ((n + 1) / 2) := by
  have := Vanish.Foundations.rank_spectrum hQ hcard ( show Finset.card ( radical Q ) = 2 ^ 1 by simp +decide [ hr ] );
  grind

/-- **The auxiliary Gold form, rank-1 radical ⇒ AB value set.**  Specializing
`quadForm_radical_two_spectrum` to the Appendix-A.4 auxiliary Gold form
`q^λ_{a}(x) = λ x^{2^{3k}+1} + a x^{2^k+1}` (`kasamiAux_isQuadraticForm`). -/
theorem kasamiAux_radical_two_spectrum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (lam a : F)
    (hr : (radical (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))).card = 2) :
    quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1)) = 0
      ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
          = 2 ^ ((n + 1) / 2)
      ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
          = -2 ^ ((n + 1) / 2) :=
  quadForm_radical_two_spectrum (kasamiAux_isQuadraticForm k lam a) hcard hn hr

end Vanish.Foundations