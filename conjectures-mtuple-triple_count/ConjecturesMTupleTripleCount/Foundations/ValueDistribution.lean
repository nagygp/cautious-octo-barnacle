import Mathlib

/-!
# Foundations — verification pearls for Layer 5 (the three-valued spectrum)

This module collects the **Mathlib-only, crypto-free "verification pearls"**
harvested while transcribing **Layer 5** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): the elementary facts that turn a *two-valued
square* into a *three-valued value* and that read off the value distribution of a
sign-valued (`{-1, 0, 1}`) function from its first two moments.

They contain no finite-field, Walsh, or Kasami vocabulary, are stated at full
generality, and are therefore directly upstreamable.  The project-specific
application to the Walsh spectrum of an AB function lives in
`ConjecturesMTupleTripleCount/Foundations/ABSpectrum.lean`.

## Pearls

* `eq_zero_or_eq_or_eq_neg_of_sq_eq_zero_or_sq` — in any commutative ring without
  zero divisors, `x² ∈ {0, c²}` forces `x ∈ {0, c, -c}`.
* `sum_eq_posCard_sub_negCard` — the **first moment** of a `{-1, 0, 1}`-valued
  function counts the signed difference `#{k = 1} − #{k = -1}`.
* `sum_sq_eq_posCard_add_negCard` — the **second moment** counts the support
  `#{k = 1} + #{k = -1}`.
* `posCard_add_negCard_add_zeroCard` — the three counts partition the index set.

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): each pearl has a single
responsibility and an intention-revealing name, is stated at the most general
carrier it admits, and reuses Mathlib (`sq_eq_sq_iff_eq_or_eq_neg`,
`pow_eq_zero_iff`, the `Finset.filter`/`card` API) rather than re-deriving.
-/

namespace Vanish.Foundations

open Finset BigOperators

/-- **Three-valued from a two-valued square.**  In a commutative ring without
zero divisors, if `x²` is either `0` or `c²`, then `x ∈ {0, c, -c}`.

This is the elementary engine behind the three-valued Walsh spectrum of an AB
function: `W² ∈ {0, 2^{n+1}}` and `2^{n+1} = (2^{(n+1)/2})²` (for `n` odd) give
`W ∈ {0, ±2^{(n+1)/2}}`. -/
theorem eq_zero_or_eq_or_eq_neg_of_sq_eq_zero_or_sq
    {R : Type*} [CommRing R] [NoZeroDivisors R] {x c : R}
    (h : x ^ 2 = 0 ∨ x ^ 2 = c ^ 2) : x = 0 ∨ x = c ∨ x = -c := by
  rcases h with h | h
  · exact Or.inl ((pow_eq_zero_iff (two_ne_zero)).mp h)
  · exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp h)

section SignDistribution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℤ)

/-- The number of indices where `k` takes the value `1`. -/
def posCard : ℕ := (univ.filter (fun i => k i = 1)).card

/-- The number of indices where `k` takes the value `-1`. -/
def negCard : ℕ := (univ.filter (fun i => k i = -1)).card

/-- The number of indices where `k` takes the value `0`. -/
def zeroCard : ℕ := (univ.filter (fun i => k i = 0)).card

/-
**First moment of a sign-valued function.**  If `k` takes only the values
`-1, 0, 1`, then `∑ k = #{k = 1} − #{k = -1}`.
-/
theorem sum_eq_posCard_sub_negCard
    (hk : ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1) :
    ∑ i, k i = (posCard k : ℤ) - (negCard k : ℤ) := by
  convert Finset.sum_congr rfl fun i _ => show k i = if k i = -1 then -1 else if k i = 1 then 1 else 0 from ?_ using 1;
  · unfold posCard negCard; simp +decide [ Finset.sum_ite ] ; ring;
    rw [ show ( Finset.filter ( fun x => k x = 1 ) Finset.univ ) = Finset.filter ( fun x => k x = 1 ) ( Finset.filter ( fun x => ¬k x = -1 ) Finset.univ ) by ext x; specialize hk x; aesop ] ; ring;
  · rcases hk i with ( h | h | h ) <;> simp +decide [ h ]

/-
**Second moment of a sign-valued function.**  If `k` takes only the values
`-1, 0, 1`, then `∑ k² = #{k = 1} + #{k = -1}` (the size of the support).
-/
theorem sum_sq_eq_posCard_add_negCard
    (hk : ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1) :
    ∑ i, (k i) ^ 2 = (posCard k : ℤ) + (negCard k : ℤ) := by
  convert Finset.sum_congr rfl fun i _ => show k i ^ 2 = if k i = 1 then 1 else if k i = -1 then 1 else 0 by rcases hk i with ( h | h | h ) <;> rw [ h ] <;> decide;
  simp +decide [ Finset.sum_ite, posCard, negCard ];
  exact congr_arg Finset.card ( by ext; aesop )

/-
**The three counts partition the index set.**  If `k` takes only the values
`-1, 0, 1`, then `#{k = 1} + #{k = -1} + #{k = 0} = |ι|`.
-/
theorem posCard_add_negCard_add_zeroCard
    (hk : ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1) :
    posCard k + negCard k + zeroCard k = Fintype.card ι := by
  unfold posCard negCard zeroCard;
  rw [ Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun i _ => by rcases hk i with ( h | h | h ) <;> simp +decide [ h ] ;

end SignDistribution

end Vanish.Foundations