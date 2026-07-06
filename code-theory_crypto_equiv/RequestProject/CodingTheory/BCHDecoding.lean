import Mathlib
import RequestProject.CodingTheory.BCHBound

/-!
# Bounded-distance decoding from the BCH bound

This module continues the coding-theory development
(`CODING_THEORY_DIRECTIONS.md`, item 13) by deriving from the **BCH bound**
(`RequestProject/CodingTheory/BCHBound.lean`) the classical *unique decoding*
guarantee for BCH / cyclic codes.

Fix distinct nonzero nodes `x₀, …, x_{n-1}` (for a genuine BCH code the powers of
a primitive root of unity) and recall the *syndrome* at exponent `e` of a word
`c : Fin n → F`, namely `S_e(c) = ∑_i c_i · x_iᵉ`. The BCH bound says a nonzero
word with `2t` consecutive vanishing syndromes has Hamming weight `≥ 2t + 1`.

Consequently two words of weight `≤ t` (the "error patterns" of two transmissions
within the correction radius) that share `2t` consecutive syndromes must coincide:
their difference has weight `≤ 2t` and `2t` consecutive vanishing syndromes, so it
is zero. This is exactly the statement that a code with designed distance
`δ = 2t + 1` corrects up to `t` errors — bounded-distance decoding is unambiguous.

## Main results

* `bch_decode_unique` — two words of Hamming weight `≤ t` with equal `2t`
  consecutive syndromes are equal (unique bounded-distance decoding).
-/

open Finset BigOperators

namespace CodingTheory
namespace BCH

variable {F : Type*} [Field F]

/-
**Unique bounded-distance decoding from the BCH bound.** Let `x₀, …, x_{n-1}`
be distinct nonzero field elements. If two words `c, c' : Fin n → F` both have
Hamming weight `≤ t` and agree on `2t` consecutive syndromes
`∑_i c_i · x_i^(b+l) = ∑_i c'_i · x_i^(b+l)` for `l = 0, …, 2t - 1`, then `c = c'`.
-/
theorem bch_decode_unique [DecidableEq F] {n : ℕ} (x : Fin n → F)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (c c' : Fin n → F) (t : ℕ)
    (hc : hammingNorm c ≤ t) (hc' : hammingNorm c' ≤ t) (b : ℕ)
    (hsyn : ∀ l : ℕ, l < 2 * t →
      ∑ i, c i * (x i) ^ (b + l) = ∑ i, c' i * (x i) ^ (b + l)) :
    c = c' := by
  by_contra h_neq;
  have h_diff : hammingNorm (c - c') ≤ 2 * t := by
    have h_diff : hammingNorm (c - c') ≤ hammingNorm c + hammingNorm c' := by
      exact le_trans ( Finset.card_le_card fun i hi => by by_cases hi1 : c i = 0 <;> by_cases hi2 : c' i = 0 <;> simp_all +decide [ sub_eq_zero ] ) ( Finset.card_union_le _ _ );
    linarith;
  have := bch_bound x hx hx0 ( c - c' ) ( sub_ne_zero.mpr h_neq ) b ( 2 * t + 1 ) ?_;
  · linarith;
  · simp_all +decide [ sub_mul ]

end BCH
end CodingTheory