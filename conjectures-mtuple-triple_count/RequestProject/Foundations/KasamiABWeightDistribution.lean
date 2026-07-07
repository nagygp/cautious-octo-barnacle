import RequestProject.Foundations.ABSpectrum
import RequestProject.Walsh.Moments
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-1: the AB Walsh weight distribution

This module is the **first from-scratch foundational module of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15).

Direction (B) closes the additive-energy value `16·E = q³ + 2q²` through the
MacWilliams / Pless power-moment route: the almost-bent three-valued Walsh
spectrum `{0, ±2^{(n+1)/2}}` determines the full *weight distribution* of the
Walsh values, and the higher power moments then read off the additive energy.

This module supplies the **explicit weight distribution** — the MacWilliams
output — by solving the two linear constraints already established in
`ABSpectrum.lean`:

* the support count `#{W = +} + #{W = −} = 2^{n−1}` (`walsh_support_count`,
  from the second moment `∑ W² = q²`), and
* the signed count `#{W = +} − #{W = −} = 2^{(n−1)/2}` (`walsh_signed_count`,
  from the first moment `∑ W = q`).

Solving them pins each individual count:

```
   2·#{W = +2^{(n+1)/2}} = 2^{n−1} + 2^{(n−1)/2},     (walsh_pos_count_two_mul)
   2·#{W = −2^{(n+1)/2}} = 2^{n−1} − 2^{(n−1)/2},     (walsh_neg_count_two_mul)
```

together with the zero count `#{W = 0} = 2^{n−1}` (`walsh_zero_count`).

As an immediate Pless-moment consistency check (and an independent,
spectrum-based derivation of the fourth moment that feeds (B)), the same counts
give

```
   ∑_b W(a,b)⁴ = 2·q³                                 (walsh_fourth_moment_from_spectrum)
```

— the AB fourth moment, here obtained purely from the weight distribution rather
than from the autocorrelation pipeline of `Walsh.Moments`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It introduces no new hypotheses beyond
the standing AB/permutation hypotheses already used by `ABSpectrum.lean`.  The
remaining deep core of (B) — the autocorrelation/Walsh fourth-moment
Wiener–Khinchin bridge `hWK` (equivalently `16·E = q³ + 2q²`) — is the subject of
the later modules of §15.

## Sources

MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 5 (power
moments); Carlet, *Boolean Functions for Cryptography and Coding Theory*, Ch. 6
(AB functions); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The explicit AB Walsh weight distribution -/

/-- **Positive-value count.**  Solving the support/signed constraints,
`2·#{W = +2^{(n+1)/2}} = 2^{n−1} + 2^{(n−1)/2}`. -/
theorem walsh_pos_count_two_mul {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    2 * ((univ.filter (fun b : F => walsh f a b = 2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ (n - 1) + 2 ^ ((n - 1) / 2) := by
  have hsupp := walsh_support_count hcard hodd hn hf hAB a ha
  have hsign := walsh_signed_count hcard hodd hf hf0 hAB a ha
  linarith

/-- **Negative-value count.**  Solving the support/signed constraints,
`2·#{W = −2^{(n+1)/2}} = 2^{n−1} − 2^{(n−1)/2}`. -/
theorem walsh_neg_count_two_mul {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n)
    (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f) (hf0 : f 0 = 0)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    2 * ((univ.filter (fun b : F => walsh f a b = -2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ (n - 1) - 2 ^ ((n - 1) / 2) := by
  have hsupp := walsh_support_count hcard hodd hn hf hAB a ha
  have hsign := walsh_signed_count hcard hodd hf hf0 hAB a ha
  linarith

/-! ## 2. The fourth moment from the weight distribution (Pless consistency) -/

/-
**The AB fourth moment from the weight distribution.**  Partitioning the
sum over `b` by the three Walsh values `{0, ±2^{(n+1)/2}}` and using the support
count `#{W ≠ 0} = 2^{n−1}` gives `∑_b W(a,b)⁴ = 2·q³`.  This is the
MacWilliams/Pless derivation of the fourth moment, independent of the
autocorrelation pipeline.
-/
theorem walsh_fourth_moment_from_spectrum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hn : 1 ≤ n) {f : F → F} (hf : Function.Bijective f)
    (hAB : IsAB hcard f) (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
  obtain ⟨ k, hk ⟩ := hodd;
  have h_fourth_moment : ∑ b, (walsh f a b : ℤ) ^ 4 = ∑ b ∈ Finset.univ.filter (fun b => (walsh f a b : ℤ) = 2 ^ ((n + 1) / 2)), (2 ^ ((n + 1) / 2) : ℤ) ^ 4 + ∑ b ∈ Finset.univ.filter (fun b => (walsh f a b : ℤ) = -2 ^ ((n + 1) / 2)), (-2 ^ ((n + 1) / 2) : ℤ) ^ 4 := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
    intro b hb; split_ifs <;> simp_all +decide [ IsAB ] ;
    · norm_num [ Nat.add_div ] at *;
      linarith [ pow_pos ( zero_lt_two' ℤ ) ( k + 1 ) ];
    · cases hAB a ha b <;> simp_all +decide [ Nat.add_div ];
      exact False.elim ( ‹¬walsh f a b = 2 ^ ( k + 1 ) › ( mul_left_cancel₀ ( sub_ne_zero_of_ne ‹¬walsh f a b = -2 ^ ( k + 1 ) › ) <| by ring_nf at *; linarith ) );
  have := Vanish.Foundations.walsh_support_count hcard ( by simp +decide [ hk ] ) hn hf hAB a ha; simp_all +decide [ Nat.add_div ] ;
  rw [ ← add_mul, this ] ; ring

end Vanish.Foundations