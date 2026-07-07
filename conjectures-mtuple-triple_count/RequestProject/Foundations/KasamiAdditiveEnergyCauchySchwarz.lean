import RequestProject.Foundations.KasamiAdditiveEnergyBound
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-6: the Cauchy–Schwarz energy bound

This module is a **further from-scratch foundational rung of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), building directly on B-fp-5
(`KasamiAdditiveEnergyBound.lean`).

B-fp-5 reduced the additive energy to a second-order object via the
representation-count identities `E(S) = ∑_t r_S(t)²` and `∑_t r_S(t) = |S|²`.
The single most basic *quantitative* consequence — the bottom rung of the whole
additive-energy estimate, and the one closest to Mathlib — is the **Cauchy–Schwarz
lower bound**

```
   |S|⁴ ≤ q · E(S)        (q = |F|).
```

It is immediate from `∑_t r_S(t) = |S|²`, `E(S) = ∑_t r_S(t)²` and the
finite-sum Cauchy–Schwarz inequality `(∑ f)² ≤ |index| · ∑ f²`
(`Finset.sq_sum_le_card_mul_sum_sq`, over the `q` group elements `t`).  This is the
trivial *lower* half of the AB value `16·E = q³ + 2q²` (which says `E` attains the
near-extremal value `(q³ + 2q²)/16`): the AB content is that this Cauchy–Schwarz
bound is essentially tight, so the bound is the natural foundation underneath it.

## Results

* `card_pow_four_le_card_mul_additiveEnergy` — `|S|⁴ ≤ q · E(S)`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite combinatorics over
`(F,+)`; it introduces no new hypotheses.  The remaining content — that the AB
derivative image *attains* the value `16·E = q³ + 2q²` — is the carried core of (B).

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy and Cauchy–Schwarz);
Carlet, Ch. 6 (AB functions); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**The Cauchy–Schwarz lower bound on additive energy.**  For any finite set
`S ⊆ F`, the additive energy satisfies `|S|⁴ ≤ q · E(S)` with `q = |F|`.  This is
Cauchy–Schwarz `(∑_t r_S(t))² ≤ q · ∑_t r_S(t)²` applied to the representation
counts, using `∑_t r_S(t) = |S|²` (`sum_repCount`) and
`E(S) = ∑_t r_S(t)²` (`additiveEnergy_eq_sum_repCount_sq`).
-/
theorem card_pow_four_le_card_mul_additiveEnergy (S : Finset F) :
    S.card ^ 4 ≤ Fintype.card F * additiveEnergy S := by
  have h_cauchy_schwarz : (∑ t : F, (repCount S t : ℤ))^2 ≤ (Fintype.card F : ℤ) * (∑ t : F, (repCount S t : ℤ)^2) := by
    have h_cauchy_schwarz : ∀ (f : F → ℝ), (∑ t : F, f t)^2 ≤ (Fintype.card F : ℝ) * (∑ t : F, f t^2) := by
      intro f; have := Finset.univ.sum_le_sum fun i _ => pow_two_nonneg ( f i - ( ∑ j, f j ) / Fintype.card F ) ; simp_all +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ;
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      nlinarith [ mul_div_cancel₀ ( ∑ i, f i ) ( show ( Fintype.card F : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero ) ) ];
    exact_mod_cast h_cauchy_schwarz fun t => repCount S t;
  rw [ ← @Nat.cast_le ℤ ] ; push_cast ; rw [ additiveEnergy_eq_sum_repCount_sq ] ; convert h_cauchy_schwarz using 1 ; norm_cast ; simp +decide [ sum_repCount ] ; ring;
  norm_cast

end Vanish.Foundations