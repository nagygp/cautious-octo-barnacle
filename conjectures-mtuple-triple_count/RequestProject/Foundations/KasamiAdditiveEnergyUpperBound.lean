import RequestProject.Foundations.KasamiAdditiveEnergyBound
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-7: the trivial additive-energy upper bound

This module is a **further from-scratch foundational rung of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), refining B-fp-5
(`KasamiAdditiveEnergyBound.lean`) and B-fp-6
(`KasamiAdditiveEnergyCauchySchwarz.lean`).

B-fp-6 gave the trivial *lower* half `|S|⁴ ≤ q·E(S)` of the AB additive-energy
value `16·E = q³ + 2q²`.  This module supplies the matching trivial *upper*
companion, the bottom rung from the other side:

```
   E(S) ≤ |S|³.
```

It is immediate from the B-fp-5 representation identities: every representation
count `r_S(t) = #{(a,b) ∈ S² | a + b = t}` satisfies `r_S(t) ≤ |S|` (the second
coordinate is determined by the first), so

```
   E(S) = ∑_t r_S(t)²  ≤  |S| · ∑_t r_S(t)  =  |S| · |S|²  =  |S|³.
```

Together with B-fp-6, these two elementary bounds bracket the additive energy,
`|S|⁴/q ≤ E(S) ≤ |S|³`; for the AB derivative image `|S| = q/2` they read
`q³/16 ≤ E(Im Δf_a) ≤ q³/8`, and the AB value `(q³ + 2q²)/16` (the carried core
of (B)) lies at the *lower* end of this bracket — pinning down precisely how much
sharper the AB content is than the elementary bounds.

## Results

* `repCount_le_card` — `r_S(t) ≤ |S|`.
* `additiveEnergy_le_card_pow_three` — `E(S) ≤ |S|³`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite combinatorics over
`(F,+)`; it introduces no new hypotheses.  The remaining content — that the AB
derivative image *attains* the value `16·E = q³ + 2q²` — is the carried core of (B).

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy); Carlet, Ch. 6 (AB
functions); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Each representation count is at most `|S|`.**  The map `(a,b) ↦ a` injects the
representations `{(a,b) ∈ S² | a + b = t}` into `S` (the second coordinate `b = t − a`
is determined by the first), so `r_S(t) ≤ |S|`.
-/
omit [CharP F 2] in
theorem repCount_le_card (S : Finset F) (t : F) : repCount S t ≤ S.card := by
  convert Finset.card_le_card ( show Finset.image ( fun p : F × F => p.1 ) ( Finset.filter ( fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = t ) Finset.univ ) ⊆ S from ?_ ) using 1;
  · rw [ Finset.card_image_of_injOn ];
    · rfl;
    · intro p hp q hq; aesop;
  · grind

/-
**The trivial additive-energy upper bound.**  For any finite set `S ⊆ F`, the
additive energy satisfies `E(S) ≤ |S|³`.  From the B-fp-5 representation identities
`E(S) = ∑_t r_S(t)²` and `∑_t r_S(t) = |S|²` together with `r_S(t) ≤ |S|`
(`repCount_le_card`):
`E(S) = ∑_t r_S(t)² ≤ |S|·∑_t r_S(t) = |S|·|S|² = |S|³`.
-/
theorem additiveEnergy_le_card_pow_three (S : Finset F) :
    additiveEnergy S ≤ S.card ^ 3 := by
  rw [ additiveEnergy_eq_sum_repCount_sq ];
  refine' le_trans ( Finset.sum_le_sum fun t _ => show repCount S t ^ 2 ≤ S.card * repCount S t from _ ) _;
  · simpa only [ sq ] using Nat.mul_le_mul_right _ ( repCount_le_card S t );
  · rw [ ← Finset.mul_sum _ _ _, sum_repCount ] ; ring_nf ; norm_num

end Vanish.Foundations