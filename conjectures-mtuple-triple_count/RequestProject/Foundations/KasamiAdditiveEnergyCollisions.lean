import RequestProject.Foundations.KasamiAdditiveEnergyBound
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-8: the additive-collision decomposition

This module is a **further from-scratch foundational rung of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), refining B-fp-5
(`KasamiAdditiveEnergyBound.lean`).

The AB core of (B) is the *exact* value `16·E = q³ + 2q²`, which the elementary
B-fp-6/B-fp-7 bounds only bracket as `q³/16 ≤ E ≤ q³/8`.  The gap to the exact
value is the count of the **"extra" additive quadruples** — the genuine AB
content.  This module isolates that count by splitting the additive energy into its
*diagonal* part and its *collision* part:

```
   E(S) = |S|²  +  ∑_t r_S(t)·(r_S(t) − 1).
```

The first term `|S|²` counts the trivial (diagonal) quadruples `(a,b,a,b)`; the
second term

```
   C(S) := ∑_t r_S(t)·(r_S(t) − 1)            (additiveCollisions)
```

counts the **ordered pairs of distinct representations** `a+b = c+d = t` — exactly
the "extra" additive quadruples whose number the AB three-valued Walsh spectrum
fixes.  Algebraically this is the identity `r² = r + r(r−1)` summed against
`∑_t r_S(t) = |S|²` (`sum_repCount`).

For the AB derivative image `|S| = q/2`, the value `16·E = q³ + 2q²` therefore reads
`16·C = q³ − 2q²` — pinning the count of extra quadruples to `(q³ − 2q²)/16`.  That
value is the carried core of (B).

## Results

* `additiveCollisions` — the collision count `∑_t r_S(t)·(r_S(t) − 1)`.
* `additiveEnergy_eq_card_sq_add_collisions` — `E(S) = |S|² + C(S)`.
* `additiveCollisions_eq` — `C(S) = E(S) − |S|²`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite combinatorics over
`(F,+)`; it introduces no new hypotheses.  The remaining content — the *value* of
the collision count (equivalently the AB value `16·E = q³ + 2q²`) — is the carried
core of (B).

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy); Carlet, Ch. 6 (AB
functions); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The **additive-collision count** `C(S) = ∑_t r_S(t)·(r_S(t) − 1)`: the number
of ordered pairs of *distinct* representations `a + b = c + d = t` — the "extra"
(non-diagonal) additive quadruples. -/
noncomputable def additiveCollisions (S : Finset F) : ℕ :=
  ∑ t : F, repCount S t * (repCount S t - 1)

/-- **The additive-collision decomposition.**  The additive energy splits into its
diagonal part `|S|²` and its collision part `C(S)`:
`E(S) = |S|² + ∑_t r_S(t)·(r_S(t) − 1)`.  This is `r² = r + r(r−1)` summed against
`∑_t r_S(t) = |S|²`. -/
theorem additiveEnergy_eq_card_sq_add_collisions (S : Finset F) :
    additiveEnergy S = S.card ^ 2 + additiveCollisions S := by
  have key : ∀ n : ℕ, n ^ 2 = n + n * (n - 1) := by
    intro n
    cases n with
    | zero => rfl
    | succ m => simp [pow_two]; ring
  rw [additiveEnergy_eq_sum_repCount_sq, additiveCollisions, ← sum_repCount S,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => key _)

/-- **The collision count as the energy excess.**  `C(S) = E(S) − |S|²`. -/
theorem additiveCollisions_eq (S : Finset F) :
    additiveCollisions S = additiveEnergy S - S.card ^ 2 := by
  rw [additiveEnergy_eq_card_sq_add_collisions]
  omega

end Vanish.Foundations
