import RequestProject.Foundations.KasamiAdditiveEnergy
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-5: additive energy as squared representations

This module is a **further from-scratch foundational rung of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), refining B-fp-4
(`KasamiWienerKhinchinBridge.lean`).

B-fp-4 pinned the Wiener–Khinchin bridge `hWK` down to the single scalar value
`16·E(Im Δf_a) = q³ + 2q²`.  The remaining frontier is to *compute* the additive
energy `E`.  The standard first step is the **representation identity**: the
additive energy equals the sum of squared representation counts,

```
   E(S) = ∑_t r_S(t)²,        r_S(t) = #{ (a,b) ∈ S² | a + b = t },
```

which turns the fourth-order object `E` into a second-order count.  In
characteristic `2` the additive-energy constraint `y₀+y₁+y₂+y₃ = 0` is precisely
`y₀+y₁ = y₂+y₃`, so each admissible quadruple is a pair of representations of a
common sum `t`, giving the identity above.

From it, the elementary bounds drop out: the diagonal quadruples `(a,b,a,b)` (valid
since `a+b+a+b = 0` in characteristic `2`) give the lower bound `|S|² ≤ E(S)`, and
the total representation count is `∑_t r_S(t) = |S|²`.  These are the
characteristic-2 foundations under the AB additive-energy value of B-fp-4.

## Results

* `repCount` — the representation count `r_S(t) = #{ (a,b) ∈ S² | a + b = t }`.
* `sum_repCount` — `∑_t r_S(t) = |S|²`.
* `additiveEnergy_eq_sum_repCount_sq` — `E(S) = ∑_t r_S(t)²`.
* `card_sq_le_additiveEnergy` — the diagonal lower bound `|S|² ≤ E(S)`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite combinatorics over
`(F,+)` in characteristic `2`; it introduces no new hypotheses.  The remaining
content — that the representation counts of the AB derivative image sum to the AB
value `q³ + 2q²` — is the carried core of (B).

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy); Carlet, Ch. 6 (AB
functions); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The representation count** `r_S(t) = #{ (a,b) ∈ S² | a + b = t }`. -/
noncomputable def repCount (S : Finset F) (t : F) : ℕ :=
  (univ.filter (fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = t)).card

/-
**The total representation count.**  `∑_t r_S(t) = |S|²`.
-/
omit [CharP F 2] in
theorem sum_repCount (S : Finset F) :
    ∑ t : F, repCount S t = S.card ^ 2 := by
  convert Finset.sum_congr rfl fun t _ => Finset.card_filter ( fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = t ) Finset.univ using 1;
  rw [ ← Finset.sum_product' ];
  rw [ Finset.sum_product ] ; simp +decide [ sq ];
  rw [ ← Finset.card_product ] ; rw [ ← Finset.card_biUnion ] ; congr ; ext x ; aesop;
  exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z => by aesop;

/-
**Additive energy as squared representations.**  In characteristic `2`, the
additive energy equals the sum of squared representation counts,
`E(S) = ∑_t r_S(t)²`.
-/
theorem additiveEnergy_eq_sum_repCount_sq (S : Finset F) :
    additiveEnergy S = ∑ t : F, (repCount S t) ^ 2 := by
  unfold additiveEnergy;
  simp +decide [ Fin.sum_univ_four, repCount ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ sq, ← Finset.card_product ] ];
  rw [ ← Finset.card_biUnion ];
  · refine' Finset.card_bij ( fun y hy => ( ( y 0, y 1 ), ( y 2, y 3 ) ) ) _ _ _ <;> simp +decide;
    · grind;
    · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h₀ h₁ h₂ h₃ => by ext i; fin_cases i <;> assumption;
    · intro a b c d ha hb hc hd h; use fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d; simp +decide [ Fin.forall_fin_succ, * ] ;
      grind +qlia;
  · intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;

/-
**The diagonal lower bound.**  The diagonal quadruples `(a,b,a,b)` (valid in
characteristic `2`, since `a+b+a+b = 0`) inject `S²` into the additive-energy
quadruples, giving `|S|² ≤ E(S)`.
-/
theorem card_sq_le_additiveEnergy (S : Finset F) :
    S.card ^ 2 ≤ additiveEnergy S := by
  convert Finset.card_le_card_of_injOn _ _ ?_;
  rw [ sq, Finset.card_product ];
  exact fun p => fun i => if i = 0 then p.1 else if i = 1 then p.2 else if i = 2 then p.1 else p.2;
  · intro p hp; simp_all +decide [ Fin.sum_univ_four ] ;
    grind;
  · intro p hp q hq h; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
    grind

end Vanish.Foundations