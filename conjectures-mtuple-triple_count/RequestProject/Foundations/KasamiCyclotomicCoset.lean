import RequestProject.Foundations.KasamiMcElieceCosetBound
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-11: the explicit `2`-cyclotomic coset

This module is a **further from-scratch foundational rung of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-10 (`KasamiMcElieceCosetBound.lean`) and the digit-sum
doubling-invariance `binDigitSum_two_pow_mul_mod` (AK3.3.0).

The next step toward the McEliece core of (A) is to **pin down the abstract
exponent `e s` concretely** as a `2`-cyclotomic coset representative.  This module
introduces the explicit coset as a `Finset` and proves the two facts that make
"the McEliece bound per coset" a well-posed, representative-independent statement:

* the binary digit sum `s₂` is **constant** on the `2`-cyclotomic coset
  (`binDigitSum_const_on_cyclotomicCoset`), an immediate consequence of the
  doubling-invariance; and
* hence the McEliece lower bound `(n+1)/2 ≤ s₂(·)` is **equivalent across the whole
  coset** (`mcEliece_bound_const_on_cyclotomicCoset`) — so it need only be checked
  on the (unique, minimal) coset representative.

The coset of `s` (reduced mod `2ⁿ − 1`) is the Frobenius orbit
`{ (2^j · s) mod (2ⁿ − 1) | 0 ≤ j < n }`; the residue `s mod (2ⁿ − 1)` itself is a
member (`self_mem_cyclotomicCoset`, taking `j = 0`).

## Results

* `cyclotomicCoset` — the `2`-cyclotomic coset of `s` modulo `2ⁿ − 1`.
* `self_mem_cyclotomicCoset` — `s mod (2ⁿ − 1)` is a coset member.
* `binDigitSum_const_on_cyclotomicCoset` — `s₂` is constant on the coset.
* `mcEliece_bound_const_on_cyclotomicCoset` — the McEliece bound is equivalent
  across the coset.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure `Nat` digit / coset
arithmetic; it introduces no new hypotheses.  The remaining content — the *value*
of `s₂` on the Kasami coset exponents (the McEliece weight congruence) and the
Gross–Koblitz `p`-adic Γ valuation — are the carried cores of (A).

## Sources

McEliece, *Weight congruences for p-ary cyclic codes* (1972); Canteaut–Charpin–
Dobbertin (IEEE-IT 2000); Lidl–Niederreiter, *Finite Fields*, Ch. 6
(cyclotomic cosets).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

/-- The **`2`-cyclotomic coset** of `s` modulo `2ⁿ − 1`: the Frobenius orbit
`{ (2^j · s) mod (2ⁿ − 1) | 0 ≤ j < n }`. -/
def cyclotomicCoset (n s : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun j => (2 ^ j * s) % (2 ^ n - 1))

/-- **The residue is a coset member.**  Taking `j = 0`, `s mod (2ⁿ − 1)` lies in
the `2`-cyclotomic coset of `s`. -/
theorem self_mem_cyclotomicCoset {n : ℕ} (hn : 1 ≤ n) (s : ℕ) :
    s % (2 ^ n - 1) ∈ cyclotomicCoset n s := by
  refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, ?_⟩
  simp

/-- **The digit sum is constant on the `2`-cyclotomic coset.**  Every member
`t = (2^j · s) mod (2ⁿ − 1)` has the same binary digit sum as the representative
`s mod (2ⁿ − 1)`, by the doubling-invariance `binDigitSum_two_pow_mul_mod`. -/
theorem binDigitSum_const_on_cyclotomicCoset {n : ℕ} (hn : 1 ≤ n) (s : ℕ) :
    ∀ t ∈ cyclotomicCoset n s, binDigitSum t = binDigitSum (s % (2 ^ n - 1)) := by
  intro t ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  exact binDigitSum_two_pow_mul_mod hn j s

/-- **The McEliece bound is equivalent across the coset.**  Since `s₂` is constant
on the `2`-cyclotomic coset, the lower bound `(n+1)/2 ≤ s₂(·)` holds for every
coset member iff it holds for the representative — so the bound need only be checked
on one representative per coset. -/
theorem mcEliece_bound_const_on_cyclotomicCoset {n : ℕ} (hn : 1 ≤ n) (s : ℕ) :
    ∀ t ∈ cyclotomicCoset n s,
      ((n + 1) / 2 ≤ binDigitSum t ↔ (n + 1) / 2 ≤ binDigitSum (s % (2 ^ n - 1))) := by
  intro t ht
  rw [binDigitSum_const_on_cyclotomicCoset hn s t ht]

end Vanish.Foundations
