import RequestProject.Foundations.KasamiLegendreValuation
import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-8: the digit-sum lower bound (`hbound`)

This module is the **eighth from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-1 (`KasamiLegendreValuation.lean`) and the divisibility assembly
(`KasamiGrossKoblitzDivisibility.lean`).

This is the core **A-fp-8**: the McEliece / Canteaut–Charpin–Dobbertin digit-sum
lower bound `(n+1)/2 ≤ s₂(e s)`, which discharges the named hypothesis `hbound` of
`KasamiGrossKoblitzDivisibility.lean`.

Via the A-fp-1 dictionary `binDigitSum_ge_iff_padicValNat_le`
(`b ≤ s₂(m) ↔ v₂(m!) ≤ m − b`), the digit-sum lower bound is **equivalent** to a
*factorial-valuation upper bound* on the exponents `e s` — the exact translation
McEliece's weight-divisibility theorem provides.  This module proves that
equivalence (carried per-frequency), reducing `hbound` to the
factorial-valuation form:

```
   ((n+1)/2 ≤ s₂(e s))   ⟺   (v₂((e s)!) ≤ e s − (n+1)/2)          (for (n+1)/2 ≤ e s)
```

* `digitSum_bound_iff_factorial` — the per-frequency equivalence.
* `hbound_of_factorial_bound` — `hbound` follows from the factorial-valuation
  bound (the McEliece weight-congruence input), under the size condition
  `(n+1)/2 ≤ e s`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the Legendre/Kummer dictionary
translation of `hbound`; the genuine combinatorial input — that the cyclotomic-coset
exponents satisfy the factorial-valuation bound (equivalently the digit-sum bound)
— is the McEliece / CCD core, carried as a named hypothesis.

## Sources

McEliece, *Weight congruences for p-ary cyclic codes* (1972); Canteaut–Charpin–
Dobbertin (IEEE-IT 2000); Ireland–Rosen, Ch. 1 (Legendre/Kummer).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [Field F] [Fintype F] [CharP F 2] in
/-- **The digit-sum bound as a factorial-valuation bound (per frequency).**  For a
frequency `s` with `(n+1)/2 ≤ e s`, the A-fp-1 dictionary
`binDigitSum_ge_iff_padicValNat_le` turns the McEliece digit-sum lower bound
`(n+1)/2 ≤ s₂(e s)` into the factorial-valuation upper bound
`v₂((e s)!) ≤ e s − (n+1)/2`. -/
theorem digitSum_bound_iff_factorial {n : ℕ} (e : F → ℕ) (s : F)
    (hle : (n + 1) / 2 ≤ e s) :
    ((n + 1) / 2 ≤ binDigitSum (e s))
      ↔ padicValNat 2 (Nat.factorial (e s)) ≤ e s - (n + 1) / 2 :=
  binDigitSum_ge_iff_padicValNat_le hle

/-- **`hbound` from the factorial-valuation bound.**  If for every non-zero
frequency the exponent satisfies `(n+1)/2 ≤ e s` and the factorial-valuation bound
`v₂((e s)!) ≤ e s − (n+1)/2` (the McEliece weight-congruence input), then the
digit-sum lower bound `hbound` `(n+1)/2 ≤ s₂(e s)` holds — the premise consumed by
`kasami_crossCorr_hdiv_of_grossKoblitz`. -/
theorem hbound_of_factorial_bound {n k : ℕ} (a : F) (e : F → ℕ)
    (hle : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 → (n + 1) / 2 ≤ e s)
    (hfact : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
        padicValNat 2 (Nat.factorial (e s)) ≤ e s - (n + 1) / 2) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (e s) :=
  fun s hs => (binDigitSum_ge_iff_padicValNat_le (hle s hs)).mpr (hfact s hs)

end Vanish.Foundations
