import RequestProject.Foundations.KasamiAdditiveEnergyBE3e
import RequestProject.Foundations.KasamiSecondDerivMultiplicity
import RequestProject.Foundations.FirstPrinciples.Decomp.SecondDerivativeDecomp
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# First-principles tower, Core (B) — module B·fp·s1: the AB second-derivative multiplicities

This is the **bottom rung** of the from-scratch closure of input (B)
(`Docs/VanishFutureDirections.md`, §15/§8.3, frontier (B)).  It supplies the
genuinely AB-specific content the additive-energy value rests on: the per-value
**multiplicity distribution of the second-order derivative**

```
   z ↦ derivPairCount f a z = #{(x,y) : Δf_a x + Δf_a y = z}
```

of the Kasami (almost-bent) map.  Its second moment off the diagonal is the deep
core of (B):

```
   ∑_{z≠0} derivPairCount (·^{d k}) a z ² = q³ − 2q²            (the AB core)
```

— *not* implied by APN alone (it fails for APN-but-not-AB functions).  The
already-proved BE3 layers reduce the additive-energy value to exactly this moment
(`additiveEnergy_value_iff_derivPairCount_sq`), so this single statement is the
remaining frontier; we carry it as `sorry`.

The supporting first-moment / diagonal facts (`derivPairCount_zero`,
`derivPairCount_sum_offDiag`) are already proved unconditionally in
`KasamiSecondDerivMultiplicity.lean` (APN); this module adds the AB second moment.

## Sources

Carlet, *Boolean Functions for Cryptography and Coding Theory*, Ch. 6 (AB
functions); Chabaud–Vaudenay §3; Canteaut–Charpin–Dobbertin (IEEE-IT 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The AB second-derivative second moment (the deep core of (B)).**  For the
Kasami almost-bent map `x ↦ x^{d k}` over `GF(2ⁿ)` (`n` odd, `gcd(k,n)=1`), the
off-diagonal second moment of the second-order-derivative collision count is

```
   ∑_{z≠0} derivPairCount (·^{d k}) a z ² = q³ − 2q² .
```

This is the almost-bent multiplicity content (the AB-vs-APN distinction); via the
BE3 reduction it is equivalent to the additive-energy value `16·E = q³ + 2q²`. -/
theorem kasami_derivPairCount_sq_offDiag {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ z ∈ univ.erase (0 : F), (derivPairCount (fun x : F => x ^ d k) a z) ^ 2 : ℤ)
      = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2 :=
  Decomp.kasami_derivPairCount_sq_offDiag hcard hk hkn hcop hnodd hn a ha

end Vanish.Foundations.FirstPrinciples
