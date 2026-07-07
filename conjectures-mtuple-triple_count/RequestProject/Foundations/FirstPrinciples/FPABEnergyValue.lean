import RequestProject.Foundations.FirstPrinciples.FPSecondDerivative
import RequestProject.Foundations.KasamiAdditiveEnergyBE3e
import RequestProject.Foundations.KasamiWienerKhinchinBridge
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# First-principles tower, Core (B) — module B·fp·s2: the AB additive-energy value and `hWK`

This module assembles the input-(B) cores.  From the AB second-derivative second
moment of `FPSecondDerivative.lean` it derives the **additive-energy value**

```
   16·E(Im Δf_a) = q³ + 2q²                       (kasami_ab_additiveEnergy_value)
```

via the already-proved BE3 equivalence `additiveEnergy_value_iff_derivPairCount_sq`,
and then the **Wiener–Khinchin bridge**

```
   ∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴                   (kasami_hWK)
```

via the characterization `kasami_hWK_iff_additiveEnergy` (`KasamiWienerKhinchinBridge`).

These two are exactly the named cores carried downstream by
`KasamiAutocorrWalshBridge` / `KasamiValueSetFromInputs`; here they are discharged
(modulo the single `sorry` in `FPSecondDerivative.lean`).

## Sources

Carlet, Ch. 6; Cusick–Stănică, Ch. 2 (Wiener–Khinchin); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The AB additive-energy value.**  From the second-derivative second moment
(`kasami_derivPairCount_sq_offDiag`) and the BE3 equivalence
`additiveEnergy_value_iff_derivPairCount_sq`, the derivative-image additive energy
attains its almost-bent value `16·E = q³ + 2q²`. -/
theorem kasami_ab_additiveEnergy_value {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
  (Vanish.Foundations.additiveEnergy_value_iff_derivPairCount_sq n hn hcard
      (fun x : F => x ^ d k)
      (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha).mpr
    (kasami_derivPairCount_sq_offDiag hcard hk hkn hcop hnodd hn a ha)

/-- **The Wiener–Khinchin bridge `hWK`.**  From the additive-energy value and the
characterization `kasami_hWK_iff_additiveEnergy`, the bridge identity holds. -/
theorem kasami_hWK {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = (Fintype.card F : ℤ) ^ 4
        + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4 :=
  (Vanish.Foundations.kasami_hWK_iff_additiveEnergy hcard hk hkn hcop hnodd hn a ha).mpr
    (kasami_ab_additiveEnergy_value hcard hk hkn hcop hnodd hn a ha)

end Vanish.Foundations.FirstPrinciples
