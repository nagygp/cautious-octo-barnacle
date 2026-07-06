import RequestProject.Foundations.FirstPrinciples.FPABEnergyValue
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import Mathlib

/-!
# First-principles tower, Core (B) — module B·fp·s3: input (B) fourth moment, unconditional

This module is the **assembly** of Core (B): feeding the discharged Wiener–Khinchin
bridge `kasami_hWK` (`FPABEnergyValue.lean`) to the project's already sorry-free
bridge `kasami_autocorr_fourthMoment_offDiag_of_bridge`
(`KasamiAutocorrWalshBridge`, which supplies the proven Walsh fourth moment) yields
the input-(B) fourth moment

```
   ∑_{s≠0} R(s)⁴ = 2·q³            (hfourth)
```

with no remaining hypotheses — the only `sorry` feeding it being the AB
second-derivative second moment `kasami_derivPairCount_sq_offDiag`
(`FPSecondDerivative.lean`).

## Sources

Carlet, Ch. 6; Cusick–Stănică, Ch. 2; Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Input (B), unconditional.**  The discharged bridge `kasami_hWK`, fed to
`kasami_autocorr_fourthMoment_offDiag_of_bridge`, gives the nonzero-frequency
fourth moment `∑_{s≠0} R(s)⁴ = 2·q³`. -/
theorem kasami_crossCorr_hfourth {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 :=
  Vanish.Foundations.kasami_autocorr_fourthMoment_offDiag_of_bridge
    hcard hk hkn hcop hnodd hn a ha
    (kasami_hWK hcard hk hkn hcop hnodd hn a ha)

end Vanish.Foundations.FirstPrinciples
