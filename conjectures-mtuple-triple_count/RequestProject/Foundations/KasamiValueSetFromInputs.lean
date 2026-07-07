import RequestProject.Foundations.KasamiCrossCorrelationValueSet
import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import Mathlib

/-!
# Foundations — the Kasami cross-correlation value set from the two scalar inputs (A), (B)

This capstone module **assembles the reduced forms of inputs (A) and (B)** into the
full Kasami cross-correlation value set, exhibiting that the two scalar inputs are
the *entire* remaining gap of the value-set program.

`KasamiCrossCorrelationValueSet.kasami_crossCorr_value_set` derives the four-valued
set
```
   R(s) ∈ { q, 0, +2^{(n+1)/2}, −2^{(n+1)/2} }
```
from two hypotheses: the input-(A) divisibility `hdiv : 2^{(n+1)/2} ∣ R(s)` and the
input-(B) fourth moment `hfourth : ∑_{s≠0} R(s)⁴ = 2q³`.  This module discharges
both from the reduced cores delivered in the (A) and (B) layers:

* **input (A)** — `hdiv` is produced by `kasami_crossCorr_hdiv_of_grossKoblitz`
  (`KasamiGrossKoblitzDivisibility.lean`) from the Gross–Koblitz value `hGKval`
  (`v₂(R(s)) = s₂(e s)`) and the digit-sum bound `hbound` (`(n+1)/2 ≤ s₂(e s)`);
* **input (B)** — `hfourth` is produced by
  `kasami_autocorr_fourthMoment_offDiag_of_bridge`
  (`KasamiAutocorrWalshBridge.lean`) from the Wiener–Khinchin bridge identity
  `hWK : ∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴` together with the *proven* Walsh fourth
  moment `WalshAB.fourth_moment_apn`.

The conclusion `kasami_crossCorr_value_set_of_cores` therefore depends only on the
three genuine deep cores `hGKval`, `hbound`, `hWK` — the precise sense in which
"the two scalar inputs (A) and (B) are now the whole remaining gap".

## Scope

The assembly is sorry-free.  The three named hypotheses `hGKval`, `hbound`, `hWK`
are the deep cores carried (per project convention) by the (A) and (B) layers; this
module adds no new ones.

## Sources

Dillon–Dobbertin (FFA 2004); Canteaut–Charpin–Dobbertin (IEEE-IT 2000);
Gross–Koblitz (Ann. Math. 1979).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Kasami cross-correlation value set from the reduced cores (A) and (B).**
Combining the input-(A) divisibility produced from the Gross–Koblitz value
`hGKval` and the digit-sum bound `hbound`, with the input-(B) fourth moment
produced from the Wiener–Khinchin bridge `hWK` (and the proven Walsh fourth
moment), every Kasami cross-correlation value lies in
`{ q, 0, ±2^{(n+1)/2} }`. -/
theorem kasami_crossCorr_value_set_of_cores {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0)
    (e : F → ℕ)
    (hGKval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s))
    (hbound : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (e s))
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4)
    (s : F) :
    autocorrScaled (fun x : F => x ^ d k) s a = (Fintype.card F : ℤ)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 0
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2) := by
  have hdiv : ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
      ∣ autocorrScaled (fun x : F => x ^ d k) s a :=
    kasami_crossCorr_hdiv_of_grossKoblitz a e hGKval hbound
  have hfourth : ∑ s ∈ univ.erase (0 : F),
      (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3 :=
    kasami_autocorr_fourthMoment_offDiag_of_bridge hcard hk hkn hcop hnodd hn a ha hWK
  exact kasami_crossCorr_value_set hcard hk hkn hcop hnodd hn a ha hdiv hfourth s

end Vanish.Foundations
