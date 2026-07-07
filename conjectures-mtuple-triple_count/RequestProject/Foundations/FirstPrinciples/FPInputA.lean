import RequestProject.Foundations.FirstPrinciples.FPStickelberger
import RequestProject.Foundations.FirstPrinciples.FPMcEliece
import RequestProject.Foundations.KasamiGrossKoblitzValue
import RequestProject.Foundations.KasamiDigitSumBound
import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import Mathlib

/-!
# First-principles tower, Core (A) — module A·fp·s5: input (A) divisibility, unconditional

This module is the **assembly** of Core (A): it composes the two from-scratch
sub-towers — the Gross–Koblitz valuation (`FPGaussSumSetup`, `FPStickelberger`)
and the McEliece factorial bound (`FPMcEliece`) — through the project's already
sorry-free reduction modules (`KasamiGrossKoblitzValue`, `KasamiDigitSumBound`,
`KasamiGrossKoblitzDivisibility`) to produce the input-(A) divisibility

```
   2^{(n+1)/2} ∣ R(s)            for all s            (hdiv)
```

with **no remaining hypotheses** beyond the field/parameter data — the named
cores `hGKval`, `hbound` having been discharged (modulo the `sorry`s in the
sub-towers).

This is the precise sense of "first-principles": the only `sorry`s feeding this
result are the genuinely transcendental leaves in `FPPadicGamma`/`FPStickelberger`
(Gross–Koblitz) and `FPMcEliece` (Ax–Katz/McEliece); the wiring here is a real
proof.

## Sources

Gross–Koblitz (Ann. Math. 1979); Canteaut–Charpin–Dobbertin (IEEE-IT 2000);
McEliece (1972).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Input (A), unconditional.**  Assembling the Gross–Koblitz value `hGKval`
(from the Gauss-sum identification `kasami_crossCorr_eq_gaussInt` and the
Stickelberger valuation `kasami_gaussInt_padicVal`) and the digit-sum bound
`hbound` (from the McEliece factorial bound `kasami_exp_factorial_bound` and the
size condition `kasami_exp_ge`), the input-(A) divisibility holds for every
frequency. -/
theorem kasami_crossCorr_hdiv {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2)
      ∣ autocorrScaled (fun x : F => x ^ d k) s a := by
  have hGKval :
      ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
        padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a)
          = binDigitSum (kasamiExp k a s) :=
    Vanish.Foundations.grossKoblitz_hGKval a (kasamiExp k a) (kasamiGaussInt k a)
      (kasami_crossCorr_eq_gaussInt hcard hk hkn hcop hnodd a ha)
      (kasami_gaussInt_padicVal hcard hk hkn hcop hnodd a ha)
  have hbound :
      ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
        (n + 1) / 2 ≤ binDigitSum (kasamiExp k a s) :=
    Vanish.Foundations.hbound_of_factorial_bound a (kasamiExp k a)
      (kasami_exp_ge hcard hk hkn hcop hnodd a ha)
      (kasami_exp_factorial_bound hcard hk hkn hcop hnodd a ha)
  exact Vanish.Foundations.kasami_crossCorr_hdiv_of_grossKoblitz a (kasamiExp k a) hGKval hbound

end Vanish.Foundations.FirstPrinciples
