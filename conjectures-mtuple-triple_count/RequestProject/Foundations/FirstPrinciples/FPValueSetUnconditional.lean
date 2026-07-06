import RequestProject.Foundations.FirstPrinciples.FPInputA
import RequestProject.Foundations.FirstPrinciples.FPInputB
import RequestProject.Foundations.KasamiCrossCorrelationValueSet
import Mathlib

/-!
# First-principles tower — module fp·s6: the Kasami cross-correlation value set, unconditional

This module **removes the two named scalar hypotheses (A)/(B)** from
`KasamiCrossCorrelationValueSet.kasami_crossCorr_value_set`, feeding it the
from-scratch discharges:

* input (A) divisibility `hdiv` ← `FPInputA.kasami_crossCorr_hdiv`;
* input (B) fourth moment `hfourth` ← `FPInputB.kasami_crossCorr_hfourth`.

The result is the full Kasami cross-correlation value set
`R(s) ∈ {q, 0, ±2^{(n+1)/2}}` and its off-trivial three-valued form, depending
only on the deep leaves of the (A) and (B) towers (Gross–Koblitz/McEliece and the
AB second-derivative second moment), all carried as `sorry` at the bottom.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); Dillon–Dobbertin
(FFA 2004).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The unconditional Kasami cross-correlation value set.**  Every value lies in
`{q, 0, ±2^{(n+1)/2}}`. -/
theorem kasami_crossCorr_value_set {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0)
    (s : F) :
    autocorrScaled (fun x : F => x ^ d k) s a = (Fintype.card F : ℤ)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 0
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2) :=
  Vanish.Foundations.kasami_crossCorr_value_set hcard hk hkn hcop hnodd hn a ha
    (kasami_crossCorr_hdiv hcard hk hkn hcop hnodd a ha)
    (kasami_crossCorr_hfourth hcard hk hkn hcop hnodd hn a ha) s

/-- **The unconditional off-trivial three-valued form.**  For `s ≠ 0`,
`R(s) ∈ {0, ±2^{(n+1)/2}}` — the `hvals` shape consumed by Layer 12. -/
theorem kasami_crossCorr_three_valued {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0)
    (s : F) (hs : s ≠ 0) :
    autocorrScaled (fun x : F => x ^ d k) s a = 0
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = 2 ^ ((n + 1) / 2)
    ∨ autocorrScaled (fun x : F => x ^ d k) s a = -2 ^ ((n + 1) / 2) :=
  Vanish.Foundations.crossCorr_three_valued_of_div_fourth hcard hnodd _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha
    (kasami_crossCorr_hdiv hcard hk hkn hcop hnodd a ha)
    (kasami_crossCorr_hfourth hcard hk hkn hcop hnodd hn a ha) s hs

end Vanish.Foundations.FirstPrinciples
