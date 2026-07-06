import RequestProject.Foundations.FirstPrinciples.FPValueSetUnconditional
import RequestProject.Foundations.KasamiVanishSign
import Mathlib

/-!
# First-principles tower — module fp·s7: `Vanish` as a sign correlation, unconditional

With the value set discharged (`FPValueSetUnconditional.lean`), Layer 12's
sign-correlation reduction becomes **unconditional**: for the Kasami map and
nonzero coefficients,

```
   Vanish m (·^{d k}) a c   ⟺   ∑_{t≠0} ∏_i σ(t·c_i) = 0           (sign correlation)
```

and at `m = 3`

```
   AdmissibleTriple n (·^{d k}) a c   ⟺   ∑_{t≠0} ∏_i σ(t·c_i) = 0 .
```

These remove the `hdiv`/`hfourth` hypotheses of
`KasamiVanishSign.kasami_vanish_iff_sign_sum` /
`kasami_admissible_iff_sign_sum` by feeding the from-scratch discharges of
`FPInputA`/`FPInputB`.  They are the explicit, elementary admissibility predicate
(the sign correlation `σ`), now resting only on the deep leaves of the (A)/(B)
towers.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); Carlet, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Unconditional `Vanish` ⟺ sign correlation (general `m`).** -/
theorem kasami_vanish_iff_signSum {n k m : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0) :
    Vanish m (fun x : F => x ^ d k) a c
      ↔ ∑ t ∈ univ.erase (0 : F),
          ∏ i : Fin m,
            Vanish.Foundations.crossCorrSign (fun x : F => x ^ d k) a ((n + 1) / 2) (t * c i)
        = 0 :=
  Vanish.Foundations.kasami_vanish_iff_sign_sum hcard hk hkn hcop hnodd hn a ha c hc
    (kasami_crossCorr_hdiv hcard hk hkn hcop hnodd a ha)
    (kasami_crossCorr_hfourth hcard hk hkn hcop hnodd hn a ha)

/-- **Unconditional admissibility ⟺ sign correlation (`m = 3`).**  The explicit
general-`k` analogue of `cube_admissible_iff`. -/
theorem kasami_admissible_iff_signSum {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0) :
    AdmissibleTriple n (fun x : F => x ^ d k) a c
      ↔ ∑ t ∈ univ.erase (0 : F),
          ∏ i : Fin 3,
            Vanish.Foundations.crossCorrSign (fun x : F => x ^ d k) a ((n + 1) / 2) (t * c i)
        = 0 :=
  Vanish.Foundations.kasami_admissible_iff_sign_sum hcard hk hkn hcop hnodd hn a ha c hc
    (kasami_crossCorr_hdiv hcard hk hkn hcop hnodd a ha)
    (kasami_crossCorr_hfourth hcard hk hkn hcop hnodd (by omega) a ha)

end Vanish.Foundations.FirstPrinciples
