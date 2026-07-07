import RequestProject.Foundations.FirstPrinciples.FPSignSumEval
import RequestProject.Foundations.KasamiMTupleCount
import Mathlib

/-!
# First-principles tower — module fp·s9: the unconditional Kasami `m`-tuple / triple count

This **capstone** assembles the whole first-principles tower into the headline
counts, the general-`k` analogues of Layer 8's cube results:

```
   imgCount m (·^{d k}) a c = 2^{(m-1)n − m}      (kasami_mtuple_count_firstPrinciples)
   imgCount 3 (·^{d k}) a c = 2^{2n − 3}          (kasami_triple_count_firstPrinciples)
```

The path is now entirely assembled (every step a real proof) down to a handful of
deep leaves carried as `sorry` in the lower modules:

* the sign correlation `kasamiSignCorr` vanishing ⟺ `Vanish`
  (`FPVanishUnconditional`, unconditional via the (A)/(B) towers);
* `Vanish` + Kasami-APN ⟹ the count (`KasamiMTupleCount`, already sorry-free);
* the explicit admissibility class `KasamiAdmissibleClass` and the sign-correlation
  closed form (`FPSignSumEval`, open Layer-12 frontier).

So the `m`-tuple count holds for any tuple whose sign correlation vanishes
(`kasami_mtuple_count_firstPrinciples`), and the triple count holds on the
explicit admissible class (`kasami_triple_count_firstPrinciples`).

## Sources

Kasami (1971); Chabaud–Vaudenay §3; MacWilliams–Sloane (Pless power moments).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The general-`k`, general-`m` Kasami `m`-tuple count (sign-correlation form).**
For nonzero coefficients whose sign correlation vanishes, the image `m`-tuple count
of the Kasami map is `2^{(m-1)n − m}`. -/
theorem kasami_mtuple_count_firstPrinciples {n k m : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hsign : kasamiSignCorr k a ((n + 1) / 2) c = 0) :
    imgCount m (fun x : F => x ^ d k) a c = 2 ^ ((m - 1) * n - m) := by
  have hv : Vanish m (fun x : F => x ^ d k) a c :=
    (kasami_vanish_iff_signSum hcard hk hkn hcop hnodd (by omega) a ha c hc).mpr hsign
  exact Vanish.Foundations.kasami_mtuple_count hcard hk hkn hcop hnodd hn hm a ha c hv

/-- **The general-`k` Kasami triple count (explicit admissible class).**  For a
nonzero coefficient triple in the explicit admissible class
`KasamiAdmissibleClass`, the image triple count of the Kasami map is `2^{2n−3}`. -/
theorem kasami_triple_count_firstPrinciples {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0)
    (hadm : KasamiAdmissibleClass n k a c) :
    imgCount 3 (fun x : F => x ^ d k) a c = 2 ^ (2 * n - 3) := by
  have hsign : kasamiSignCorr k a ((n + 1) / 2) c = 0 :=
    (kasami_signCorr_closed_form a c).mpr hadm
  have hadm' : AdmissibleTriple n (fun x : F => x ^ d k) a c :=
    (kasami_admissible_iff_signCorr_zero hcard hk hkn hcop hnodd hn a ha c hc).mpr hsign
  exact Vanish.Foundations.kasami_triple_count hcard hk hkn hcop hnodd hn a ha c hadm'

end Vanish.Foundations.FirstPrinciples
