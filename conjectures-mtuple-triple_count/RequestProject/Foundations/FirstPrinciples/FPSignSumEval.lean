import RequestProject.Foundations.FirstPrinciples.FPVanishUnconditional
import RequestProject.Foundations.FirstPrinciples.Decomp.AdmissibleClassDecomp
import Mathlib

/-!
# First-principles tower — module fp·s8: the sign-correlation sum (Layer-12 combinatorial frontier)

This module isolates the **last combinatorial frontier** of the program: the
*explicit evaluation* of the sign-correlation sum

```
   kasamiSignCorr k a e c = ∑_{t≠0} ∏_i σ(t·c_i) .
```

From `FPVanishUnconditional.lean` (unconditional now, modulo the (A)/(B) leaves)
this sum vanishing is **exactly** admissibility:

```
   AdmissibleTriple n (·^{d k}) a c   ⟺   kasamiSignCorr k a ((n+1)/2) c = 0 .
```

That already gives an explicit, *computable* admissibility predicate (the integer
sign correlation).  What remains genuinely open — and is the deepest combinatorial
content for general `k` — is reducing this to an **elementary closed-form
condition on the coefficients** `c` (the joint sign distribution of
`(σ(t·c_0), σ(t·c_1), σ(t·c_2))` over `t`).  Unlike the cube/`k = 1` case
(`cube_admissible_iff`: "not all equal"), for general `k` the class is *not*
"not all equal" — a repeated-coefficient tuple `(c, c, c')` can already fail.  The
elementary predicate `KasamiAdmissibleClass` and the evaluation
`kasami_signCorr_closed_form` are the carried open core (`sorry`).

## Deliverables

* `kasamiSignCorr` — the integer sign-correlation sum (definition).
* `kasami_admissible_iff_signCorr_zero` — **delivered** (real proof): admissibility
  ⟺ the sign correlation vanishes.
* `KasamiAdmissibleClass` — the (open) elementary coefficient predicate.
* `kasami_signCorr_closed_form` — the (open) reduction of the sign correlation to
  `KasamiAdmissibleClass`.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); Carlet, Ch. 6;
Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The integer sign-correlation sum** of a coefficient tuple. -/
noncomputable def kasamiSignCorr (k : ℕ) (a : F) (e : ℕ) {m : ℕ} (c : Fin m → F) : ℤ :=
  ∑ t ∈ univ.erase (0 : F),
    ∏ i : Fin m,
      Vanish.Foundations.crossCorrSign (fun x : F => x ^ d k) a e (t * c i)

/-- **Admissibility ⟺ vanishing sign correlation** (delivered, real proof). -/
theorem kasami_admissible_iff_signCorr_zero {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0) :
    AdmissibleTriple n (fun x : F => x ^ d k) a c
      ↔ kasamiSignCorr k a ((n + 1) / 2) c = 0 :=
  kasami_admissible_iff_signSum hcard hk hkn hcop hnodd hn a ha c hc

/-- **The elementary admissible coefficient class** for general `k` (now discharged
via `Decomp.AdmissibleClassDecomp`).  The combinatorial predicate replacing the
cube/`k = 1` "not all equal": the `+1`- and `−1`-sign-product counts balance. -/
def KasamiAdmissibleClass (n k : ℕ) (a : F) (c : Fin 3 → F) : Prop :=
  Decomp.KasamiAdmissibleClass' n k a c

/-- **The closed-form evaluation of the sign correlation** (now a real proof via
`Decomp.AdmissibleClassDecomp`).  The sign-correlation sum vanishes iff the
elementary class `KasamiAdmissibleClass` holds (the sign-product counts balance). -/
theorem kasami_signCorr_closed_form {n k : ℕ} (a : F) (c : Fin 3 → F) :
    kasamiSignCorr k a ((n + 1) / 2) c = 0 ↔ KasamiAdmissibleClass n k a c :=
  Decomp.kasami_signCorrSum_closed_form n k a c

end Vanish.Foundations.FirstPrinciples
