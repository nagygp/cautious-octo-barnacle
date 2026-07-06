import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.FirstPrinciples.FPPadicGamma
import RequestProject.Foundations.FirstPrinciples.FPStickelberger
import RequestProject.Foundations.FirstPrinciples.FPMcEliece
import RequestProject.Foundations.FirstPrinciples.FPInputA
import RequestProject.Foundations.FirstPrinciples.FPSecondDerivative
import RequestProject.Foundations.FirstPrinciples.FPABEnergyValue
import RequestProject.Foundations.FirstPrinciples.FPInputB
import RequestProject.Foundations.FirstPrinciples.FPValueSetUnconditional
import RequestProject.Foundations.FirstPrinciples.FPVanishUnconditional
import RequestProject.Foundations.FirstPrinciples.FPSignSumEval
import RequestProject.Foundations.FirstPrinciples.FPKasamiCount
import RequestProject.Foundations.FirstPrinciples.Decomp
import RequestProject.Foundations.FirstPrinciples.Transcribe

/-!
# `Vanish.Foundations.FirstPrinciples` — the remaining proof-path skeleton

This is the single entry point for the **skeleton tower** that completes the
first-principles proof of the Kasami `m`-tuple / triple count *via vanishing*.

The project's `RequestProject/Foundations/` already reduces "Kasami is Vanish"
(for odd `n`) — through the sorry-free layers documented in
`Docs/VanishFutureDirections.md` — to a small set of **deep cores carried as named
hypotheses**.  This `FirstPrinciples/` tower supplies the *remaining modules*: it
states, bottom-up, every lemma and every piece of new theory still needed to
discharge those cores from scratch, with all genuinely deep leaves `sorry`-blocked
and all wiring done by real proofs.  Building these out (filling the `sorry`s) is a
multi-session effort; the scaffold pins down exactly what must be proved and how it
composes into the headline counts.

## The DAG (bottom → top)

```
   Core (A)  Gross–Koblitz / Stickelberger / McEliece  ⟹  input (A) divisibility
   ----------------------------------------------------------------------------
   FPGaussSumSetup     hgauss : R(s) = ±g(ω^{-e(s)})           (Frobenius substitution)   [sorry]
   FPPadicGamma        Morita's Γ_p over ℤ_[p]                 (the transcendental object) [sorry]
   FPStickelberger     hGK   : v₂(g(s)) = s₂(e(s))             (Gross–Koblitz value)       [sorry]
   FPMcEliece          hfact : v₂((e s)!) ≤ e s − (n+1)/2      (Ax–Katz / McEliece)        [sorry]
   FPInputA            hdiv  : 2^{(n+1)/2} ∣ R(s)              (assembly, real proof)

   Core (B)  almost-bent additive energy  ⟹  input (B) fourth moment
   ----------------------------------------------------------------------------
   FPSecondDerivative  ∑_{z≠0} derivPairCount² = q³ − 2q²      (AB multiplicities)         [sorry]
   FPABEnergyValue     16·E = q³ + 2q²  and  hWK               (assembly, real proof)
   FPInputB            hfourth : ∑_{s≠0} R(s)⁴ = 2q³           (assembly, real proof)

   Assembly  value set ⟹ Vanish ⟹ count
   ----------------------------------------------------------------------------
   FPValueSetUnconditional   R(s) ∈ {q,0,±2^{(n+1)/2}}         (real proof from A,B)
   FPVanishUnconditional     Vanish ⟺ ∑_{t≠0} ∏ σ(t·c_i) = 0  (real proof)
   FPSignSumEval             explicit admissible class          (Layer-12 frontier)        [sorry]
   FPKasamiCount             imgCount m (·^{d k}) a c = 2^{(m-1)n−m}, triple = 2^{2n−3}
```

## The headline targets

* `FirstPrinciples.kasami_mtuple_count_firstPrinciples` — the general-`k`,
  general-`m` count `2^{(m-1)n − m}` for any tuple with vanishing sign correlation;
* `FirstPrinciples.kasami_triple_count_firstPrinciples` — the `m = 3` count
  `2^{2n − 3}` on the explicit admissible class.

## The remaining `sorry` leaves (the genuine open cores)

Each `FirstPrinciples` core has been **expanded bottom-up** in the companion
decomposition library `RequestProject.Foundations.FirstPrinciples.Decomp` (see
`Decomp.lean`).  There, every deep core is reduced — by real-proof wiring — to a
handful of *atomic* leaves, and many of those leaves are now discharged.  The FP
cores `FPStickelberger.gaussSum_grossKoblitz_factor`,
`FPMcEliece.{axKatz_two_pow_dvd, kasami_exp_factorial_bound, kasami_exp_ge}`,
`FPSecondDerivative.kasami_derivPairCount_sq_offDiag`, `FPPadicGamma` (all 7
properties) and `FPSignSumEval.{KasamiAdmissibleClass, kasami_signCorr_closed_form}`
now delegate to the decomposition (the last is **fully proved**).

The genuinely classical leaves that remain (each a single named statement, no
subtheory hidden behind it) are, in `Decomp`:

* **(A) Gross–Koblitz**: `StickelbergerDecomp.kasamiGaussInt_factor_two_pow`;
  `GaussSumDecomp.kasami_crossCorr_eq_gaussInt` (final bridge); Morita Γ_p in
  `PadicGammaDecomp` (the convergence core `padicFactorialTrunc_converges` and the
  limit-passing properties).
* **(A) Ax–Katz / McEliece**: `AxKatzDecomp.axKatz_two_pow_dvd`,
  `AxKatzDecomp.kasami_exp_digitSum_lower_bound`.
* **(B)** `SecondDerivativeDecomp.kasami_derivQuadrupleCount`.
* **Setup defs** `FPGaussSumSetup.{kasamiExp, kasamiGaussInt}` (the discrete-log /
  integer-Gauss-sum objects; `GaussSumDecomp.kasamiDiscreteLog` is the real
  building block).

## Why no equation-(12)/DD route here

The Dillon–Dobbertin equation-(12) GF(4)-coset average is an intrinsically
**even-`n`** device (it degenerates for odd `n`, per
`Docs/VanishFutureDirections.md` §9: `3 ∤ 2ⁿ − 1` for odd `n`).  Since the Kasami
APN/AB target is the **odd-`n`** regime, the value set is closed here through the
(A)/(B) towers, not through (DD); the DD quadratic-form substrate
(`GoldQuadratic`, `RankSpectrum`, …) is retained in the main `Foundations` tower
as parity-agnostic infrastructure.
-/
