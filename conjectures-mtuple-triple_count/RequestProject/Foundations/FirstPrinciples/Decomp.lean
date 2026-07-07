import RequestProject.Foundations.FirstPrinciples.Decomp.GaussWilson
import RequestProject.Foundations.FirstPrinciples.Decomp.PadicGammaDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.GaussSumDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.StickelbergerDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.AxKatzDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.SecondDerivativeDecomp
import RequestProject.Foundations.FirstPrinciples.Decomp.AdmissibleClassDecomp

/-!
# `Vanish.Foundations.FirstPrinciples.Decomp` — exhaustive bottom-up decomposition

This is the entry point for the **decomposition library** that expands every deep
core `sorry` of the `FirstPrinciples/` tower into a fully bottom-up skeleton: each
remaining `sorry` is a single, faithfully-stated, self-contained statement (an
atomic leaf), with the assembly into the corresponding `FirstPrinciples` core done
by real proofs wherever the composition is elementary, and the genuinely classical
inputs isolated as individually-named leaves (no `sorry` hiding a whole subtheory).

## Module map (core → decomposition module)

| `FirstPrinciples` core (deep `sorry`) | decomposition module | new atomic leaves |
| --- | --- | --- |
| `FPGaussSumSetup.kasami_crossCorr_eq_gaussInt` | `GaussSumDecomp` | discrete-log defn + fibre-count / monomial-sum / final bridge leaves |
| `FPPadicGamma.padicGamma` (+7 props) | `PadicGammaDecomp` | real truncated-factorial defn + recurrence / convergence / limit-passing leaves |
| `FPStickelberger.gaussSum_grossKoblitz_factor` | `StickelbergerDecomp` | integer Gross–Koblitz factorization leaf + real valuation arithmetic |
| `FPMcEliece.{axKatz_two_pow_dvd, kasami_exp_factorial_bound, kasami_exp_ge}` | `AxKatzDecomp` | Ax–Katz leaf + digit-sum bound leaf + real arithmetic assembly |
| `FPSecondDerivative.kasami_derivPairCount_sq_offDiag` | `SecondDerivativeDecomp` | quadruple-count leaf + real diagonal-separation assembly |
| `FPSignSumEval.{KasamiAdmissibleClass, kasami_signCorr_closed_form}` | `AdmissibleClassDecomp` | **fully closed**: real elementary class defn + real closed-form proof |

## The remaining atomic leaves (what is left to fill)

* **p-adic Γ** (`PadicGammaDecomp`): `padicFactorialTrunc_succ_unit_step`,
  `padicFactorialTrunc_succ_nonunit_step`, `padicFactorialTrunc_isUnit`,
  `padicFactorialTrunc_converges` (the one analytic existence core), plus the
  limit-passing steps `padicGamma_natCast`, `padicGamma_continuous`,
  `padicGamma_succ_unit`, `padicGamma_succ_nonunit`, `padicGamma_unit`,
  `padicGamma_reflection`.
* **Gauss-sum identification** (`GaussSumDecomp`): `kasamiDiscreteLog_spec`,
  `powerMap_fibreCount`, and the final bridge `kasami_crossCorr_eq_gaussInt`.
* **Gross–Koblitz** (`StickelbergerDecomp`): `kasamiGaussInt_factor_two_pow` (the
  integer factorization) and `padicValInt_two_pow_mul_odd`.
* **Ax–Katz / McEliece** (`AxKatzDecomp`): `axKatz_two_pow_dvd` and
  `kasami_exp_digitSum_lower_bound`.
* **AB second moment** (`SecondDerivativeDecomp`):
  `derivPairCount_sq_sum_eq_quadruple` and `kasami_derivQuadrupleCount`.
* **Layer 12** (`AdmissibleClassDecomp`): **fully discharged** — the elementary
  admissible class and the closed-form evaluation are real definitions and real
  proofs, with no remaining `sorry`.

Every remaining `sorry` above is a single named classical statement; none packages
a further deep subtheory behind one `sorry`.  The remaining leaves are exactly the
genuinely classical inputs absent from Mathlib (Ax–Katz divisibility, the integer
Gross–Koblitz factorization, Morita's `Γ_p` convergence and its limit-passing
properties, the finite-field fibre-count / Gauss-sum bridge, the McEliece digit-sum
lower bound, and the almost-bent quadruple count).
-/
