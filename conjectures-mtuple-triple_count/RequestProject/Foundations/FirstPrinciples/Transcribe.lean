import RequestProject.Foundations.FirstPrinciples.Transcribe.GaussSumModulus
import RequestProject.Foundations.FirstPrinciples.Transcribe.MulCharDual
import RequestProject.Foundations.FirstPrinciples.Transcribe.MonomialGaussExpansion
import RequestProject.Foundations.FirstPrinciples.Transcribe.FrobeniusPowSubstitution
import RequestProject.Foundations.FirstPrinciples.Transcribe.TraceMonomial
import RequestProject.Foundations.FirstPrinciples.Transcribe.GaussSumBridge
import RequestProject.Foundations.FirstPrinciples.Transcribe.KasamiMonomialCollapseDisproof
import RequestProject.Foundations.FirstPrinciples.Transcribe.AutocorrCharSumBound
import RequestProject.Foundations.FirstPrinciples.Transcribe.GrossKoblitzStatement
import RequestProject.Foundations.FirstPrinciples.Transcribe.GrossKoblitzValuation
import RequestProject.Foundations.FirstPrinciples.Transcribe.GrossKoblitzInteger
import RequestProject.Foundations.FirstPrinciples.Transcribe.FiniteFieldPowerSum
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzCountingCongruence
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzChevalleyWarning
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzReduction
import RequestProject.Foundations.FirstPrinciples.Transcribe.AxKatzIterated
import RequestProject.Foundations.FirstPrinciples.Transcribe.McElieceWeightCongruence
import RequestProject.Foundations.FirstPrinciples.Transcribe.KasamiCosetDigitSum
import RequestProject.Foundations.FirstPrinciples.Transcribe.AdditiveEnergyWalsh
import RequestProject.Foundations.FirstPrinciples.Transcribe.ABFourthMoment
import RequestProject.Foundations.FirstPrinciples.Transcribe.KasamiQuadrupleCount

/-!
# `Vanish.Foundations.FirstPrinciples.Transcribe` — first-principles transcription, started

This is the entry point for the **transcription tower** that builds the remaining
classical inputs of the Kasami m-tuple / triple count *from textbook sources rooted
in Mathlib*, following `FirstPrinciplesTranscriptionRoadmap.md`.

The roadmap maps each of the five remaining `Decomp` leaves to an ordered sequence
of Mathlib-rooted modules.  This tower holds the **first few** of those modules (the
most Mathlib-ready opening rungs of leaves L1 and L4):

| module | leaf | content | status |
| --- | --- | --- | --- |
| `Transcribe/GaussSumModulus` | L1 | Gauss-sum modulus / Jacobi theory (Lidl–Niederreiter §5.2) | **sorry-free** |
| `Transcribe/MulCharDual` | L1 | dual orthogonality `∑ χ₁ʲ(y) = #{x | xᵐ=y}` on `Fˣ` | **sorry-free** |
| `Transcribe/MonomialGaussExpansion` | L1 | monomial → Gauss-sum expansion (Thm 5.30) | **sorry-free** |
| `Transcribe/TraceMonomial` | L1 | Kasami trace → monomial substitution (`chiC`, cast id real; substitution leaf) | wiring real; substitution leaf |
| `Transcribe/GaussSumBridge` | L1 | full Gauss-sum expansion of `R(s)` (real) + single-coset collapse leaf | expansion real; collapse leaf |
| `Transcribe/GrossKoblitzStatement` | L3 | `Γ_p`-unit product theory + Gross–Koblitz → integer factorization reduction | **sorry-free** |
| `Transcribe/AxKatzChevalleyWarning` | L4 | Ax–Katz base from Chevalley–Warning + iterated leaf | base real; iterated leaf |

Thus the **entire analytic heart of leaf L1** (the additive→multiplicative
character-sum bridge: the monomial → Gauss-sum expansion together with the dual
orthogonality / fibre count on `Fˣ`) is now proved from first principles, rooted
only in Mathlib's `gaussSum`, `MulChar`, `AddChar`, and `IsCyclic` API.  Modules 4–5
(`TraceMonomial`, `GaussSumBridge`) then wire this analytic heart into the Kasami
cross-correlation itself: the `ℂ`-valued sign character `chiC`, its primitivity, the
cast identity `(R_a(s) : ℂ) = ∑_x chiC(s·Δf_a x)`, and — as a genuinely new real
proof — the **full Gauss-sum expansion** `(R_a(s) : ℂ) = ∑_{j} (χ₁ʲ)⁻¹(c)·g(χ₁ʲ,chiC)`
(`GaussSumBridge.kasami_autocorr_eq_gaussSum_sum`).  The remaining `sorry` leaves are
the genuinely deep classical inputs: the Kasami Frobenius/trace → *single monomial*
substitution (`TraceMonomial.kasami_autocorr_eq_monomial_addCharSum`), the
Stickelberger/cyclotomic-coset single-coset collapse to `±` one Gauss sum
(`GaussSumBridge.kasami_autocorr_eq_pm_single_gaussSum`), and the iterated Ax–Katz
`2^μ`-divisibility (`AxKatzChevalleyWarning.axKatz_two_pow_dvd_iterated`).

For leaf **L3** (Gross-Koblitz), `GrossKoblitzStatement` is the first rung (the next
chapter after L2): it packages the `Gamma_p`-unit product theory (real) and proves
the **real reduction** `gaussInt_factor_of_padic_grossKoblitz`: the Gross-Koblitz
`2`-adic identity implies the integer `± 2^c · odd` factorization, leaving only
the Gross-Koblitz identity itself (abstracted into that lemma's hypothesis) as the
deep input.

The remaining modules in each leaf's sequence (and leaves L5, L6, plus the deeper
rungs of L3) are described in the roadmap; they are subsequent transcription work.
-/
