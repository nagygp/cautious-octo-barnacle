import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.GrossKoblitzStatement

/-!
# Transcription — Leaf L3, module 2: extracting `v₂` from the Gross–Koblitz product

This is the **second rung** of the integer Gross–Koblitz factorization (leaf **L3**
in `FirstPrinciplesTranscriptionRoadmap.md`), continuing
`Transcribe/GrossKoblitzStatement.lean`.

Module 1 packaged the `Γ_p`-unit product theory (every `Γ_p`-factor is a unit, so
the finite product `∏_i Γ_p(⟨…⟩)` is a unit of norm `1`) and gave the integer
factorization reduction.  This module carries out the **valuation extraction**: from
the Gross–Koblitz `2`-adic identity `(g : ℤ₂) = (−1)^c · 2^c · u` (`u` a unit — the
`Γ_p` product times the sign), it reads off the whole `2`-adic content:

* `padicNorm_of_padic_grossKoblitz` — `‖(g : ℤ₂)‖ = 2^(−c)` (**real proof**): the
  unit part `(−1)^c · u` has norm `1`, so the norm comes entirely from `2^c`;
* `padicValInt_of_padic_grossKoblitz` — `v₂(g) = c` (**real proof**): the integer
  `2`-adic valuation equals the exponent `c = s₂(e)` of the `π^{s₂(e)}` prefactor.

The `Γ_p`-factors contribute nothing (they are units, `GrossKoblitzStatement`), so
the valuation is exactly the uniformizer exponent — this is the "`v₂(π) = 1`
normalisation, giving `v₂(g) = s₂(e)`" step of the roadmap.  Everything here is real
`padicVal` arithmetic; the genuine deep input (the Gross–Koblitz identity itself)
stays abstracted into the hypothesis, as in module 1.

## Sources

* B. Gross, N. Koblitz, *Gauss sums and the p-adic Γ-function*, Ann. of Math. 109
  (1979), 569–581.
* L. Washington, *Introduction to Cyclotomic Fields*, Ch. 6.
* Project: `PadicGammaDecomp.padicGamma_unit`,
  `Transcribe.gaussInt_factor_of_padic_grossKoblitz`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators

/-
**The `2`-adic norm from the Gross–Koblitz identity (real proof).**  If the
integer Gauss sum satisfies `(g : ℤ₂) = (−1)^c · 2^c · u` with `u` a unit, then its
`2`-adic norm is `2^(−c)`: the unit part `(−1)^c · u` has norm `1`, so the norm
comes entirely from the `2^c` prefactor.
-/
theorem padicNorm_of_padic_grossKoblitz (g : ℤ) (c : ℕ)
    (u : ℤ_[2]) (hu : IsUnit u) (hGK : (g : ℤ_[2]) = (-1) ^ c * 2 ^ c * u) :
    ‖(g : ℤ_[2])‖ = (2 : ℝ) ^ (-c : ℤ) := by
  rw [ hGK, norm_mul, norm_mul, norm_pow ];
  norm_num [ zpow_neg, zpow_natCast ];
  rw [ show ‖ ( 2 : ℤ_[2] )‖ = ( 2 : ℝ ) ⁻¹ from ?_, show ‖u‖ = 1 from ?_ ] ; norm_num;
  · rw [one_div, inv_pow];
  · exact PadicInt.isUnit_iff.mp hu;
  · convert PadicInt.norm_p

/-
**The `2`-adic valuation from the Gross–Koblitz identity (real proof).**  If the
integer Gauss sum satisfies `(g : ℤ₂) = (−1)^c · 2^c · u` with `u` a unit, then its
integer `2`-adic valuation is exactly `c`.  For the Kasami Teichmüller Gauss sum,
`c = s₂(e(s))` is the binary digit sum of the exponent, so this is the
`v₂(g) = s₂(e)` conclusion of Gross–Koblitz.
-/
theorem padicValInt_of_padic_grossKoblitz (g : ℤ) (c : ℕ)
    (u : ℤ_[2]) (hu : IsUnit u) (hGK : (g : ℤ_[2]) = (-1) ^ c * 2 ^ c * u) :
    padicValInt 2 g = c := by
  convert padicNorm_of_padic_grossKoblitz g c u hu hGK using 1;
  rw [ PadicInt.norm_eq_zpow_neg_valuation ];
  · norm_num [ PadicInt.valuation ];
  · aesop

end Vanish.Foundations.FirstPrinciples.Transcribe