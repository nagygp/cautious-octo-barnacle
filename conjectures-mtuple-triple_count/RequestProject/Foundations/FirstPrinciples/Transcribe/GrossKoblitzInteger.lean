import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.GrossKoblitzValuation
import RequestProject.Foundations.FirstPrinciples.Decomp.StickelbergerDecomp

/-!
# Transcription — Leaf L3, module 3: descending to the integer Gauss-sum factorization

This is the **third and final rung** of the integer Gross–Koblitz factorization
(leaf **L3** in `FirstPrinciplesTranscriptionRoadmap.md`), assembling
`Transcribe/GrossKoblitzStatement.lean` (module 1, the integer factorization
reduction) and `Transcribe/GrossKoblitzValuation.lean` (module 2, the valuation
extraction) to discharge the shape of the `Decomp` leaf
`StickelbergerDecomp.kasamiGaussInt_factor_two_pow`.

The genuine deep input remaining is the **Gross–Koblitz `2`-adic identity for the
Kasami Teichmüller Gauss sum**: that, over `ℤ₂`,
`(g(s) : ℤ₂) = (−1)^{s₂(e(s))} · 2^{s₂(e(s))} · u` for a unit `u` (the `Γ_p`-factor
product, `GrossKoblitzStatement.padicGamma_prod_isUnit`, times the sign).  This
module carries that identity as the single hypothesis `hGK` and proves, as a **real
proof**, the integer factorization `g(s) = ± 2^{s₂(e(s))} · odd` — exactly the
conclusion of `kasamiGaussInt_factor_two_pow`.  Thus once the `2`-adic identity is
supplied for `kasamiGaussInt`, the `Decomp` leaf is discharged from first principles.

The abstraction is faithful to the Gross–Koblitz formula: the `π^{s₂(e)}` prefactor
carries the whole valuation (module 2) and the `Γ_p`-product is a unit (module 1),
so the descent to `ℤ` is the elementary `2`-adic argument proved in module 1.

## Sources

* B. Gross, N. Koblitz, *Gauss sums and the p-adic Γ-function*, Ann. of Math. 109
  (1979), 569–581.
* L. Washington, *Introduction to Cyclotomic Fields*, Ch. 6.
* Project: `StickelbergerDecomp.kasamiGaussInt_factor_two_pow` (the `Decomp` leaf).
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open Vanish.Foundations.FirstPrinciples.Decomp WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The integer Gross–Koblitz factorization, from the `2`-adic identity (real
proof).**  Carrying the Gross–Koblitz `2`-adic identity for the Kasami Teichmüller
Gauss sum as the hypothesis `hGK` — namely
`(g(s) : ℤ₂) = (−1)^{s₂(e(s))} · 2^{s₂(e(s))} · u` with `u` a unit (the `Γ_p`-factor
product times the sign) — the integer Gauss sum factors as `± 2^{s₂(e(s))} · odd`.
This is exactly the conclusion of `StickelbergerDecomp.kasamiGaussInt_factor_two_pow`;
it is discharged here by the module-1 reduction `gaussInt_factor_of_padic_grossKoblitz`
once the `2`-adic identity is available.  (The full Kasami regime hypotheses of the
`Decomp` leaf are not needed for this descent — only the `2`-adic identity is — so
they are omitted, giving a cleaner reduction.) -/
theorem kasamiGaussInt_factor_two_pow_of_padic (k : ℕ) (a : F) (s : F)
    (u : ℤ_[2]) (hu : IsUnit u)
    (hGK : ((kasamiGaussInt k a s : ℤ) : ℤ_[2])
        = (-1) ^ (binDigitSum (kasamiExp k a s))
            * 2 ^ (binDigitSum (kasamiExp k a s)) * u) :
    ∃ m : ℤ, Odd m ∧
      (kasamiGaussInt k a s = 2 ^ (binDigitSum (kasamiExp k a s)) * m
        ∨ kasamiGaussInt k a s = -(2 ^ (binDigitSum (kasamiExp k a s)) * m)) :=
  gaussInt_factor_of_padic_grossKoblitz (kasamiGaussInt k a s)
    (binDigitSum (kasamiExp k a s)) u hu hGK

end Vanish.Foundations.FirstPrinciples.Transcribe
