import RequestProject.Foundations.KasamiAxKatzAK4
import RequestProject.Foundations.KasamiGrossKoblitz
import Mathlib

/-!
# Foundations — Input (A): Gross–Koblitz value + digit-sum bound ⟹ the divisibility

This module **transcribes the next step of direction (A)**: it assembles the two
pieces named in the roadmap into the cross-correlation divisibility
`2^{(n+1)/2} ∣ R(s)` (input (A) of the value-set program).

The two inputs, carried as named hypotheses (the genuine deep cores, exactly as in
`KasamiGrossKoblitz.lean`):

* **the Gross–Koblitz value** `hGKval` — the `p`-adic Γ / Stickelberger formula in
  the form `v₂(R(s)) = s₂(e s)`, the `2`-adic valuation of each non-zero
  cross-correlation value read off as the binary digit sum of its Gauss-sum
  exponent `e s` (`binDigitSum`); and
* **the digit-sum bound** `hbound` — the McEliece / CCD combinatorial lower bound
  `(n+1)/2 ≤ s₂(e s)` on those digit sums.

Chaining them gives the valuation bound `(n+1)/2 ≤ v₂(R(s))`
(`kasami_crossCorr_valuation_of_grossKoblitz`), which is exactly the input fed to
the *proven* valuation-to-divisibility bridge `kasami_crossCorr_hdiv_of_valuation`
(AK4) to produce the input-(A) divisibility
`2^{(n+1)/2} ∣ R(s)` for all `s`
(`kasami_crossCorr_hdiv_of_grossKoblitz`).  The zero frequencies are divided
automatically.

## Scope

The assembly is sorry-free.  The Gross–Koblitz value `hGKval` (the explicit
`p`-adic Γ formula, together with the lift of the residue Frobenius `x ↦ x²` to
the cyclotomic automorphism) and the digit-sum lower bound `hbound` remain the
deep cores, carried as named hypotheses rather than axioms or `sorry`.

## Sources

Gross–Koblitz, *Gauss sums and the p-adic Γ-function* (Ann. Math. 1979);
McEliece, *Weight congruences for p-ary cyclic codes* (1972); Canteaut–Charpin–
Dobbertin (IEEE-IT 2000).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## 1. Gross–Koblitz value + digit-sum bound ⟹ valuation bound -/

/-- **The valuation lower bound from Gross–Koblitz and the digit-sum bound.**
Substituting the Gross–Koblitz value `v₂(R(s)) = s₂(e s)` (`hGKval`) into the
digit-sum lower bound `(n+1)/2 ≤ s₂(e s)` (`hbound`) gives the valuation bound
`(n+1)/2 ≤ v₂(R(s))` for every non-zero frequency. -/
theorem kasami_crossCorr_valuation_of_grossKoblitz {n k : ℕ} (a : F)
    (e : F → ℕ)
    (hGKval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s))
    (hbound : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (e s)) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) := by
  intro s hs
  rw [hGKval s hs]
  exact hbound s hs

/-! ## 2. The input-(A) divisibility -/

/-- **Input (A) from Gross–Koblitz and the digit-sum bound.**  The valuation bound
of `kasami_crossCorr_valuation_of_grossKoblitz`, fed to the proven
valuation-to-divisibility bridge `kasami_crossCorr_hdiv_of_valuation` (AK4),
yields the input-(A) divisibility `2^{(n+1)/2} ∣ R(s)` for all `s`. -/
theorem kasami_crossCorr_hdiv_of_grossKoblitz {n k : ℕ} (a : F)
    (e : F → ℕ)
    (hGKval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s))
    (hbound : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (e s)) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled (fun x : F => x ^ d k) s a :=
  kasami_crossCorr_hdiv_of_valuation a
    (kasami_crossCorr_valuation_of_grossKoblitz a e hGKval hbound)

end Vanish.Foundations
