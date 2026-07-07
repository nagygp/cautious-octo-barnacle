import RequestProject.Foundations.KasamiFrobeniusLift
import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import RequestProject.Foundations.KasamiLegendreValuation
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-6: the Gross–Koblitz value (`hGKval`)

This module is the **sixth from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-5 (`KasamiFrobeniusLift.lean`) and the divisibility assembly
(`KasamiGrossKoblitzDivisibility.lean`).

This is the core **A-fp-6**: the Gross–Koblitz value `v₂(R(s)) = s₂(e s)`, which
discharges the named hypothesis `hGKval` of `KasamiGrossKoblitzDivisibility.lean`.
It is assembled from the two irreducible inputs of the Gross–Koblitz route,
together with the elementary passage `e = 1` (the unramified prime A-fp-3) that
identifies the `𝔭`-valuation with the rational `2`-adic valuation:

* **the Gauss-sum identification** `hgauss` — the cross-correlation `R(s)` is, up to
  sign, the Gauss sum `g(ω^{-s}, ψ)` (a Frobenius substitution rewrites the Kasami
  character sum as the Teichmüller-indexed Gauss sum); and
* **the Gross–Koblitz / Stickelberger valuation** `hGK` —
  `v₂(g(ω^{-s})) = s₂(e s)`, the explicit `p`-adic Γ formula.

The reduction is then pure valuation algebra: the `2`-adic valuation is
sign-insensitive (`padicValInt 2 (−x) = padicValInt 2 x`), so the valuation of
`R(s) = ±g(ω^{-s})` is the valuation of the Gauss sum, which `hGK` reads as the
digit sum.  This is exactly the `hGKval` premise consumed downstream
(`grossKoblitz_hGKval`).

## Results

* `grossKoblitz_hGKval` — from the Gauss-sum identification and the Gross–Koblitz
  valuation, the `hGKval` premise of input (A): `padicValInt 2 (R(s)) = s₂(e s)`
  for all non-zero frequencies.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the `e = 1` valuation reduction;
the two inputs (the Frobenius-substitution Gauss-sum identification and the
explicit Gross–Koblitz `p`-adic Γ formula) are the deep number-theoretic cores,
carried as named hypotheses rather than axioms or `sorry`.

## Sources

Gross–Koblitz, *Gauss sums and the p-adic Γ-function* (Ann. Math. 1979);
Ireland–Rosen, Ch. 14; Washington, *Cyclotomic Fields*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-
**The `2`-adic valuation is sign-insensitive.**  `padicValInt 2 (−x) = padicValInt 2 x`.
-/
theorem padicValInt_two_neg (x : ℤ) : padicValInt 2 (-x) = padicValInt 2 x := by
  simp +decide [ padicValInt ]

/-
**The Gross–Koblitz value `hGKval`, from the Gauss-sum identification.**  If the
cross-correlation `R(s)` is, up to sign, the Gauss sum value `g s`
(`hgauss`), and the Gross–Koblitz formula reads its `2`-adic valuation as the
binary digit sum `s₂(e s)` (`hGK`), then `padicValInt 2 (R(s)) = s₂(e s)` for every
non-zero frequency.  This is the `hGKval` premise consumed by
`kasami_crossCorr_hdiv_of_grossKoblitz`.
-/
theorem grossKoblitz_hGKval {k : ℕ} (a : F) (e : F → ℕ) (g : F → ℤ)
    (hgauss : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a = g s
        ∨ autocorrScaled (fun x : F => x ^ d k) s a = -g s)
    (hGK : ∀ s : F, g s ≠ 0 → padicValInt 2 (g s) = binDigitSum (e s)) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s) := by
  -- By cases on hgauss s, we split into the two possible cases for autocorrScaled s a.
  intro s hs
  cases hgauss s <;> simp_all +decide [ padicValInt_two_neg ]

end Vanish.Foundations