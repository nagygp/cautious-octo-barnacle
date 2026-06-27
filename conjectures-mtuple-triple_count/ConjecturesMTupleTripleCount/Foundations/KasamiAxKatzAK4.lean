import ConjecturesMTupleTripleCount.Foundations.KasamiAxKatzAK3b
import ConjecturesMTupleTripleCount.Foundations.KasamiTwoAdicValuation
import Mathlib

/-!
# Foundations, Layer AK4 — the CCD specialization to the Kasami exponent `d k` closes input (A)

This module implements the **fourth and final layer of the Ax–Katz / McEliece
sub-path for input (A)** laid out in `Docs/VanishFutureDirections.md` §7.

Layers AK1–AK3 built the route up to Stickelberger's valuation: the binary
digit-sum engine (AK1/AK2), the Gauss-sum toolkit and the local-valuation
framework at the prime above `2` (AK3/AK3.1/AK3.2), and the `|g|² = q` valuation
constraint (AK3.3).  The **deep core** — Stickelberger's individual valuation
`v(g(ω^{-s})) = s₂(s)` — together with the Canteaut–Charpin–Dobbertin (CCD)
weight-divisibility computation pins the `2`-adic valuation of the Kasami
cross-correlation `R(s)` from below.  This module supplies the **final
specialization**: how that valuation lower bound discharges input **(A)**, the
divisibility hypothesis `hdiv` of `kasami_crossCorr_value_set`.

## What is established (sorry-free)

1. **The valuation-to-divisibility bridge.**  For integers, a lower bound on the
   `2`-adic valuation is exactly a power-divisibility:
   `(n+1)/2 ≤ v₂(z) ⟹ 2^{(n+1)/2} ∣ z` (`int_two_pow_dvd_of_le_padicValInt`),
   handling the degenerate `z = 0` case (where every power divides `0`).  This is
   the bookkeeping that converts Stickelberger's additive valuation statement
   into the multiplicative divisibility `hdiv` speaks of.

2. **The Kasami digit-sum input.**  `s₂(d k) = k + 1` for the Kasami exponent
   `d k = 2^{2k} − 2^k + 1` (`kasami_binDigitSum_exponent`, from AK2) — the
   concrete combinatorial number the CCD computation feeds into the McEliece /
   Stickelberger valuation.

3. **The AK4 reduction (input (A) from the CCD valuation bound).**
   `kasami_crossCorr_hdiv_of_valuation`: if every *non-zero* Kasami
   cross-correlation value `R(s)` has `2`-adic valuation at least `(n+1)/2` — the
   CCD / Stickelberger output — then `2^{(n+1)/2} ∣ R(s)` for **all** `s`, which
   is exactly `hdiv`.  The zero frequencies are divided automatically, so the
   only content is the valuation bound on the spectrum, supplied by the deep
   core.

## Scope

This layer is sorry-free.  It provides the **final reduction** of input (A) to
the CCD / Stickelberger `2`-adic valuation lower bound on the cross-correlation
spectrum, stated as the explicit hypothesis `hval` (matching the project's
convention of carrying the still-open deep inputs as named hypotheses rather than
axioms).  The bound `hval` itself — the Canteaut–Charpin–Dobbertin specialization
of Stickelberger's congruence `v(g(ω^{-s})) = s₂(s)` to `d k` — is the open deep
core (AK3.3 / CCD), **absent from Mathlib**, deliberately neither axiomatized nor
`sorry`-ed.  Note that the quadratic Kasami exponents `k ≤ 2` already have `hdiv`
discharged **unconditionally** by the radical/valuation route of Layer A2
(`kasami_one_crossCorr_hdiv`, `kasami_two_crossCorr_hdiv`); AK4 is the route for
the genuinely non-quadratic exponents `k ≥ 3`.

## Sources

Canteaut–Charpin–Dobbertin, *Weight divisibility of cyclic codes, highly
nonlinear functions on GF(2ᵐ), and crosscorrelation of maximum-length sequences*
(SIAM J. Discrete Math., 2000); McEliece, *Weight congruences for p-ary cyclic
codes* (Discrete Math., 1972); Ireland–Rosen, Ch. 14.
-/

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The valuation-to-divisibility bridge -/

/-
**Valuation lower bound ⟹ power divisibility.**  For an integer `z`, a lower
bound `m ≤ v₂(z)` on its `2`-adic valuation is exactly the divisibility
`2^m ∣ z`; the degenerate case `z = 0` is divided by every power.
-/
theorem int_two_pow_dvd_of_le_padicValInt {m : ℕ} {z : ℤ}
    (h : m ≤ padicValInt 2 z) : (2 : ℤ) ^ m ∣ z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hz : z = 0
  · simp [hz]
  · have : ((2 : ℕ) : ℤ) ^ m ∣ z := (padicValInt_dvd_iff m z).2 (Or.inr h)
    simpa using this

/-! ## 2. The Kasami digit-sum input -/

/-
**The Kasami-exponent digit sum** `s₂(d k) = k + 1` (from AK2,
`binDigitSum_kasami_exponent`) — the combinatorial number the CCD / McEliece
valuation reads off the Kasami exponent.
-/
theorem kasami_binDigitSum_exponent (k : ℕ) :
    binDigitSum (CollisionAnalysis.d k) = k + 1 :=
  binDigitSum_kasami_exponent k

/-! ## 3. The AK4 reduction: input (A) from the CCD valuation bound -/

/-
**Input (A) from the CCD / Stickelberger valuation bound.**  If every non-zero
Kasami cross-correlation value `R(s)` has `2`-adic valuation at least `(n+1)/2`
(the Canteaut–Charpin–Dobbertin output, specializing Stickelberger's
`v(g(ω^{-s})) = s₂(s)` to `d k`), then `2^{(n+1)/2} ∣ R(s)` for **all** `s` —
exactly the hypothesis `hdiv` of `kasami_crossCorr_value_set`.  Zero frequencies
are divided automatically.
-/
omit [DecidableEq F] in
theorem kasami_crossCorr_hdiv_of_valuation {n k : ℕ} (a : F)
    (hval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a)) :
    ∀ s : F, (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled (fun x : F => x ^ d k) s a := by
  intro s
  by_cases hz : autocorrScaled (fun x : F => x ^ d k) s a = 0
  · simp [hz]
  · exact int_two_pow_dvd_of_le_padicValInt (hval s hz)

end Vanish.Foundations
