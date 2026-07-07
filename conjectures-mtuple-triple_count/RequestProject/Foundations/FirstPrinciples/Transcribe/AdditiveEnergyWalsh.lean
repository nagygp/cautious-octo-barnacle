import Mathlib
import RequestProject.Foundations.KasamiWienerKhinchinBridge
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import RequestProject.Foundations.KasamiAdditiveEnergyBE3
import RequestProject.Core.KasamiAB

/-!
# Transcription — Leaf L6, module 1: the Wiener–Khinchin energy bridge

This is the **first rung** of the almost-bent quadruple count (leaf **L6** in
`FirstPrinciplesTranscriptionRoadmap.md`), whose goal (with modules 2–3,
`ABFourthMoment` and `KasamiQuadrupleCount`) is the `Decomp` leaf
`SecondDerivativeDecomp.kasami_derivQuadrupleCount`:
`#{(x,y,x′,y′) | Δf_a x + Δf_a y = Δf_a x′ + Δf_a y′} = q³ + 2q²`.

This module packages the **Wiener–Khinchin energy bridge** — the Fourier-analytic
link between the derivative additive energy, the autocorrelation fourth moment, and
the direct Walsh fourth moment — as **real proofs**, assembling the project's
`WienerKhinchin*` / `AutocorrWalshBridge` / `AdditiveEnergyBE3` lemmas:

* `kasami_walsh_fourthMoment` — `∑_b W(a,b)⁴ = 2q³` for the Kasami map (the proven
  APN fourth moment `WalshAB.fourth_moment_apn`);
* `kasami_offDiag_fourthMoment_eq_walsh` — the off-diagonal autocorrelation fourth
  moment equals the Walsh fourth moment, *given* the Wiener–Khinchin bridge identity;
* `kasami_additiveEnergy_iff_offDiag_fourthMoment` — `16·E = q³ + 2q²` iff
  `∑_{s≠0} R(s)⁴ = 2q³` (`additiveEnergy_value_iff_fourthMoment`).

These are the analytic bridges; the genuine AB input (that the bridge identity holds,
equivalently that the additive energy attains its value) is isolated in module 2.

## Sources

* N. Wiener; A. Khinchin (autocorrelation ↔ power spectrum).
* T. W. Cusick, P. Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2.
* C. Carlet, *Boolean Functions for Cryptography …*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Kasami Walsh fourth moment (real proof).**  For the Kasami APN power
permutation `x ↦ x^{d k}`, the direct Walsh fourth moment is `∑_b W(a,b)⁴ = 2q³`
(`WalshAB.fourth_moment_apn`, via `KasamiAB.kasami_bijective` /
`KasamiAB.kasami_is_apn_pred`). -/
theorem kasami_walsh_fourthMoment {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 :=
  WalshAB.fourth_moment_apn hcard (d k)
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha

/-- **Off-diagonal autocorrelation fourth moment = Walsh fourth moment (real proof).**
Given the Wiener–Khinchin bridge identity `∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴`, splitting
off the zero frequency `R(0)⁴ = q⁴` gives `∑_{s≠0} R(s)⁴ = ∑_b W(a,b)⁴`.  Re-export of
`autocorr_fourthMoment_offDiag_eq_walsh`. -/
theorem kasami_offDiag_fourthMoment_eq_walsh {k : ℕ} (a : F)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4 + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4 :=
  Vanish.Foundations.autocorr_fourthMoment_offDiag_eq_walsh _ a hWK

/-- **Additive energy ↔ off-diagonal fourth moment (real proof).**  For the Kasami
APN map, the additive-energy value `16·E = q³ + 2q²` is equivalent to the
off-diagonal autocorrelation fourth moment `∑_{s≠0} R(s)⁴ = 2q³`.  Re-export of
`additiveEnergy_value_iff_fourthMoment` for the Kasami map. -/
theorem kasami_additiveEnergy_iff_offDiag_fourthMoment {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
        = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ (∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) :=
  Vanish.Foundations.additiveEnergy_value_iff_fourthMoment _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha

end Vanish.Foundations.FirstPrinciples.Transcribe
