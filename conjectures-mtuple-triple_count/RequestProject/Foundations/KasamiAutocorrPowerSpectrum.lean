import RequestProject.Foundations.WienerKhinchin
import RequestProject.Foundations.WalshTransform
import RequestProject.Foundations.ChiBridge
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-3: the autocorrelation power spectrum

This module is the **third from-scratch foundational module of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), building on the Wiener–Khinchin / Parseval
substrate (`Fourier.lean`, `WienerKhinchin.lean`) and the `χ`-character bridge
(`ChiBridge.lean`).

Direction (B) computes the autocorrelation fourth moment of the second-derivative
collision distribution.  The harmonic-analytic engine is the **autocorrelation
power spectrum** identity: for a fixed mask `b`, the Walsh transform `a ↦ W(a,b)`
is the Fourier transform of the scaled autocorrelation `R_b` (the project's
`walsh_sq_eq_autocorr_sum_via_foundation`: `W(a,b)² = 𝓕_χ(R_b)(a)`), so Parseval
(`fourierTransform_parseval`) applied to `R_b` against itself reads the
*Walsh fourth moment* (mask `b` fixed, varying coefficient `a`) off the
*autocorrelation second moment*:

```
   ∑_a W(a,b)⁴ = q · ∑_u R_b(u)²            (autocorr_power_spectrum)
```

This is the autocorrelation-side power spectrum: the Walsh power spectrum
`a ↦ W(a,b)²` and the autocorrelation `u ↦ R_b(u)` are a Fourier pair, and
Parseval ties their moments.  It is the parity-agnostic Fourier identity on which
the AB-specific fourth-moment bridge `hWK` (core B-fp-4) rests.

## Results

* `autocorr_power_spectrum` — `∑_a W(a,b)⁴ = q · ∑_u R_b(u)²` (Parseval for the
  autocorrelation/Walsh Fourier pair).

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the pure Plancherel/Parseval
identity for the autocorrelation power spectrum; the AB-specific fourth-moment
bridge `hWK` linking the frequency-side fourth moment `∑_s R(s)⁴` to `∑_b W(a,b)⁴`
is the subject of B-fp-4.

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2
(Wiener–Khinchin, Parseval); Carlet, Ch. 6 (AB functions, fourth moment).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open AddChar Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**The autocorrelation power spectrum (Parseval).**  For a fixed mask `b`, the
Walsh power spectrum `a ↦ W(a,b)²` is the Fourier transform of the scaled
autocorrelation `R_b` (`walsh_sq_eq_autocorr_sum_via_foundation`), so Parseval
(`fourierTransform_parseval`, with `χ⁻¹ = χ` in characteristic two) gives the
Walsh fourth moment as the autocorrelation second moment:

```
   ∑_a W(a,b)⁴ = q · ∑_u R_b(u)².
```
-/
theorem autocorr_power_spectrum (f : F → F) (b : F) :
    ∑ a : F, walsh f a b ^ 4
      = (Fintype.card F : ℤ) * ∑ u : F, autocorrScaled f b u ^ 2 := by
  convert WalshAB.walsh_fourth_sum_a f b using 1

end Vanish.Foundations