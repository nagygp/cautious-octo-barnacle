import RequestProject.Foundations.KasamiAutocorrPowerSpectrum
import RequestProject.Foundations.KasamiAutocorrWalshBridge
import RequestProject.Foundations.KasamiAdditiveEnergyBE3
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Foundations — Direction (B), first-principles module B-fp-4: the Wiener–Khinchin bridge (`hWK`)

This module is the **fourth from-scratch foundational module of direction (B)**
(the almost-bent additive-energy programme of
`Docs/VanishFutureDirections.md`, §15), building on B-fp-3
(`KasamiAutocorrPowerSpectrum.lean`), the bridge assembly
(`KasamiAutocorrWalshBridge.lean`), and the additive-energy equivalence
(`KasamiAdditiveEnergyBE3.lean`).

This is the core **B-fp-4**: the AB Wiener–Khinchin fourth-moment bridge

```
   ∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴            (hWK)
```

linking the frequency-side autocorrelation fourth moment to the direct Walsh
fourth moment.  For an almost-bent power permutation, the direct Walsh fourth
moment is the *proven* value `∑_b W(a,b)⁴ = 2q³` (`WalshAB.fourth_moment_apn`), so
the bridge is no longer an opaque hypothesis: this module proves that, for the
Kasami AB regime, **`hWK` is equivalent to the additive-energy value**

```
   hWK  ⟺  16·E(Im Δf_a) = q³ + 2q²          (kasami_hWK_iff_additiveEnergy)
```

— pinning down exactly what the bridge core buys.  Concretely, with
`∑_b W(a,b)⁴ = 2q³` substituted and the zero frequency split off
(`R(0)⁴ = q⁴`, `autocorrScaled_zero_pow_four`), `hWK` says precisely
`∑_{s≠0} R(s)⁴ = 2q³`, which the punctured-moment equivalence
`additiveEnergy_value_iff_fourthMoment` translates into the additive-energy value.

This is the AB-specific content: the bridge `hWK` is exactly the assertion that the
second-derivative additive energy attains its almost-bent value.

## Results

* `kasami_hWK_iff_additiveEnergy` — for the Kasami AB power permutation,
  `hWK ⟺ 16·E = q³ + 2q²`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It does not assume `hWK`; instead it
characterizes it.  The remaining genuine content — that the additive energy
*attains* the value `q³ + 2q²` (equivalently that `hWK` *holds*) — is the
AB-additive-energy computation, the deep frontier of (B).

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2
(Wiener–Khinchin); Carlet, Ch. 6 (AB functions, fourth moment);
Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

variable {n k : ℕ}

/-
**The Wiener–Khinchin bridge is equivalent to the additive-energy value.**
For the Kasami almost-bent power permutation `x ↦ x^{d k}`, the direct Walsh fourth
moment is the proven value `∑_b W(a,b)⁴ = 2q³` (`WalshAB.fourth_moment_apn`), so the
bridge `hWK` (`∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴`) is *equivalent* to the AB
additive-energy value `16·E(Im Δf_a) = q³ + 2q²`.  This pins down exactly what the
bridge core delivers.
-/
theorem kasami_hWK_iff_additiveEnergy
    (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) (a : F) (ha : a ≠ 0) :
    ((∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4)
      ↔ (16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) := by
  have hWalsh : ∑ b : F, walsh (fun x => x ^ d k) a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3 := by
    apply_rules [ WalshAB.fourth_moment_apn ];
    · exact KasamiAB.kasami_bijective hcard k hk hcop hnodd ( by linarith );
    · exact KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn;
  constructor <;> intro h <;> have := Vanish.Foundations.additiveEnergy_value_iff_fourthMoment (fun x => x ^ d k) (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha <;> simp_all +decide;
  · rw [ Vanish.Foundations.autocorrScaled_zero_pow_four ] ; norm_num [ hcard ];
  · rw [ Vanish.Foundations.autocorrScaled_zero_pow_four ] at this;
    grind

end Vanish.Foundations