import RequestProject.Foundations.KasamiAdditiveEnergyBE3
import RequestProject.Foundations.KasamiAdditiveEnergy
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Foundations — Input (B): the Wiener–Khinchin autocorrelation/Walsh fourth-moment bridge

This module **transcribes the next step of direction (B)**: it connects the
*known, proven* direct Walsh fourth moment `∑_b W(a,b)⁴ = 2q³`
(`WalshAB.fourth_moment_apn`, unconditional for APN power permutations) to the
*autocorrelation* fourth moment `∑_{s≠0} R(s)⁴ = 2q³` — the punctured second
moment of the second-derivative collision distribution (input (B)).

The two fourth moments are tied by a single **Wiener–Khinchin identity** between
the autocorrelation power spectrum and the direct Walsh power spectrum:

```
   ∑_{s} R(s)⁴ = q⁴ + ∑_b W(a,b)⁴            (hWK)
```

(the `q⁴` is the zero-frequency term `R(0)⁴ = q⁴`,
`autocorrScaled_zero_pow_four`).  Once this identity is supplied, the off-diagonal
autocorrelation fourth moment is obtained from the *proven* Walsh fourth moment by
pure arithmetic:

* `autocorr_fourthMoment_offDiag_of_bridge` — the field-agnostic step
  `∑_{s≠0} R(s)⁴ = ∑_b W(a,b)⁴`, hence `= 2q³` once `hWalsh` is supplied;
* `kasami_autocorr_fourthMoment_offDiag_of_bridge` — its Kasami specialization,
  where `hWalsh` is discharged by the proven `WalshAB.fourth_moment_apn`, so that
  input (B) follows from the single bridge identity `hWK` alone;
* `kasami_additiveEnergy_value_of_bridge` — feeding the result through the
  equivalence `additiveEnergy_value_iff_fourthMoment` to pin the genuine deep
  input of (B), the AB additive-energy value `16·E(Im Δf_a) = q³ + 2q²`, again
  from `hWK` alone.

## Scope

The arithmetic assembly is sorry-free.  The bridge identity `hWK` itself — the
Wiener–Khinchin link between the autocorrelation and direct Walsh fourth moments —
is the genuine remaining input of (B); for power permutations on odd `n` it is the
Fourier-analytic content of almost-bentness (it fails for APN-but-not-AB
functions).  It is carried here as a named hypothesis rather than an axiom or
`sorry`, matching the project convention.

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2
(Wiener–Khinchin); Carlet, Ch. 6 (AB functions, fourth moment); Chabaud–Vaudenay
§3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The bridge, field-agnostic -/

/-- **The autocorrelation off-diagonal fourth moment equals the direct Walsh
fourth moment.**  Splitting off the zero-frequency term `R(0)⁴ = q⁴`
(`autocorrScaled_zero_pow_four`) from the Wiener–Khinchin bridge
`∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴` gives `∑_{s≠0} R(s)⁴ = ∑_b W(a,b)⁴`. -/
theorem autocorr_fourthMoment_offDiag_eq_walsh (f : F → F) (a : F)
    (hWK : (∑ s : F, (autocorrScaled f s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4 + ∑ b : F, walsh f a b ^ 4) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4)
      = ∑ b : F, walsh f a b ^ 4 := by
  have hsplit :
      (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4)
        + (autocorrScaled f 0 a) ^ 4
        = ∑ s : F, (autocorrScaled f s a) ^ 4 :=
    Finset.sum_erase_add _ _ (Finset.mem_univ 0)
  rw [autocorrScaled_zero_pow_four f a] at hsplit
  rw [hWK] at hsplit
  linarith

/-- **Input (B) from the Wiener–Khinchin bridge and the proven Walsh moment.**
Given the bridge identity `hWK` and the value `hWalsh : ∑_b W(a,b)⁴ = 2q³`, the
off-diagonal autocorrelation fourth moment is `2q³`. -/
theorem autocorr_fourthMoment_offDiag_of_bridge (f : F → F) (a : F)
    (hWalsh : ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3)
    (hWK : (∑ s : F, (autocorrScaled f s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4 + ∑ b : F, walsh f a b ^ 4) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  rw [autocorr_fourthMoment_offDiag_eq_walsh f a hWK, hWalsh]

/-! ## 2. The Kasami specialization (Walsh moment discharged) -/

variable {n k : ℕ}

/-- **Kasami input (B) from the bridge alone.**  Specializing to the Kasami power
permutation `x ↦ x^{d k}` (APN by `KasamiAB.kasami_is_apn_pred`, a permutation by
`KasamiAB.kasami_bijective`), the Walsh fourth moment `∑_b W(a,b)⁴ = 2q³` is the
*proven* `WalshAB.fourth_moment_apn`, so input (B) follows from the single bridge
identity `hWK`. -/
theorem kasami_autocorr_fourthMoment_offDiag_of_bridge
    (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) (a : F) (ha : a ≠ 0)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  have hWalsh : ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4
      = 2 * (Fintype.card F : ℤ) ^ 3 :=
    WalshAB.fourth_moment_apn hcard (d k)
      (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
      (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha
  exact autocorr_fourthMoment_offDiag_of_bridge _ a hWalsh hWK

/-- **The AB additive-energy value from the bridge.**  Routing the previous result
through `additiveEnergy_value_iff_fourthMoment` pins the genuine deep input of (B),
`16·E(Im Δf_a) = q³ + 2q²`, from the single bridge identity `hWK`. -/
theorem kasami_additiveEnergy_value_of_bridge
    (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) (a : F) (ha : a ≠ 0)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4) :
    16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
  (additiveEnergy_value_iff_fourthMoment _
      (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha).mpr
    (kasami_autocorr_fourthMoment_offDiag_of_bridge hcard hk hkn hcop hnodd hn a ha hWK)

end Vanish.Foundations
