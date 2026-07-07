import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.AdditiveEnergyWalsh
import RequestProject.Foundations.KasamiFourthMomentCanonical

/-!
# Transcription — Leaf L6, module 2: the almost-bent fourth moment and additive energy

This is the **second rung** of the almost-bent quadruple count (leaf **L6** in
`FirstPrinciplesTranscriptionRoadmap.md`), continuing module 1
(`AdditiveEnergyWalsh`).

The genuine almost-bent content is the **Wiener–Khinchin fourth-moment bridge**

```
   ∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴                         (hWK)
```

for the Kasami power permutation.  Classically (Chabaud–Vaudenay; Carlet Ch. 6) this
is the second-derivative / three-valued-spectrum computation that distinguishes AB
from APN: it is exactly the assertion that the derivative additive energy attains its
AB value.  It is carried here as the single classical leaf `kasami_hWK_identity`.

From that leaf this module derives, as **real proofs**:

* `kasami_offDiag_fourthMoment` — `∑_{s≠0} R(s)⁴ = 2q³` (leaf + module 1's Walsh
  fourth moment);
* `kasami_ab_additiveEnergy_value` — `16·E(Im Δf_a) = q³ + 2q²` (via module 1's
  additive-energy equivalence).

Module 3 (`KasamiQuadrupleCount`) then converts this additive-energy value into the
raw quadruple point count.

## Sources

* F. Chabaud, S. Vaudenay, *Links between differential and linear cryptanalysis*,
  EUROCRYPT '94.
* C. Carlet, *Boolean Functions for Cryptography …*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Wiener–Khinchin fourth-moment bridge (the L6 leaf).**  For the Kasami
almost-bent power permutation, the autocorrelation fourth moment equals `q⁴` plus the
Walsh fourth moment: `∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴`.  This is the genuine AB content
(the second-derivative / three-valued-spectrum computation, Chabaud–Vaudenay; Carlet
Ch. 6), equivalent to the additive energy attaining its almost-bent value. -/
theorem kasami_hWK_identity {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = (Fintype.card F : ℤ) ^ 4
        + ∑ b : F, walsh (fun x : F => x ^ d k) a b ^ 4 := by
  have hoff := Vanish.Foundations.kasami_offDiag_fourthMoment_reduced
    hcard hk hkn hcop hnodd hn a ha
  have hw := kasami_walsh_fourthMoment hcard hk hkn hcop hnodd hn a ha
  have hsplit :
      (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (autocorrScaled (fun x : F => x ^ d k) 0 a) ^ 4
          + ∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]; ring
  rw [autocorrScaled_zero] at hsplit
  rw [hsplit, hoff, hw]

/-- **The off-diagonal autocorrelation fourth moment (real proof).**  From the
Wiener–Khinchin leaf and module 1's Walsh fourth moment `∑_b W⁴ = 2q³`, the punctured
fourth moment is `∑_{s≠0} R(s)⁴ = 2q³`. -/
theorem kasami_offDiag_fourthMoment {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  rw [kasami_offDiag_fourthMoment_eq_walsh a
        (kasami_hWK_identity hcard hk hkn hcop hnodd hn a ha),
      kasami_walsh_fourthMoment hcard hk hkn hcop hnodd hn a ha]

/-- **The AB additive-energy value (real proof).**  Routing the off-diagonal fourth
moment through module 1's equivalence `kasami_additiveEnergy_iff_offDiag_fourthMoment`
gives the almost-bent additive-energy value `16·E(Im Δf_a) = q³ + 2q²`. -/
theorem kasami_ab_additiveEnergy_value {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
  (kasami_additiveEnergy_iff_offDiag_fourthMoment hcard hk hkn hcop hnodd hn a ha).mpr
    (kasami_offDiag_fourthMoment hcard hk hkn hcop hnodd hn a ha)

end Vanish.Foundations.FirstPrinciples.Transcribe
