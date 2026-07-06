import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.ABFourthMoment
import RequestProject.Foundations.FirstPrinciples.Decomp.SecondDerivativeDecomp

/-!
# Transcription — Leaf L6, module 3: the almost-bent quadruple count

This is the **third and final rung** of the almost-bent quadruple count (leaf **L6**
in `FirstPrinciplesTranscriptionRoadmap.md`), assembling module 2
(`ABFourthMoment`, the AB additive-energy value) to discharge the shape of the
`Decomp` leaf `SecondDerivativeDecomp.kasami_derivQuadrupleCount`.

The proof is a **real proof** translating the additive-energy value into the raw
second-derivative quadruple point count:

* `kasami_derivQuadrupleCount` —
  `#{(x,y,x′,y′) | Δf_a x + Δf_a y = Δf_a x′ + Δf_a y′} = q³ + 2q²`.

Route: module 2's `kasami_ab_additiveEnergy_value` gives `16·E = q³ + 2q²`, which
`additiveEnergy_value_iff_derivPairCount_sq` converts to the off-diagonal collision
moment `∑_{z≠0} derivPairCount² = q³ − 2q²`; adding the diagonal term
`derivPairCount(0)² = (2q)²` (`derivPairCount_zero`) and using the fiberwise identity
`derivPairCount_sq_sum_eq_quadruple` (`∑_z derivPairCount² = derivQuadrupleCount`)
gives `q³ + 2q²`.

This closes the L6 transcription: the deep leaf is now the single Wiener–Khinchin
fourth-moment bridge `ABFourthMoment.kasami_hWK_identity`, and everything else is
real Fourier/counting arithmetic.

## Sources

* F. Chabaud, S. Vaudenay, EUROCRYPT '94.
* C. Carlet, *Boolean Functions for Cryptography …*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations
open Vanish.Foundations.FirstPrinciples.Decomp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The almost-bent quadruple count (real proof).**  For the Kasami map, the
second-derivative quadruple count attains its almost-bent value `q³ + 2q²`.  Proof:
module 2's additive-energy value `16·E = q³ + 2q²` gives (via
`additiveEnergy_value_iff_derivPairCount_sq`) the off-diagonal collision moment
`∑_{z≠0} derivPairCount² = q³ − 2q²`; adding the diagonal `derivPairCount(0)² = (2q)²`
and the fiberwise identity `derivPairCount_sq_sum_eq_quadruple` yields `q³ + 2q²`.
This matches the `Decomp` leaf `SecondDerivativeDecomp.kasami_derivQuadrupleCount`. -/
theorem kasami_derivQuadrupleCount {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (derivQuadrupleCount (fun x : F => x ^ d k) a : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  have hapn : IsAPN (fun x : F => x ^ d k) :=
    KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn
  have haddE := kasami_ab_additiveEnergy_value hcard hk hkn hcop hnodd hn a ha
  have hoff :=
    (Vanish.Foundations.additiveEnergy_value_iff_derivPairCount_sq n hn hcard
      (fun x : F => x ^ d k) hapn a ha).mp haddE
  have hzero := derivPairCount_zero n hn hcard (fun x : F => x ^ d k) hapn a ha
  have htot := derivPairCount_sq_sum_eq_quadruple (fun x : F => x ^ d k) a
  have hsplit :
      (∑ z : F, (derivPairCount (fun x : F => x ^ d k) a z : ℤ) ^ 2)
        = (derivPairCount (fun x : F => x ^ d k) a 0 : ℤ) ^ 2
          + ∑ z ∈ univ.erase (0 : F), (derivPairCount (fun x : F => x ^ d k) a z : ℤ) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    ring
  rw [hsplit, hzero, hoff] at htot
  rw [← htot]
  push_cast
  ring

end Vanish.Foundations.FirstPrinciples.Transcribe
