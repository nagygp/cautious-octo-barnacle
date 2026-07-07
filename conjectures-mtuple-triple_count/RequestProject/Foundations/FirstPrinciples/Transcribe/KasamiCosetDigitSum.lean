import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.McElieceWeightCongruence

/-!
# Transcription — Leaf L5, module 2: the Kasami coset digit-sum bound

This is the **second and final rung** of the McEliece digit-sum bound (leaf **L5** in
`FirstPrinciplesTranscriptionRoadmap.md`), assembling module 1
(`McElieceWeightCongruence`) with Stickelberger's valuation formula (leaf L3,
`StickelbergerDecomp.gaussSum_grossKoblitz_factor`) to discharge the shape of the
`Decomp` leaf `AxKatzDecomp.kasami_exp_digitSum_lower_bound`:

* `kasami_exp_digitSum_lower_bound` — for a non-trivial Kasami frequency,
  `(n+1)/2 ≤ s₂(e(s))` (**real proof**, modulo the module-1 weight-congruence leaf
  and the L1/L3 leaves it rests on).

The proof is the clean McEliece reading: the frequency `R(s) = ± g(s)` is non-zero
(`FPGaussSumSetup.kasami_crossCorr_eq_gaussInt`), so `g(s) ≠ 0`; module 1 gives
`2^{(n+1)/2} ∣ g(s)`, hence `v₂(g(s)) ≥ (n+1)/2` (`padicValInt_ge_of_two_pow_dvd`);
and Stickelberger's `v₂(g(s)) = s₂(e(s))`
(`gaussSum_grossKoblitz_factor`) turns this into the digit-sum lower bound.  This is
the whole content of the Kasami coset digit-sum bound.

## Sources

* R. J. McEliece, *Weight congruences for p-ary cyclic codes*, Discrete Math. 3
  (1972).
* A. Canteaut, P. Charpin, H. Dobbertin, SIAM J. Discrete Math. 13 (2000).
* Project: `StickelbergerDecomp.gaussSum_grossKoblitz_factor`,
  `FPGaussSumSetup.kasami_crossCorr_eq_gaussInt`.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations
open Vanish.Foundations.FirstPrinciples Vanish.Foundations.FirstPrinciples.Decomp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Kasami coset digit-sum bound (real proof).**  For a non-trivial Kasami
frequency (`autocorrScaled ≠ 0`), the binary digit sum of the Teichmüller exponent
is at least `(n+1)/2`.  Proof: the cross-correlation equals `± g(s)`
(`kasami_crossCorr_eq_gaussInt`), so `g(s) ≠ 0`; module 1's weight congruence gives
`2^{(n+1)/2} ∣ g(s)`, hence `(n+1)/2 ≤ v₂(g(s))`; and Stickelberger's
`v₂(g(s)) = s₂(e(s))` (`gaussSum_grossKoblitz_factor`) gives the digit-sum bound.
This has the same shape as the `Decomp` leaf
`AxKatzDecomp.kasami_exp_digitSum_lower_bound`. -/
theorem kasami_exp_digitSum_lower_bound {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      (n + 1) / 2 ≤ binDigitSum (kasamiExp k a s) := by
  intro s hs
  have hgauss := kasami_crossCorr_eq_gaussInt hcard hk hkn hcop hnodd a ha s
  have hne : kasamiGaussInt k a s ≠ 0 := by
    intro hz
    apply hs
    rcases hgauss with h | h <;> simp [h, hz]
  have hdvd := kasami_gaussInt_two_pow_dvd hcard hk hkn hcop hnodd a ha s hne
  have hval := padicValInt_ge_of_two_pow_dvd (kasamiGaussInt k a s) ((n + 1) / 2) hne hdvd
  have hstick := gaussSum_grossKoblitz_factor hcard hk hkn hcop hnodd a ha s hne
  rw [hstick] at hval
  exact hval

end Vanish.Foundations.FirstPrinciples.Transcribe
