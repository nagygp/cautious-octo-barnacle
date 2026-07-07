import RequestProject.Foundations.KasamiTwoDerivPolar
import RequestProject.Foundations.KasamiVanishSign
import RequestProject.Foundations.KasamiMTupleCount
import Mathlib

/-!
# Foundations — the `k = 2` Kasami m-tuple count, reduced to the single WK bridge core

This module is the `k = 2` capstone of the m-tuple count proof path.  For the general
Kasami exponent the count `imgCount m (·^{d k}) a c = 2^{(m-1)n − m}` rests on **both**
classical scalar inputs (A) (the `2^{(n+1)/2}`-divisibility of the cross-correlation)
and (B) (the almost-bent fourth moment `∑_{s≠0} R(s)⁴ = 2q³`), each carried as a deep
leaf of the (A)/(B) towers.

For the **quadratic** Kasami exponent `k = 2` (whose derivative form has vanishing
third derivative, so it is a genuine quadratic form), input (A) is now **green**
(`crossCorr_hdiv_of_third_deriv`, via the quadratic-form Gauss-sum divisibility
`quadGaussSum_two_adic_div_of_third_deriv`), and input (B) reduces — through the green
Wiener–Khinchin bridge lemma `kasami_autocorr_fourthMoment_offDiag_of_bridge` and the
*proven* Walsh fourth moment `WalshAB.fourth_moment_apn` — to the **single shared
bridge core** `hWK`:
```
   ∑_s R(s)⁴ = q⁴ + ∑_b W(a,b)⁴          (at the shift a = 1).
```
Moreover, by power-map shift invariance (`fourthMoment_pow_indep`), the fourth moment
at *every* shift `a ≠ 0` follows from the single `a = 1` bridge core, so the whole
family of counts (all shifts `a`) collapses onto that one hypothesis.

* `kasami_two_fourthMoment_of_bridge` — input (B) at every shift `a`, from the `a = 1`
  bridge core `hWK`;
* `kasami_two_mtuple_count` — the general-`m` count at every shift `a`, for coefficients
  whose sign correlation vanishes, resting only on `hWK`;
* `kasami_two_triple_count` — the `m = 3` specialization `imgCount = 2^{2n-3}`.

All are sorry-free assemblies of the green k=2 layers (`KasamiTwoDerivPolar`,
`KasamiTwoAdicValuation`, `KasamiAutocorrWalshBridge`, `KasamiFourthMomentCanonical`)
with the general `Vanish`/count engine (`KasamiVanishSign`, `KasamiMTupleCount`,
`MTuple.imgCount_of_vanish`).

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000); Carlet,
*Boolean Functions for Cryptography…*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Input (B) at every shift, from the single `a = 1` WK bridge core.**  For the
quadratic Kasami exponent `k = 2`, the off-diagonal autocorrelation fourth moment
`∑_{s≠0} R_a(s)⁴ = 2q³` holds for *every* shift `a ≠ 0`, deduced from the `a = 1`
bridge core `hWK` by power-map shift invariance (`fourthMoment_pow_indep`) after
splitting off the constant zero-frequency term `R_a(0)⁴ = q⁴`. -/
theorem kasami_two_fourthMoment_of_bridge {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n) (hnodd : Odd n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (a : F) (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  have h1 := kasami_autocorr_fourthMoment_offDiag_of_bridge hcard
    (by norm_num) hkn hcop hnodd (by omega) 1 one_ne_zero hWK
  have sa := Finset.sum_erase_add Finset.univ
    (fun s => (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s a) ^ 4)
    (Finset.mem_univ (0 : F))
  have s1 := Finset.sum_erase_add Finset.univ
    (fun s => (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
    (Finset.mem_univ (0 : F))
  have hindep := fourthMoment_pow_indep (CollisionAnalysis.d 2) a ha
  dsimp only at sa s1
  rw [autocorrScaled_zero_pow_four (fun x : F => x ^ CollisionAnalysis.d 2) a] at sa
  rw [autocorrScaled_zero_pow_four (fun x : F => x ^ CollisionAnalysis.d 2) 1] at s1
  linarith [h1, sa, s1, hindep]

/-- **The `k = 2` Kasami m-tuple count, reduced to the WK bridge core.**  For the
quadratic Kasami exponent `k = 2` over `GF(2ⁿ)` (`n` odd, `n > 2`), the image m-tuple
count of the derivative at any shift `a ≠ 0` is `2^{(m-1)n − m}` for every nonzero
coefficient tuple whose sign correlation vanishes.  Input (A) is green; the only
remaining input is the shared `a = 1` Wiener–Khinchin bridge core `hWK`. -/
theorem kasami_two_mtuple_count {n m : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n) (hnodd : Odd n)
    (hm : 2 ≤ m)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hsign : ∑ t ∈ univ.erase (0 : F),
        ∏ i : Fin m, crossCorrSign (fun x : F => x ^ CollisionAnalysis.d 2) a
          ((n + 1) / 2) (t * c i) = 0) :
    imgCount m (fun x : F => x ^ CollisionAnalysis.d 2) a c = 2 ^ ((m - 1) * n - m) := by
  -- input (A) divisibility: green (the k = 2 derivative form is quadratic).
  have hdiv := crossCorr_hdiv_of_third_deriv hcard hnodd
    (fun x : F => x ^ CollisionAnalysis.d 2) a
    (fun s x y z => kasami_two_deriv_third_deriv_zero s a x y z)
  -- input (B) fourth moment at shift `a`: green from the `a = 1` bridge core `hWK`.
  have hfourth := kasami_two_fourthMoment_of_bridge hcard hkn hcop hnodd hWK a ha
  have hv : Vanish m (fun x : F => x ^ CollisionAnalysis.d 2) a c :=
    (kasami_vanish_iff_sign_sum hcard (by norm_num) hkn hcop hnodd (by omega)
      a ha c hc hdiv hfourth).mpr hsign
  exact kasami_mtuple_count hcard (by norm_num) hkn hcop hnodd (by omega) hm a ha c hv

/-- **The `k = 2` Kasami triple count, reduced to the WK bridge core.**  The `m = 3`
specialization of `kasami_two_mtuple_count`: `imgCount 3 (·^{d 2}) a c = 2^{2n-3}` for a
nonzero coefficient triple whose sign correlation vanishes. -/
theorem kasami_two_triple_count {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hkn : 2 < n) (hcop : Nat.Coprime 2 n) (hnodd : Odd n)
    (hWK : (∑ s : F, (autocorrScaled (fun x : F => x ^ CollisionAnalysis.d 2) s 1) ^ 4)
        = (Fintype.card F : ℤ) ^ 4
          + ∑ b : F, walsh (fun x : F => x ^ CollisionAnalysis.d 2) 1 b ^ 4)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) (hc : ∀ i, c i ≠ 0)
    (hsign : ∑ t ∈ univ.erase (0 : F),
        ∏ i : Fin 3, crossCorrSign (fun x : F => x ^ CollisionAnalysis.d 2) a
          ((n + 1) / 2) (t * c i) = 0) :
    imgCount 3 (fun x : F => x ^ CollisionAnalysis.d 2) a c = 2 ^ (2 * n - 3) := by
  have h := kasami_two_mtuple_count hcard hkn hcop hnodd (by norm_num) hWK a ha c hc hsign
  simpa using h

end Vanish.Foundations
