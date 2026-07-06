import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.FirstPrinciples.Decomp.PadicGammaDecomp
import RequestProject.Foundations.KasamiAxKatz
import Mathlib

/-!
# Decomposition library — Core (A·fp·s3): Gross–Koblitz / Stickelberger valuation, bottom-up

This module **expands the deep core** `FPStickelberger.gaussSum_grossKoblitz_factor`
(the `hGK` valuation `v₂(g) = s₂(e)`) into a bottom-up skeleton whose single deep
leaf is the **integer Gross–Koblitz factorization** of the Gauss sum, after which
the valuation extraction is real `2`-adic arithmetic.

## The chain

* `kasamiGaussInt_factor_two_pow` — the genuine Gross–Koblitz leaf: the integer
  Gauss sum factors as `± 2^{s₂(e(s))} · (odd)`.  (Gross–Koblitz, Ann. Math. 1979,
  read off through Morita's `Γ_p` of `PadicGammaDecomp`, every `Γ_p`-factor a unit.)
* `padicValInt_two_pow_mul_odd` — elementary `2`-adic valuation arithmetic:
  `v₂(2^c · m) = c` for `m` odd (a real proof).
* `gaussSum_grossKoblitz_factor` — the assembled `hGK`, a **real proof** combining
  the factorization with the valuation arithmetic.

## Sources

Gross–Koblitz (Ann. Math. 1979); Washington, *Cyclotomic Fields*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open Finset BigOperators WalshAB MTuple CollisionAnalysis Vanish.Foundations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The integer Gross–Koblitz factorization (the deep leaf).**  Through the
Gross–Koblitz formula — the Gauss sum factored over the `p`-adic Γ function, every
`Γ_p`-factor a unit (`PadicGammaDecomp.padicGamma_unit`) — the integer Teichmüller
Gauss sum factors as `± 2^{s₂(e(s))} · (odd integer)`. -/
theorem kasamiGaussInt_factor_two_pow {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F)
    (hne : kasamiGaussInt k a s ≠ 0) :
    ∃ m : ℤ, Odd m ∧
      (kasamiGaussInt k a s = 2 ^ (binDigitSum (kasamiExp k a s)) * m
        ∨ kasamiGaussInt k a s = -(2 ^ (binDigitSum (kasamiExp k a s)) * m)) := by
  sorry

/-
**Elementary `2`-adic valuation arithmetic.**  `v₂(2^c · m) = c` for `m` an odd
integer.  A real proof (no number theory beyond `padicValInt` of a power times a
unit).
-/
theorem padicValInt_two_pow_mul_odd (c : ℕ) (m : ℤ) (hm : Odd m) :
    padicValInt 2 (2 ^ c * m) = c := by
  rcases hm with ⟨ k, rfl ⟩;
  rw [ padicValInt.mul ] <;> norm_num;
  · norm_num [ padicValInt ];
    omega;
  · omega

/-- **The assembled Gross–Koblitz value (`hGK`).**  Combining the factorization
`kasamiGaussInt_factor_two_pow` with the valuation arithmetic
`padicValInt_two_pow_mul_odd`, the `2`-adic valuation of the integer Gauss sum is
the binary digit sum of the Teichmüller exponent.  Real wiring. -/
theorem gaussSum_grossKoblitz_factor {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F)
    (hne : kasamiGaussInt k a s ≠ 0) :
    padicValInt 2 (kasamiGaussInt k a s) = binDigitSum (kasamiExp k a s) := by
  obtain ⟨m, hodd, hfac | hfac⟩ :=
    kasamiGaussInt_factor_two_pow hcard hk hkn hcop hnodd a ha s hne
  · rw [hfac, padicValInt_two_pow_mul_odd _ _ hodd]
  · rw [hfac]
    have : padicValInt 2 (-(2 ^ (binDigitSum (kasamiExp k a s)) * m))
        = padicValInt 2 (2 ^ (binDigitSum (kasamiExp k a s)) * m) := by
      simp [padicValInt]
    rw [this, padicValInt_two_pow_mul_odd _ _ hodd]

end Vanish.Foundations.FirstPrinciples.Decomp