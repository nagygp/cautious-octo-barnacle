import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.FirstPrinciples.FPPadicGamma
import RequestProject.Foundations.FirstPrinciples.Decomp.StickelbergerDecomp
import RequestProject.Foundations.KasamiAxKatzAK3d
import Mathlib

/-!
# First-principles tower, Core (A) — module A·fp·s3: Stickelberger / Gross–Koblitz valuation (`hGK`)

This module assembles the Gross–Koblitz factorization of a Gauss sum out of the
`p`-adic Γ function (`FPPadicGamma.lean`) and reads off the `2`-adic valuation in
terms of the binary digit sum, discharging the named hypothesis `hGK` of
`KasamiGrossKoblitzValue.grossKoblitz_hGKval`:

```
   v₂(g(ω^{-e(s)})) = s₂(e(s))            (hGK)
```

## The chain

* **Gross–Koblitz factorization** (`gaussSum_grossKoblitz_factor`).  The Gauss sum
  `g(ω^{-s})` equals `−π^{s₂(s)} · (unit)` where `π` is a uniformizer of the prime
  above `p` and the unit is a product of `Γ_p`-values (each a unit,
  `padicGamma_unit`); the exponent of `π` is exactly the digit sum.  This is the
  transcendental core (carried as `sorry`).
* **Valuation extraction** (`kasami_gaussInt_padicVal`).  Taking the `2`-adic
  valuation of the factorization and using `padicGamma_unit` (the Γ-factor is a
  unit, valuation `0`), the valuation of the Gauss sum is the exponent `s₂(e(s))`.
  This is `hGK`.
* **Orbit consistency** (`kasami_gaussInt_padicVal_orbit_const`).  The valuation is
  constant along the Frobenius orbit — the consistency shadow already proved as
  `binDigitSum_two_pow_mul_mod` (AK3.3.0) — so it only depends on the coset of
  `e(s)`.

## Sources

Gross–Koblitz (Ann. Math. 1979); Washington, *Cyclotomic Fields*, Ch. 6;
Ireland–Rosen, Ch. 14.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Gross–Koblitz factorization (as a `2`-adic valuation statement).**  The
integer Gauss sum `g(s)`, factored through the `p`-adic Γ function, has `2`-adic
valuation equal to the binary digit sum of its Teichmüller exponent.  This is the
transcendental Gross–Koblitz core. -/
theorem gaussSum_grossKoblitz_factor {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F)
    (hne : kasamiGaussInt k a s ≠ 0) :
    padicValInt 2 (kasamiGaussInt k a s) = binDigitSum (kasamiExp k a s) :=
  Decomp.gaussSum_grossKoblitz_factor hcard hk hkn hcop hnodd a ha s hne

/-- **`hGK`: the Gross–Koblitz value.**  Packaged in the exact shape consumed by
`grossKoblitz_hGKval`: the `2`-adic valuation of the integer Gauss sum equals the
binary digit sum of the Teichmüller exponent, for every frequency with non-zero
Gauss sum. -/
theorem kasami_gaussInt_padicVal {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) :
    ∀ s : F, kasamiGaussInt k a s ≠ 0 →
      padicValInt 2 (kasamiGaussInt k a s) = binDigitSum (kasamiExp k a s) :=
  fun s hne => gaussSum_grossKoblitz_factor hcard hk hkn hcop hnodd a ha s hne

omit [CharP F 2] in
/-- **Orbit constancy of the valuation.**  The Gauss-sum valuation is the digit
sum, which is invariant along the `2`-cyclotomic (Frobenius) orbit
(`binDigitSum_two_pow_mul_mod`, AK3.3.0); hence it depends only on the coset of
`e(s)`. -/
theorem kasami_gaussInt_padicVal_orbit_const {n k : ℕ} (a : F) (s : F)
    (hn : 1 ≤ n) (j : ℕ) :
    binDigitSum ((2 ^ j * kasamiExp k a s) % (2 ^ n - 1))
      = binDigitSum ((kasamiExp k a s) % (2 ^ n - 1)) :=
  Vanish.Foundations.binDigitSum_two_pow_mul_mod hn j (kasamiExp k a s)

end Vanish.Foundations.FirstPrinciples
