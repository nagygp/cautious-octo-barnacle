import RequestProject.Foundations.KasamiAxKatzAK3f
import RequestProject.Foundations.KasamiAxKatzAK4a
import Mathlib

/-!
# Foundations, Layer AK3.3.3 — the Gross–Koblitz value and its arithmetic-Frobenius realization

This module **implements direction (A)**: the explicit (residue-level) arithmetic
Frobenius realizing the Gauss-sum doubling step `g(ω^{-2s}) = e(g(ω^{-s}))`, and the
Gross–Koblitz value `v(g(ω^{-s})) = s₂(s)`.

## The arithmetic-Frobenius realization

The abstract layer AK3.3.2 (`KasamiAxKatzAK3f.lean`) carried the Frobenius step
`g(ω^{-2s}) = e(g(ω^{-s}))` as a hypothesis.  Here it is **realized concretely** at
the residue / character level by the Gauss-sum `p`-power law `gaussSum_pow_char`
(AK3): in characteristic `2`,

```
   g(χ, ψ)² = g(χ², ψ²)        (gaussSum_sq_char_step).
```

Writing `χ = ω^{-s}` (the multiplicative character indexing the Gauss sum), `χ²` is
`ω^{-2s}`, so squaring is *literally* the doubling step `s ↦ 2s`: the arithmetic
Frobenius `e` of the decomposition group at the prime above `2` lifts this residue
Frobenius `x ↦ x²`, and `gaussSum_sq_char_step` exhibits it on the Gauss sums.

## The Gross–Koblitz value `v(g) = s₂(s)` is orbit-constant

Stickelberger / Gross–Koblitz gives the valuation as the binary digit sum
`v(g(ω^{-s})) = s₂(s mod (2ⁿ − 1))`.  Carrying this value as a named hypothesis
`hGK` (the genuine Gross–Koblitz core), the orbit constancy
`v(g(ω^{-2^j s})) = v(g(ω^{-s}))` is **forced** by the digit-sum doubling
invariance `binDigitSum_two_pow_mul_mod` (AK3.3.0):

* `grossKoblitz_value_orbit_const` — `v(g(ω^{-2^j s})) = s₂(s mod (2ⁿ−1))` for all `j`,
  the value-level analogue of the abstract valuation orbit-invariance
  `gaussSum_intValuation_frobenius_orbit` (AK3.3.2);
* `grossKoblitz_kasami_orbit_const` — its Kasami specialization `s = d k`, where the
  digit sum is the Kasami coset invariant `kasami_coset_digitSum_invariant` (AK4.0).

So both AK3.3.2's valuation invariance (proved abstractly) and Gross–Koblitz's value
`s₂(s)` (carried as `hGK`) agree along the Frobenius orbit, reducing the Stickelberger
valuation to the binary digit sum of one orbit representative.

## Scope

The Frobenius-step realization `gaussSum_sq_char_step` and the orbit-constancy of the
Gross–Koblitz value are sorry-free.  The Gross–Koblitz equality `v(g) = s₂(s)` itself
(the explicit `p`-adic Gamma / Gross–Koblitz formula) and the lift of the residue
Frobenius to the cyclotomic automorphism `e` remain the deep cores, carried as named
hypotheses rather than axioms or `sorry`.

## Sources

Gross–Koblitz, *Gauss sums and the p-adic Γ-function* (Ann. Math. 1979);
Ireland–Rosen, Ch. 14; Washington, *Cyclotomic Fields*, Ch. 6; Lang,
*Cyclotomic Fields*, Ch. 1.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators MulChar AddChar

/-! ## 1. The arithmetic-Frobenius realization of the doubling step -/

variable {R : Type*} [Field R] [Fintype R]
  {R' : Type*} [CommRing R'] [IsDomain R']

omit [IsDomain R'] in
/-- **The Frobenius doubling step, realized.**  In characteristic `2`, the Gauss-sum
`p`-power law (`gaussSum_pow_char`, AK3) gives `g(χ, ψ)² = g(χ², ψ²)`.  With
`χ = ω^{-s}` this is the literal doubling step `s ↦ 2s` realizing
`g(ω^{-2s}) = e(g(ω^{-s}))` at the residue / character level. -/
theorem gaussSum_sq_char_step [Fact (Nat.Prime 2)] [CharP R' 2]
    (χ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ ^ 2 = gaussSum (χ ^ 2) (ψ ^ 2) :=
  gaussSum_pow_char 2 χ ψ

/-! ## 2. The Gross–Koblitz value is orbit-constant -/

/-
**The Gross–Koblitz value is orbit-constant.**  Carrying the Gross–Koblitz
valuation `v(g(ω^{-2^j s})) = s₂((2^j s) mod (2ⁿ−1))` as the named hypothesis `hGK`,
the digit-sum doubling invariance `binDigitSum_two_pow_mul_mod` (AK3.3.0) forces the
value to be constant along the Frobenius orbit:
`v(g(ω^{-2^j s})) = s₂(s mod (2ⁿ−1))`.
-/
theorem grossKoblitz_value_orbit_const {n : ℕ} (hn : 1 ≤ n) (s : ℕ) (val : ℕ → ℕ)
    (hGK : ∀ j, val j = binDigitSum ((2 ^ j * s) % (2 ^ n - 1))) (j : ℕ) :
    val j = binDigitSum (s % (2 ^ n - 1)) := by
  rw [ hGK, Vanish.Foundations.binDigitSum_two_pow_mul_mod hn j s ]

/-- **The Gross–Koblitz value, Kasami specialization.**  For the Kasami exponent
`s = d k`, the orbit-constant Gross–Koblitz value is the Kasami coset digit-sum
invariant `s₂((d k) mod (2ⁿ−1))` (`kasami_coset_digitSum_invariant`, AK4.0). -/
theorem grossKoblitz_kasami_orbit_const {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (val : ℕ → ℕ)
    (hGK : ∀ j, val j = binDigitSum ((2 ^ j * CollisionAnalysis.d k) % (2 ^ n - 1)))
    (j : ℕ) :
    val j = binDigitSum (CollisionAnalysis.d k % (2 ^ n - 1)) :=
  grossKoblitz_value_orbit_const hn (CollisionAnalysis.d k) val hGK j

end Vanish.Foundations