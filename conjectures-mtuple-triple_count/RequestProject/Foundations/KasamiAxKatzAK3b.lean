import RequestProject.Foundations.KasamiAxKatzAK3a
import Mathlib

/-!
# Foundations, Layer AK3.2 / AK3.3 — the prime above 2 and the Gauss-sum valuation constraint

This module continues the **sub-sub-path of Layer AK3** laid out in
`Docs/VanishFutureDirections.md` §7.  Layer AK3.1
(`KasamiAxKatzAK3a.lean`) fixed the Teichmüller character `ω` (a generator of the
character group, so `χ = ω^{-s}` with a well-defined Stickelberger exponent `s`)
and showed that character values lie in the cyclotomic ring `ℤ[μ]`.  This module
supplies the **local valuation** at which Stickelberger's congruence is read off.

The deep core of AK3 is the factorization `v(g(ω^{-s})) = s₂(s)` (AK3.3), where
`v` is the local valuation at a prime above `2` (AK3.2) and `s₂` is the binary
digit sum.  This module establishes:

* **AK3.2 — the prime above 2 with its local valuation.**  In a Dedekind domain
  `O` (the cyclotomic ring of integers `ℤ[μ]` is one; `2` is not a unit there
  because `q − 1` is odd, so `2` is unramified and lies under some prime), every
  non-unit non-zero element lies in a **height-one prime**
  (`exists_heightOneSpectrum_mem`), in particular there is a prime
  `v` **above `2`** (`exists_primeAboveTwo`), at which `2` has strictly positive
  valuation `v.intValuation 2 < 1` (`intValuation_two_lt_one`).  The local
  valuation is **multiplicative** (`intValuation_mul`, `intValuation_pow`) and
  **non-degenerate** away from `0` (`intValuation_ne_zero`) — the homomorphism
  property Stickelberger's additive congruence rests on.

* **AK3.3 — the `|g|² = q` valuation constraint.**  AK3 (`KasamiAxKatzAK3.lean`)
  provided the conjugate identity `g(χ)·g(χ⁻¹) = q`.  Taking the local valuation
  of any such *conjugate pair* `g·ḡ = q = 2ⁿ` gives the **product constraint**
  `v(g)·v(ḡ) = v(2)ⁿ` (`intValuation_conj_pair`).  This is the multiplicative
  shadow of the classical absolute value `|g(χ)|² = q`: the *sum* of the two
  additive valuations is `n·v₂(2)`.  Stickelberger's deep content (AK3.3 proper)
  is the **individual** split `v(g(ω^{-s})) = s₂(s)` — exactly *which* part of the
  total `n` each conjugate carries; the constraint pins their sum, the digit sum
  pins each summand.

## Scope

This layer is sorry-free.  It builds the **local-valuation framework** (the prime
above `2`, multiplicativity, non-degeneracy) and the **product constraint**
`v(g)·v(ḡ) = v(2)ⁿ` on a conjugate pair, isolating the open deep core to the
*individual* valuation value `v(g(ω^{-s})) = s₂(s)` — the Gross–Koblitz /
Stickelberger factorization, the `p`-adic content **absent from Mathlib**,
documented as the open frontier and deliberately neither axiomatized nor
`sorry`-ed.

## Sources

Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14
(Gauss sums, Stickelberger's relation); Washington, *Introduction to Cyclotomic
Fields*, Ch. 6; Lidl–Niederreiter, *Finite Fields*, Ch. 5–6.
-/

namespace Vanish.Foundations

open IsDedekindDomain

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

/-! ## 1. (AK3.2) The prime above 2 and its local valuation -/

/-
**Every non-unit non-zero element lies in a height-one prime.**  Its principal
ideal is proper (it is not the unit ideal, as the element is not a unit) and
non-zero, so it sits inside a maximal ideal, which in a Dedekind domain is a
height-one prime.
-/
omit [IsDedekindDomain O] in
theorem exists_heightOneSpectrum_mem {x : O} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) :
    ∃ v : HeightOneSpectrum O, x ∈ v.asIdeal := by
  obtain ⟨M, hM, hxM⟩ := (Ideal.span {x}).exists_le_maximal (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hxu)
  have hxmem : x ∈ M := hxM (Ideal.mem_span_singleton_self x)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hxmem⟩
  intro hbot
  rw [hbot] at hxmem
  exact hx0 (by simpa using hxmem)

/-
**A prime above 2.**  When `2` is neither `0` nor a unit in `O` (as in the
cyclotomic ring `ℤ[μ]` with `q − 1` odd), there is a height-one prime `v`
containing `2` — the prime *above* `2` on which Stickelberger's valuation acts.
-/
omit [IsDedekindDomain O] in
theorem exists_primeAboveTwo (h0 : (2 : O) ≠ 0) (hu : ¬ IsUnit (2 : O)) :
    ∃ v : HeightOneSpectrum O, (2 : O) ∈ v.asIdeal :=
  exists_heightOneSpectrum_mem h0 hu

/-
**`2` has positive valuation.**  Membership in the prime ideal is exactly
`v.intValuation 2 < 1`: the local valuation of `2` is strictly below the unit
level.
-/
theorem intValuation_two_lt_one (v : HeightOneSpectrum O) (h : (2 : O) ∈ v.asIdeal) :
    v.intValuation 2 < 1 := by
  rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]; exact h

/-
**Multiplicativity of the local valuation.**  `v(x·y) = v(x)·v(y)` — the
homomorphism property underlying Stickelberger's *additive* congruence.
-/
theorem intValuation_mul (v : HeightOneSpectrum O) (x y : O) :
    v.intValuation (x * y) = v.intValuation x * v.intValuation y :=
  v.intValuation.map_mul x y

/-
**The local valuation of a power.**  `v(xⁿ) = v(x)ⁿ`.
-/
theorem intValuation_pow (v : HeightOneSpectrum O) (x : O) (n : ℕ) :
    v.intValuation (x ^ n) = v.intValuation x ^ n :=
  map_pow v.intValuation x n

/-
**Non-degeneracy.**  The local valuation of a non-zero element is non-zero
(`intValuation x = 0 ⟺ x = 0`), so valuations of Gauss sums (which are non-zero)
are genuine elements of the value group.
-/
theorem intValuation_ne_zero (v : HeightOneSpectrum O) {x : O} (hx : x ≠ 0) :
    v.intValuation x ≠ 0 :=
  HeightOneSpectrum.intValuation_ne_zero v x hx

/-! ## 2. (AK3.3) The `|g|² = q` valuation constraint on a conjugate pair -/

/-
**The product constraint.**  If a Gauss sum and its conjugate multiply to the
field size `g·ḡ = 2ⁿ` (the identity `g(χ)·g(χ⁻¹) = q` of AK3, with `q = 2ⁿ`),
then their local valuations multiply to `v(2)ⁿ`:
`v(g)·v(ḡ) = v(2)ⁿ`.  This is the multiplicative shadow of `|g(χ)|² = q`; the
*sum* of the additive valuations of the conjugate pair is `n·v₂(2)`, fixed
independently of `s`.  Stickelberger's deep content is *which* part of this total
each conjugate carries — the digit-sum split `v(g(ω^{-s})) = s₂(s)`.
-/
theorem intValuation_conj_pair (v : HeightOneSpectrum O) (g gbar : O) (n : ℕ)
    (h : g * gbar = (2 : O) ^ n) :
    v.intValuation g * v.intValuation gbar = (v.intValuation 2) ^ n := by
  rw [← intValuation_mul, h, intValuation_pow]

end Vanish.Foundations
