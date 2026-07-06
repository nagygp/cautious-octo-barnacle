import RequestProject.Foundations.KasamiAxKatzAK3e
import Mathlib

/-!
# Foundations, Layer AK3.3.2 — Gauss-sum valuation invariance along the Frobenius orbit

This module promotes the **abstract** valuation Frobenius-invariance of AK3.3.1
(`KasamiAxKatzAK3e.lean`) — *an automorphism fixing the prime above `p` preserves
its valuation* — to the **Gauss-sum-level** statement requested in direction (A):

> `v(g(ω^{-2s})) = v(g(ω^{-s}))` along the Frobenius orbit `s, 2s, 4s, …`,

reducing the Stickelberger valuation `v(g(ω^{-s}))` to a **single orbit
representative**.

## The mathematical content

Stickelberger's congruence is read off the local valuation `v` at the prime above
`2` of the cyclotomic ring of integers.  The Gauss-sum `p`-power law
`g(χ,ψ)^p = g(χ^p, ψ^p)` (`gaussSum_pow_char`, AK3) exhibits `g(ω^{-2s})` as the
image of `g(ω^{-s})` under the **arithmetic Frobenius** `e` of the decomposition
group at the prime above `2`; that automorphism *fixes* the prime, so by
AK3.3.1's `intValuation_eq_of_ringEquiv_fixes` it preserves the valuation.

The Gauss sums `g(ω^{-2^j s})` are defined independently of `e`; what links them
into an orbit is precisely the realization `g(ω^{-2s}) = e(g(ω^{-s}))` of the
Frobenius step.  This module carries that realization as a hypothesis (matching
the project's convention of carrying the still-open deep inputs as named
hypotheses rather than axioms) and derives the **valuation constancy along the
orbit** unconditionally from it:

* `gaussSum_intValuation_frobenius_step` — one Frobenius step:
  `v(g₂) = v(g₁)` whenever `g₂ = e g₁` and `e` fixes `v`.  This is the literal
  `v(g(ω^{-2s})) = v(g(ω^{-s}))`.
* `gaussSum_intValuation_frobenius_orbit` — the **orbit form**: for any externally
  supplied Gauss-sum orbit `g : ℕ → R` with `g (j+1) = e (g j)`, the valuation is
  constant, `v(g j) = v(g 0)` — the valuation depends only on the orbit
  representative.
* `gaussSum_intValuation_orbit_const` — the two-point constancy `v(g i) = v(g j)`.

This is the valuation-theoretic upgrade of the combinatorial digit-sum doubling
invariance `binDigitSum_two_pow_mul_mod` (AK3.3.0) and `kasami_coset_digitSum_…`
(AK4.0): the *valuation* (not merely its conjectural digit-sum value) is genuinely
constant on the Frobenius orbit.

## Scope

This layer is sorry-free.  It supplies the Gauss-sum-level orbit invariance,
reducing the Stickelberger valuation to one orbit representative.  The remaining
deep core — that the arithmetic Frobenius `e` fixing the prime above `2` indeed
realizes `g(ω^{-2s}) = e(g(ω^{-s}))` (the explicit Galois action on Gauss sums),
and the *value* `v(g(ω^{-s})) = s₂(s)` (Gross–Koblitz / `p`-adic Gamma) — stays
open, deliberately neither axiomatized nor `sorry`-ed.

## Sources

Ireland–Rosen, Ch. 14 (Stickelberger; the Galois action on Gauss sums);
Washington, *Cyclotomic Fields*, Ch. 6; Neukirch, Ch. I (decomposition group,
Frobenius, valuations of conjugates).
-/

namespace Vanish.Foundations

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-
**One Frobenius step.**  If a ring automorphism `e` fixes the height-one prime
`v` (above `2`) and the Frobenius step is realized as `g₂ = e g₁` (with
`g₁ = g(ω^{-s})`, `g₂ = g(ω^{-2s})` the Gauss sums), then the local valuation is
preserved: `v(g₂) = v(g₁)`.  This is the literal Gauss-sum valuation invariance
`v(g(ω^{-2s})) = v(g(ω^{-s}))`.
-/
theorem gaussSum_intValuation_frobenius_step (v : HeightOneSpectrum R) (e : R ≃+* R)
    (hfix : Ideal.map (e : R →+* R) v.asIdeal = v.asIdeal) {g₁ g₂ : R}
    (hstep : g₂ = e g₁) :
    v.intValuation g₂ = v.intValuation g₁ := by
  rw [ hstep, intValuation_eq_of_ringEquiv_fixes v e hfix g₁ ]

/-
**Orbit invariance.**  For an externally supplied Gauss-sum orbit
`g : ℕ → R` (with `g j = g(ω^{-2^j s})`) whose successive terms are related by the
Frobenius `e` fixing `v` (`g (j+1) = e (g j)`), the local valuation is constant
along the orbit: `v(g j) = v(g 0)`.  This reduces the Stickelberger valuation to a
single orbit representative.
-/
theorem gaussSum_intValuation_frobenius_orbit (v : HeightOneSpectrum R) (e : R ≃+* R)
    (hfix : Ideal.map (e : R →+* R) v.asIdeal = v.asIdeal) (g : ℕ → R)
    (hstep : ∀ j, g (j + 1) = e (g j)) (j : ℕ) :
    v.intValuation (g j) = v.intValuation (g 0) := by
  induction' j with j ih;
  · rfl;
  · rw [ hstep, Vanish.Foundations.intValuation_eq_of_ringEquiv_fixes v e hfix, ih ]

/-
**Two-point constancy.**  Any two members of a Frobenius Gauss-sum orbit have
equal local valuation.
-/
theorem gaussSum_intValuation_orbit_const (v : HeightOneSpectrum R) (e : R ≃+* R)
    (hfix : Ideal.map (e : R →+* R) v.asIdeal = v.asIdeal) (g : ℕ → R)
    (hstep : ∀ j, g (j + 1) = e (g j)) (i j : ℕ) :
    v.intValuation (g i) = v.intValuation (g j) := by
  rw [gaussSum_intValuation_frobenius_orbit v e hfix g hstep i,
    gaussSum_intValuation_frobenius_orbit v e hfix g hstep j]

end Vanish.Foundations