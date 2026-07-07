import RequestProject.Foundations.KasamiAdditiveEnergyBE3b
import Mathlib

/-!
# Foundations, Layer BE3.3.0 — the `W⁴ ↔ ∑ R²` Parseval bridge, re-keyed at fixed `a`

This module formalizes the **first layer of the open deep core BE3.3** of
`Docs/VanishFutureDirections.md` §8.3: the Parseval re-keying that expresses the
autocorrelation **second moment** in a fixed nonzero direction `a` through the
already-proven differential spectrum.

## The mathematical content

The project already proves the *frequency-keyed* Wiener–Khinchin / Parseval
bridge `walsh_fourth_sum_a`:

  `∑_a W(a,b)⁴ = q · ∑_u R_b(u)²`,   `R_b(u) = ∑ₓ χ(b·(f(x+u)+f x))`,

relating the Walsh **fourth** moment (summed over the linear frequency `a`, at a
fixed multiplier `b`) to the autocorrelation **second** moment.  Its companion at
the level of the autocorrelation itself is `autocorr_sq_sum_b`:

  `∑_b R_b(u)² = q · ∑_c N(u,c)²`,

the second Parseval, tying `∑R²` to the differential spectrum `N(u,·)` (the
derivative collision counts, i.e. the *image* data).

For the **AB / image direction** one fixes the derivative direction `a` and lets
the multiplier `s` vary: `R(s) := autocorrScaled f s a = ∑ₓ χ(s·Δf_a x)` is the
cross-correlation spectrum whose moments BE3.3 must evaluate.  *Re-keying*
`autocorr_sq_sum_b` at `u = a` is exactly the bridge

  `∑_s R(s)² = q · ∑_c N(a,c)²`   (`autocorr_secondMoment_eq_diffCount_sq`),

expressing the cross-correlation second moment via the known differential
spectrum of `f` in direction `a`.  For an **APN** function the differential
second moment is pinned (`diffCount_sq_sum_apn`: `∑_c N(a,c)² = 2q` for `a ≠ 0`),
which closes the second moment to an explicit value:

  `∑_s R(s)² = 2q²`   (`autocorr_secondMoment_apn`),
  `∑_{s≠0} R(s)² = q²`   (`autocorr_secondMoment_punctured_apn`),

since the zero frequency contributes `R(0)² = q²` (`autocorrScaled_zero`).

This is the **second-moment** companion of the BE3 *fourth*-moment reduction
`additiveEnergy_value_iff_fourthMoment`: it supplies the `∑R²` half of the
`W⁴ ↔ ∑R²` Parseval bookkeeping that BE3.3.1 (the second-derivative AB
multiplicities, the genuinely open content) will combine with the AB Walsh
fourth moment `∑_b W(a,b)⁴ = 2q³` (`fourth_moment_apn`).

## What is established (sorry-free)

* `autocorr_secondMoment_eq_diffCount_sq` — the re-keyed Parseval bridge
  `∑_s R(s)² = q · ∑_c N(a,c)²` (general `f`).
* `autocorr_secondMoment_apn` — the APN closed form `∑_s R(s)² = 2q²` (`a ≠ 0`).
* `autocorr_secondMoment_punctured_apn` — the punctured form
  `∑_{s≠0} R(s)² = q²` (`a ≠ 0`).

## Scope

This layer is sorry-free; it is the project-internal **Parseval re-keying** that
needs no theory absent from Mathlib (it is built entirely on `autocorr_sq_sum_b`,
`diffCount_sq_sum_apn`, and `autocorrScaled_zero`).  The genuinely open content of
BE3.3 — the per-value multiplicities of the second-order derivative (BE3.3.1) and
the resulting exact off-diagonal energy `16·offDiagEnergy = q³ − 2q²` (BE3.3.2) —
is the AB-vs-APN distinction, deliberately neither axiomatized nor `sorry`-ed.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3, §4.1 (the second and fourth moments of
the Fourier transform); Carlet, Ch. 6 (AB/APN functions and the Walsh spectrum);
Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The re-keyed Parseval bridge (`∑R² ↔ image second moment`) -/

/--
**The `∑R²` Parseval bridge, re-keyed at a fixed direction `a`.**  For the
cross-correlation spectrum `R(s) = autocorrScaled f s a` in direction `a`, the
autocorrelation second moment equals `q` times the differential second moment of
`f` in direction `a`:

  `∑_s R(s)² = q · ∑_c N(a,c)²`.

This is `autocorr_sq_sum_b` read in the AB / image direction (`u = a`, multiplier
`s`), expressing `∑R²` through the known differential spectrum `N(a,·)`.
-/
theorem autocorr_secondMoment_eq_diffCount_sq (f : F → F) (a : F) :
    ∑ s : F, (autocorrScaled f s a) ^ 2
      = (Fintype.card F : ℤ) * ∑ c : F, (diffCount f a c : ℤ) ^ 2 :=
  autocorr_sq_sum_b f a

/-! ## 2. The APN closed form for the second moment -/

/--
**The APN second moment `∑_s R(s)² = 2q²`.**  Combining the re-keyed Parseval
bridge with the APN differential second moment `∑_c N(a,c)² = 2q`
(`diffCount_sq_sum_apn`, valid for `a ≠ 0`).
-/
theorem autocorr_secondMoment_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ∑ s : F, (autocorrScaled f s a) ^ 2 = 2 * (Fintype.card F : ℤ) ^ 2 := by
  rw [autocorr_secondMoment_eq_diffCount_sq, diffCount_sq_sum_apn hcard f hf a ha]
  ring

/-! ## 3. The punctured APN second moment -/

/--
**The punctured APN second moment `∑_{s≠0} R(s)² = q²`.**  Splitting the zero
frequency `R(0)² = q²` (`autocorrScaled_zero`) off the full second moment
`∑_s R(s)² = 2q²`.
-/
theorem autocorr_secondMoment_punctured_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 2
      = (Fintype.card F : ℤ) ^ 2 := by
  have hfull := autocorr_secondMoment_apn hcard f hf a ha
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F)),
    MTuple.autocorrScaled_zero] at hfull
  nlinarith [hfull]

end Vanish.Foundations
