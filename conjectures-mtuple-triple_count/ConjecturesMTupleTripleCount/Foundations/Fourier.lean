import ConjecturesMTupleTripleCount.Foundations.AddCharCount

/-!
# Foundations — the discrete Fourier transform, Plancherel and Wiener–Khinchin

This module factors out the **reusable, Mathlib-only kernel** underlying the
project's Walsh/Parseval results (`ConjecturesMTupleTripleCount/Foundations/WalshTransform.lean`)
and the autocorrelation/power-spectrum duality (Layer 4 of
`Docs/VanishFutureDirections.md`).

Everything here is stated for an arbitrary **finite commutative ring `R`**, a
**primitive additive character** `ψ : AddChar R R'` into a domain `R'`, and
*arbitrary* functions `g, h : R → R'` — there is no mention of Walsh, Boolean
functions, bijections, fields, or characteristic two.  That is deliberate: these
are the genuinely general statements one would propose for Mathlib, with the
project's Walsh-flavoured results recovered as thin specializations elsewhere.

## Contents

* `fourierTransform ψ g a = ∑ x, ψ (a·x) · g x` — the discrete Fourier transform
  of `g` with respect to `ψ`.
* `crossCorr g h u = ∑ x, g (x + u) · h x` — the (cyclic) cross-correlation.
* `fourierTransform_parseval` — **Plancherel/Parseval**:
  `∑_b 𝓕ψ g b · 𝓕(ψ⁻¹) h b = |R| · ∑_x g x · h x`.
* `fourierTransform_wienerKhinchin` — **Wiener–Khinchin**:
  `𝓕ψ g a · 𝓕(ψ⁻¹) h a = ∑_u ψ (a·u) · crossCorr g h u`
  (the power spectrum is the Fourier transform of the cross-correlation).

## Relation to Mathlib

Mathlib's `ZMod.dft` (`Mathlib/Analysis/Fourier/ZMod.lean`) provides a discrete
Fourier transform, but only over `ZMod N`, only for the *canonical* character
`stdAddChar` into `ℂ`, and only valued in `ℂ`-modules; it proves Fourier
inversion (`ZMod.dft_dft`) but **not** Plancherel/Parseval, and is unavailable in
positive characteristic or over a general domain.  The statements here are purely
algebraic (no analysis), hold over any finite commutative ring with any primitive
character into any domain, and supply the missing Plancherel and Wiener–Khinchin
identities.  See `Docs/UpstreamAssessment.md`.

## Sources

Rudin, *Fourier Analysis on Groups*; Terras, *Fourier Analysis on Finite Groups
and Applications*; Cusick–Stănică, *Cryptographic Boolean Functions and
Applications*, Ch. 2 (Wiener–Khinchin).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): one definition per
responsibility, intention-revealing names, and the orthogonality input taken
verbatim from Mathlib (`AddChar.sum_mulShift`) rather than re-derived (DRY).
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators

variable {R R' : Type*} [CommRing R] [Fintype R] [DecidableEq R] [CommRing R']

/-! ## The discrete Fourier transform and cross-correlation -/

/-- **Discrete Fourier transform.**  For an additive character `ψ : AddChar R R'`
and `g : R → R'`, the Fourier coefficient at frequency `a` is
`∑ x, ψ (a·x) · g x`. -/
def fourierTransform (ψ : AddChar R R') (g : R → R') (a : R) : R' :=
  ∑ x : R, ψ (a * x) * g x

/-- **Cyclic cross-correlation** of `g, h : R → R'`:
`crossCorr g h u = ∑ x, g (x + u) · h x`. -/
def crossCorr (g h : R → R') (u : R) : R' :=
  ∑ x : R, g (x + u) * h x

/-! ## Plancherel / Parseval

Summing the product of a Fourier coefficient and its conjugate over all
frequencies recovers the inner product (up to the `|R|` factor).  This is the
reusable Plancherel kernel; the project's `vectorialWalsh_parseval` is a thin
specialization of it. -/

/-
**Plancherel / Parseval.**  For a primitive additive character `ψ` of a
finite commutative ring `R` into a domain `R'`, and arbitrary `g, h : R → R'`,
`∑_b 𝓕ψ g b · 𝓕(ψ⁻¹) h b = |R| · ∑_x g x · h x`.

Here `ψ⁻¹` is the conjugate character (`ψ⁻¹ z = ψ (-z)`), the correct
harmonic-analytic conjugate in any characteristic.
-/
theorem fourierTransform_parseval [IsDomain R']
    {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) (g h : R → R') :
    ∑ b : R, fourierTransform ψ g b * fourierTransform ψ⁻¹ h b
      = (Fintype.card R : R') * ∑ x : R, g x * h x := by
  -- Expand the product of sums into a double sum.
  have h_expand : ∑ b : R, (∑ x : R, ψ (b * x) * g x) * (∑ y : R, ψ⁻¹ (b * y) * h y) = ∑ x : R, ∑ y : R, g x * h y * ∑ b : R, ψ (b * (x - y)) := by
    simp +decide only [mul_comm, Finset.sum_mul _ _ _];
    simp +decide only [mul_sum _ _ _, mul_sub];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun x _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => _ );
    simp +decide [ mul_assoc, mul_left_comm, sub_eq_add_neg, AddChar.map_add_eq_mul ];
  -- Apply the orthogonality relation of the character $\psi$.
  have h_ortho : ∀ x y : R, ∑ b : R, ψ (b * (x - y)) = if x = y then (Fintype.card R : R') else 0 := by
    intro x y; split_ifs with hxy; simp_all +decide [ mul_comm ] ;
    convert AddChar.sum_mulShift ( x - y ) hψ using 1;
    simp +decide [ sub_eq_zero, hxy ];
  convert h_expand using 1;
  simp +decide [ h_ortho, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ]

/-! ## Wiener–Khinchin

A single power-spectrum value (the product of a Fourier coefficient and its
conjugate, *at one frequency*) is the Fourier transform of the cross-correlation.
Unlike Plancherel this is a purely formal change of variables: it needs neither
primitivity of `ψ` nor that `R'` be a domain. -/

/-
**Wiener–Khinchin.**  For any additive character `ψ`, any `g, h : R → R'`
and any frequency `a`,
`𝓕ψ g a · 𝓕(ψ⁻¹) h a = ∑_u ψ (a·u) · crossCorr g h u`.
-/
theorem fourierTransform_wienerKhinchin
    (ψ : AddChar R R') (g h : R → R') (a : R) :
    fourierTransform ψ g a * fourierTransform ψ⁻¹ h a
      = ∑ u : R, ψ (a * u) * crossCorr g h u := by
  -- Let's simplify the left-hand side using the definitions of `fourierTransform` and `crossCorr`.
  have lhs_simp : ∑ x, ψ (a * x) * g x * ∑ y, ψ⁻¹ (a * y) * h y = ∑ x, ∑ y, ψ (a * x) * ψ⁻¹ (a * y) * g x * h y := by
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_assoc];
  -- Using the fact that `ψ⁻¹ (a * y) = ψ (-a * y)`, we can rewrite the inner sum.
  have lhs_simp' : ∑ x, ∑ y, ψ (a * x) * ψ⁻¹ (a * y) * g x * h y = ∑ x, ∑ y, ψ (a * (x - y)) * g x * h y := by
    simp +decide [ mul_sub, AddChar.map_sub_eq_div ];
    simp +decide [ sub_eq_add_neg, AddChar.map_add_eq_mul ];
  -- Substitute $u = x - y$ into the double sum.
  have lhs_simp'' : ∑ x, ∑ y, ψ (a * (x - y)) * g x * h y = ∑ u, ∑ x, ψ (a * u) * g x * h (x - u) := by
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.fst - x.snd, x.fst ⟩ ) _ _ _ _ <;> simp +decide;
    · grind;
    · exact fun b => ⟨ b.2, b.2 - b.1, by simp +decide ⟩;
  convert lhs_simp.trans ( lhs_simp'.trans lhs_simp'' ) using 1;
  · unfold fourierTransform; simp +decide [ Finset.sum_mul _ _ _ ] ;
  · simp +decide only [crossCorr, Finset.mul_sum _ _ _, mul_assoc];
    exact Finset.sum_congr rfl fun _ _ => by rw [ ← Equiv.sum_comp ( Equiv.subRight ‹_› ) ] ; simp +decide [ mul_assoc, mul_comm ] ;

end Vanish.Foundations