import ConjecturesMTupleTripleCount.Foundations.WalshTransform

/-!
# Foundations, Layer 4 — Wiener–Khinchin: power spectrum ↔ autocorrelation

This module realizes **Layer 4** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`).  It connects the project's hand-rolled
Wiener–Khinchin step `WalshAB.walsh_sq_eq_autocorr_sum`
(`W(a,b)² = ∑_u χ(a·u)·R_b(u)`) to the general, character-agnostic identity
`Vanish.Foundations.fourierTransform_wienerKhinchin`
(`ConjecturesMTupleTripleCount/Foundations/Fourier.lean`), exactly as Layers 2–3 did for
orthogonality and Parseval.

The single observation is that, for a fixed mask `b`, the Walsh transform
`a ↦ W(a,b)` is the discrete Fourier transform of `gᵦ x := χ(b·f x)`:

  `W(a,b) = fourierTransform chiAddChar gᵦ a`.

Wiener–Khinchin (`fourierTransform_wienerKhinchin`) then says the power spectrum
`W(a,b)·W(a,b)` (here `W(a,b)²`, since `χ⁻¹ = χ` in characteristic two) is the
Fourier transform of the cross-correlation `crossCorr gᵦ gᵦ`, and that
cross-correlation is exactly the project's scaled autocorrelation
`WalshAB.autocorrScaled f b`.

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2
(Wiener–Khinchin theorem); Carlet, *Boolean Functions for Cryptography and
Coding Theory*, Ch. 5.

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the general identity is proved
once (in `Fourier.lean`) and *reused* here (DRY); the two bridging lemmas each
have a single responsibility (recognize the transform; identify the
correlation).
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
For a fixed mask `b`, the project's Walsh transform `a ↦ walsh f a b` is the
discrete Fourier transform of `gᵦ x = χ (b · f x)`.
-/
theorem walsh_eq_fourierTransform_chi (f : F → F) (a b : F) :
    (walsh f a b : ℤ)
      = fourierTransform (chiAddChar : AddChar F ℤ) (fun x => χ (b * f x)) a := by
  unfold walsh fourierTransform;
  simp +decide [ chiAddChar_apply, χ_mul ]

/-
The cross-correlation of `gᵦ x = χ (b · f x)` with itself is exactly the
project's scaled autocorrelation `R_b`.
-/
theorem crossCorr_chi_eq_autocorrScaled (f : F → F) (b u : F) :
    crossCorr (fun x => χ (b * f x)) (fun x => χ (b * f x)) u
      = autocorrScaled f b u := by
  convert congr_arg ( fun x : ℤ => x ) ( Finset.sum_congr rfl fun x _ => ?_ ) using 1;
  simp +decide [ mul_add, χ_mul ]

/-
**The project's Wiener–Khinchin step as a specialization.**  Recovers
`WalshAB.walsh_sq_eq_autocorr_sum`: `W(a,b)² = ∑_u χ(a·u)·R_b(u)`, now a
corollary of the general `fourierTransform_wienerKhinchin`.
-/
theorem walsh_sq_eq_autocorr_sum_via_foundation (f : F → F) (a b : F) :
    walsh f a b ^ 2 = ∑ u : F, χ (a * u) * autocorrScaled f b u := by
  have hwk := fourierTransform_wienerKhinchin (chiAddChar : AddChar F ℤ)
    (fun x => χ (b * f x)) (fun x => χ (b * f x)) a
  rw [chiAddChar_inv] at hwk
  rw [sq, walsh_eq_fourierTransform_chi f a b, hwk]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [chiAddChar_apply, crossCorr_chi_eq_autocorrScaled]

end Vanish.Foundations