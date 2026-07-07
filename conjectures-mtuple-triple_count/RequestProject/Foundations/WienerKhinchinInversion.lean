import RequestProject.Foundations.WienerKhinchin
import RequestProject.Foundations.ABSpectrum

/-!
# Foundations — Wiener–Khinchin *inversion*: `R(u)` from the direct power spectrum

The forward Wiener–Khinchin step of the project
(`WalshAB.walsh_sq_eq_autocorr_sum`, re-derived as
`Vanish.Foundations.walsh_sq_eq_autocorr_sum_via_foundation`) expresses the
direct Walsh *power spectrum* `W(a,b)²` as the discrete Fourier transform of the
scaled autocorrelation `R_b(u) = autocorrScaled f b u`:

  `W(a,b)² = ∑_u χ(a·u)·R_b(u)`.

This module supplies the **inverse** direction — the genuinely missing half of
"link the direct Walsh spectrum to `R(s)`": Fourier inversion expresses the
autocorrelation `R_b(u)` *back* in terms of the direct power spectrum,

  `|F|·R_b(u) = ∑_a χ(a·u)·W(a,b)²`     (`autocorrScaled_eq_walsh_sq_sum`).

In characteristic two `χ⁻¹ = χ`, so the inversion is the *same* transform applied
twice, scaled by `|F|`.  This is the precise sense in which the cross-correlation
`R(s)` of the value-set program is *determined by* the direct Walsh spectrum: it
is (up to the `1/|F|` normalisation) the Fourier transform of `a ↦ W(a,b)²`.

## The almost-bent structural corollary

When `f` is almost bent (`IsAB`), the off-axis power spectrum is two-valued,
`W(a,b)² ∈ {0, 2^{n+1}}` for `a ≠ 0`.  For a permutation `f` the axis term
`W(0,b) = 0` whenever `b ≠ 0`, so the inversion collapses to a **support
character sum**:

  `R_b(u) = 2·∑_{a : W(a,b) ≠ 0} χ(a·u)`     (`autocorrScaled_ab_eq_support_sum`).

Thus, for an AB permutation, every autocorrelation value is `2` times a sum of
additive-character values over the Walsh support — exposing that the *only*
remaining content of the divisibility input **(A)** `2^{(n+1)/2} ∣ R(u)` is a
`2^{(n-1)/2}`-divisibility of these support character sums (a statement about how
the Walsh support meets the hyperplanes `{a : χ(a·u) = -1}`), the classical
Kasami/CCD weight-divisibility datum.  This run delivers the bridge; the
support-sum divisibility itself remains the documented deep core.

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2;
Carlet, *Boolean Functions for Cryptography and Coding Theory*, Ch. 5–6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open AddChar Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**Wiener–Khinchin inversion.**  The scaled autocorrelation is, up to the
`1/|F|` normalisation, the discrete Fourier transform of the direct Walsh power
spectrum `a ↦ W(a,b)²`:

  `|F|·R_b(u) = ∑_a χ(a·u)·W(a,b)²`.

Proof: substitute the forward identity `W(a,b)² = ∑_v χ(a·v)·R_b(v)`, swap the
order of summation, and apply dual orthogonality `∑_a χ(a·(u+v)) = |F|·[u+v=0]`
together with `-u = u` in characteristic two.
-/
theorem autocorrScaled_eq_walsh_sq_sum (f : F → F) (b u : F) :
    (Fintype.card F : ℤ) * autocorrScaled f b u
      = ∑ a : F, χ (a * u) * walsh f a b ^ 2 := by
  -- Use the forward Wiener–Khinchin identity to expand the square.
  have h_expand : ∀ a, (walsh f a b) ^ 2 = ∑ v, χ (a * v) * autocorrScaled f b v :=
    fun a => WalshAB.walsh_sq_eq_autocorr_sum f a b
  simp +decide only [h_expand];
  -- By interchanging the order of summation, we can rewrite the right-hand side.
  have h_interchange : ∑ x : F, ∑ v : F, χ (x * u) * χ (x * v) * autocorrScaled f b v = ∑ v : F, autocorrScaled f b v * ∑ x : F, χ (x * (u + v)) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    simp +decide [ mul_add, mul_comm, Finset.mul_sum _ _ _, WalshAB.χ_mul ];
  convert h_interchange.symm using 1;
  · rw [ Finset.sum_eq_single u ] <;> simp +contextual [ WalshAB.χ_sum_dual ];
    · rw [ if_pos ( by rw [ ← two_smul F u, CharTwo.two_eq_zero, zero_smul ] ), mul_comm ];
    · grind;
  · simp +decide only [Finset.mul_sum _ _ _, mul_assoc]

/-
**Almost-bent support-sum form of the autocorrelation.**  For an AB
permutation `f`, every off-axis power-spectrum value is `0` or `2^{n+1}` and the
axis term `W(0,b)` vanishes for `b ≠ 0`, so the inversion collapses to

  `R_b(u) = 2·∑_{a : W(a,b) ≠ 0} χ(a·u)`.
-/
theorem autocorrScaled_ab_eq_support_sum {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f)
    (b : F) (hb : b ≠ 0) (u : F) :
    autocorrScaled f b u
      = 2 * ∑ a ∈ univ.filter (fun a : F => walsh f a b ≠ 0), χ (a * u) := by
  have h_sum : ∑ a : F, χ (a * u) * walsh f a b ^ 2 = ∑ a ∈ Finset.univ.filter (fun a => walsh f a b ≠ 0), χ (a * u) * (2 ^ (n + 1)) := by
    rw [ Finset.sum_filter, Finset.sum_congr rfl ];
    intro a ha; specialize hAB a; by_cases ha' : a = 0 <;> simp_all +decide ;
    · rw [ WalshAB.walsh_a_zero_perm ] <;> aesop;
    · grind;
  convert congr_arg ( fun x : ℤ => x / ( 2 ^ n ) ) h_sum using 1;
  · rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_num [ ← autocorrScaled_eq_walsh_sq_sum f b u, hcard ];
    ring;
  · rw [ ← Finset.sum_mul _ _ _, Int.ediv_eq_of_eq_mul_left (by positivity) ]; ring

end Vanish.Foundations