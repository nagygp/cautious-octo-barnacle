/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Autocorrelation and Wiener-Khinchin Identity

This module develops the autocorrelation function of the additive character
and establishes its relationship to the Walsh-Hadamard transform via the
Wiener-Khinchin identity:
  `C_f(a, c) = (1/2^n) ∑_b W_{c·f}(b)^2 · χ(a·b)`

## Main definitions
- `autoCorr f a c`: the autocorrelation `∑_x χ(c·(f(x+a) + f(x)))`
- `scaledWht f c b`: the WHT `W_{c·f}(b) = ∑_x χ(b·x + c·f(x))`

## Main results
- `wiener_khinchin`: `autoCorr f a c = (1/2^n) ∑_b W_{c·f}(b)^2 · χ(a·b)`
- `autoCorr_zero_val`: `C_f(0, c) = 2^n`
- `autoCorr_via_deriv`: relationship to derivative distribution

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §4.2
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

set_option maxHeartbeats 800000

/-! ### Autocorrelation -/

/-- The autocorrelation function: `C_f(a, c) = ∑_x χ(c·(f(x+a) + f(x)))`.
    Measures the correlation between `f(x+a)` and `f(x)` through the character χ. -/
def autoCorrGen {n : ℕ} (f : F2n n → F2n n) (a c : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (c * (f (x + a) + f x))

/-- The "scaled" WHT: `W_{c·f}(b) = ∑_x χ(b·x + c·f(x))`.
    This is the standard WHT of the function `x ↦ c · f(x)`. -/
def scaledWht {n : ℕ} (f : F2n n → F2n n) (c b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (b * x + c * f x)

/-- The scaled WHT is exactly the WHT of `x ↦ c · f(x)`. -/
theorem scaledWht_eq_wht {n : ℕ} (f : F2n n → F2n n) (c b : F2n n) :
    scaledWht f c b = wht (fun x => c * f x) b := by
  rfl

/-! ### Basic autocorrelation properties -/

/-- `C_f(0, c) = 2^n` for all `c`. -/
theorem autoCorrGen_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (c : F2n n) :
    autoCorrGen f 0 c = 2 ^ n := by
  unfold autoCorrGen
  simp [F2n.add_self, chi_zero, F2n.card n hn]

/-- Autocorrelation factors through chi_add. -/
theorem autoCorrGen_chi_factor {n : ℕ} (f : F2n n → F2n n) (a c : F2n n) :
    autoCorrGen f a c = ∑ x : F2n n, chi n (c * f (x + a)) * chi n (c * f x) := by
  unfold autoCorrGen
  congr 1; ext x
  rw [show c * (f (x + a) + f x) = c * f (x + a) + c * f x by ring]
  exact chi_add _ _

/-! ### Wiener-Khinchin identity -/

/-
The squared scaled WHT can be expressed as a sum involving autocorrelation.
    `W_{c·f}(b)^2 = ∑_a autoCorrGen f a c · χ(b·a)`.
-/
theorem scaledWht_sq_eq_fourier_autoCorr {n : ℕ} (f : F2n n → F2n n) (c b : F2n n) :
    scaledWht f c b ^ 2 = ∑ a : F2n n, autoCorrGen f a c * chi n (b * a) := by
  unfold scaledWht autoCorrGen;
  simp +decide only [pow_two, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ];
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ ← Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.addRight y ) ] ; simp +decide [ mul_add, add_assoc, chi_add ] ;
  refine' Finset.sum_congr rfl fun x hx => _ ; ring;
  rw [ show chi n ( b * y ) ^ 2 = 1 by exact? ] ; ring

/-
**Wiener-Khinchin identity**:
    `2^n · C_f(a, c) = ∑_b W_{c·f}(b)^2 · χ(b·a)`.

    This is the inverse Fourier transform of the power spectral density.
-/
theorem wiener_khinchin {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a c : F2n n) :
    (2 ^ n : ℤ) * autoCorrGen f a c =
    ∑ b : F2n n, scaledWht f c b ^ 2 * chi n (b * a) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ b : F2n n, ∑ a' : F2n n, autoCorrGen f a' c * chi n (b * a') * chi n (b * a) = ∑ a' : F2n n, autoCorrGen f a' c * ∑ b : F2n n, chi n (b * (a' + a)) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; rw [ mul_add ] ; rw [ chi_add ] ; ring;
  -- By the orthogonality of the character χ, we have ∑_b χ(b(a'+a)) = 2^n if a' = a, else 0.
  have h_orthogonality : ∀ a' : F2n n, ∑ b : F2n n, chi n (b * (a' + a)) = if a' = a then (2 ^ n : ℤ) else 0 := by
    intro a'
    have h_orthogonality : ∑ b : F2n n, chi n (b * (a' + a)) = if a' + a = 0 then (2 ^ n : ℤ) else 0 := by
      convert chi_sum hn ( a' + a ) using 1;
    simp_all +decide [ add_eq_zero_iff_eq_neg ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Finset.sum_ite ];
  rw [ ← h_fubini, Finset.sum_congr rfl ] ; intros ; rw [ scaledWht_sq_eq_fourier_autoCorr ] ; ring;
  rw [ Finset.mul_sum _ _ _ ] ; ac_rfl

/-! ### Autocorrelation via derivative distribution -/

/-
The autocorrelation can be expressed using the derivative distribution:
    `C_f(a, c) = ∑_b N_a(b) · χ(c·b)`
    where `N_a(b) = |{x : f(x+a) + f(x) = b}|`.
-/
theorem autoCorrGen_via_deriv {n : ℕ} (f : F2n n → F2n n) (a c : F2n n) :
    autoCorrGen f a c = ∑ b : F2n n,
      ((Finset.univ.filter fun x => f (x + a) + f x = b).card : ℤ) * chi n (c * b) := by
  unfold autoCorrGen;
  simp +decide only [Finset.card_filter];
  simp +decide only [Nat.cast_sum, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-! ### Scaled WHT for AB functions -/

/-- For a bijective power function, the scaled WHT at (c, b) equals the
    original WHT at a shifted argument. Specifically:
    `scaledWht (x ↦ x^d) c b = wht (x ↦ x^d) (b * u⁻¹)`
    where `u^d = c`. -/

/-
When `u ≠ 0` and `u^d = c`, the scaled WHT equals the regular WHT
    at the shifted argument `b * u⁻¹`.
-/
theorem scaledWht_power_shift {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (c b : F2n n) (u : F2n n) (hu0 : u ≠ 0) (hu : u ^ d = c) :
    scaledWht (fun x => x ^ d) c b = wht (fun x => x ^ d) (b * u⁻¹) := by
  apply Finset.sum_bij (fun x _ => u * x);
  · grind +qlia;
  · aesop;
  · exact fun x _ => ⟨ x / u, Finset.mem_univ _, mul_div_cancel₀ _ hu0 ⟩;
  · simp +decide [ ← mul_assoc, hu0, hu ];
    simp +decide [ ← hu, mul_pow ]

/-- For an AB power function, the scaled WHT has the same spectral structure. -/
theorem scaledWht_ab_spectrum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf_pow : ∃ d : ℕ, ∀ x, f x = x ^ d)
    (hf_ab : IsAlmostBent f)
    (c : F2n n) (b : F2n n) :
    scaledWht f c b ^ 2 = 0 ∨ scaledWht f c b ^ 2 = (2 ^ (n + 1) : ℤ) := by
  sorry

end
end Kasami