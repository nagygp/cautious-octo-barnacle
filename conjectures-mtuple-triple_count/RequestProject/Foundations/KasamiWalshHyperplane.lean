import RequestProject.Foundations.WienerKhinchinInversion
import RequestProject.Foundations.KasamiTwoAdicValuation
import RequestProject.Core.KasamiAB
import Mathlib

/-!
# Foundations, interim layer for input (A) — the Walsh-support ↔ hyperplane divisibility

This module formalizes the **cheaper interim step** of the divisibility input (A)
isolated in `Docs/VanishFutureDirections.md` §10: the reduction of the
cross-correlation divisibility `2^{(n+1)/2} ∣ R(s)` to a *hyperplane count
divisibility* on the Walsh support, and its **unconditional discharge for the
small Kasami exponents** `k = 1, 2`.

## The mathematical content

The Wiener–Khinchin inversion bridge
(`Vanish.Foundations.autocorrScaled_ab_eq_support_sum`) shows that, for an
almost-bent permutation `f`, every autocorrelation value is twice a character sum
over the Walsh support:

  `R_b(u) = autocorrScaled f b u = 2 · ∑_{a ∈ Supp(b)} χ(a · u)`,

where `Supp(b) = {a : walsh f a b ≠ 0}`.  Since `χ z = (-1)^{Tr z}`, that
character sum is exactly a **trace-hyperplane count difference**

  `∑_{a ∈ Supp(b)} χ(a · u) = #{a ∈ Supp(b) : Tr(a·u) = 0} − #{a ∈ Supp(b) : Tr(a·u) ≠ 0}`
                            =: `hyperplaneDiff (Supp(b)) u`.

Thus the divisibility input **(A)** `2^{(n+1)/2} ∣ R_b(u)` is *equivalent* (for `n`
odd, AB permutations) to the cleaner statement

  `2^{(n-1)/2} ∣ hyperplaneDiff (Supp(b)) u`

— a divisibility purely about how the Walsh support meets the affine hyperplanes
`{a : Tr(a·u) = 1}`.  This is the "Walsh-support ↔ hyperplane divisibility"
reformulation.  For the **quadratic Kasami exponents** `k = 1` (`d 1 = 3`) and
`k = 2` (`d 2 = 13`) the left side is already a *theorem* of the project
(`kasami_one_crossCorr_hdiv`, `kasami_two_crossCorr_hdiv`, proven unconditionally
from the vanishing third derivative / quadratic Gauss-sum route), so the
hyperplane divisibility falls out unconditionally for these cases.

## What is established (sorry-free)

* `sum_chi_eq_hyperplaneDiff` — the character sum is the hyperplane count
  difference (general `S`, `u`).
* `two_pow_dvd_two_mul_iff` — the elementary divisibility shift
  `2^{m+1} ∣ 2·D ↔ 2^m ∣ D`.
* `autocorrScaled_ab_eq_hyperplaneDiff` — for an AB permutation,
  `R_b(u) = 2 · hyperplaneDiff (walshSupport f b) u`.
* `two_pow_dvd_autocorr_ab_iff` — the equivalence of input (A) with the
  hyperplane divisibility (`n` odd, AB permutation).
* `hyperplaneDiff_div_of_crossCorr_hdiv` — the forward implication packaging.
* `kasami_one_walsh_hyperplane_div`, `kasami_two_walsh_hyperplane_div` — the
  **unconditional** hyperplane divisibility for the small Kasami exponents
  `k = 1, 2`.

## Scope

This layer is sorry-free.  It supplies the documented interim reformulation of
input (A) and discharges it unconditionally for `k ≤ 2`.  The general-`k`
hyperplane divisibility (equivalently the full input (A)) remains the deep
McEliece/Ax–Katz core, deliberately neither axiomatized nor `sorry`-ed.

## Sources

Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math., 2000); Carlet, Ch. 5–6;
Cusick–Stănică, Ch. 2.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The Walsh support and the hyperplane count difference -/

/-- The **Walsh support** of `f` at multiplier `b`: the frequencies `a` with
nonzero Walsh coefficient. -/
noncomputable def walshSupport (f : F → F) (b : F) : Finset F :=
  univ.filter (fun a : F => walsh f a b ≠ 0)

/-- The **trace-hyperplane count difference** inside a finite set `S`, in
direction `u`: `#{a ∈ S : Tr(a·u) = 0} − #{a ∈ S : Tr(a·u) ≠ 0}`.  This is the
value of the additive-character sum `∑_{a ∈ S} χ(a·u)`. -/
noncomputable def hyperplaneDiff (S : Finset F) (u : F) : ℤ :=
  ((S.filter (fun a : F => Tr (a * u) = 0)).card : ℤ)
    - ((S.filter (fun a : F => Tr (a * u) ≠ 0)).card : ℤ)

/-
**The character sum is the hyperplane count difference.**  Since
`χ z = (-1)^{Tr z}`, summing `χ(a·u)` over a finite set counts the points with
`Tr(a·u) = 0` with sign `+1` and the rest with sign `-1`.
-/
omit [Fintype F] [DecidableEq F] in
theorem sum_chi_eq_hyperplaneDiff (S : Finset F) (u : F) :
    ∑ a ∈ S, χ (a * u) = hyperplaneDiff S u := by
  have h_char_sum : ∀ a ∈ S, χ (a * u) = if Tr (a * u) = 0 then 1 else -1 :=
    fun a _ => rfl
  rw [ Finset.sum_congr rfl h_char_sum ] ; simp +decide [ hyperplaneDiff ] ;
  simp +decide [ Finset.sum_ite, sub_eq_add_neg ]

/-! ## 2. The elementary divisibility shift -/

/-
**Divisibility shift.**  `2^{m+1} ∣ 2·D ↔ 2^m ∣ D`.
-/
theorem two_pow_dvd_two_mul_iff (m : ℕ) (D : ℤ) :
    (2 : ℤ) ^ (m + 1) ∣ 2 * D ↔ (2 : ℤ) ^ m ∣ D := by
  rw [pow_succ, mul_comm ((2 : ℤ) ^ m) 2, mul_dvd_mul_iff_left (two_ne_zero' ℤ)]

/-! ## 3. The AB hyperplane bridge -/

/-
**AB support-sum as a hyperplane count difference.**  For an almost-bent
permutation `f` and `b ≠ 0`, every autocorrelation value is twice the
hyperplane count difference over the Walsh support:

  `R_b(u) = 2 · hyperplaneDiff (walshSupport f b) u`.
-/
theorem autocorrScaled_ab_eq_hyperplaneDiff {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) {f : F → F} (hf : Function.Bijective f)
    (hAB : IsAB hcard f) (b : F) (hb : b ≠ 0) (u : F) :
    autocorrScaled f b u = 2 * hyperplaneDiff (walshSupport f b) u := by
  rw [ ← sum_chi_eq_hyperplaneDiff, autocorrScaled_ab_eq_support_sum hcard hf hAB b hb u ];
  rfl

/-! ## 4. The reformulation of input (A) -/

/-
**Input (A) ⟺ hyperplane divisibility.**  For `n` odd and an AB permutation
`f`, the divisibility `2^{(n+1)/2} ∣ R_b(u)` is equivalent to
`2^{(n-1)/2} ∣ hyperplaneDiff (walshSupport f b) u`.
-/
theorem two_pow_dvd_autocorr_ab_iff {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) {f : F → F} (hf : Function.Bijective f) (hAB : IsAB hcard f)
    (b : F) (hb : b ≠ 0) (u : F) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled f b u
      ↔ (2 : ℤ) ^ ((n - 1) / 2) ∣ hyperplaneDiff (walshSupport f b) u := by
  rw [ autocorrScaled_ab_eq_hyperplaneDiff hcard hf hAB b hb u ];
  rcases hodd with ⟨ k, rfl ⟩ ; norm_num [ Nat.add_div ];
  rw [ pow_succ', mul_dvd_mul_iff_left ( by norm_num ) ]

/-- **Forward implication packaging.**  From input (A) for an AB permutation we
obtain the hyperplane divisibility. -/
theorem hyperplaneDiff_div_of_crossCorr_hdiv {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hodd : Odd n) {f : F → F}
    (hf : Function.Bijective f) (hAB : IsAB hcard f) (b : F) (hb : b ≠ 0) (u : F)
    (hdiv : (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled f b u) :
    (2 : ℤ) ^ ((n - 1) / 2) ∣ hyperplaneDiff (walshSupport f b) u :=
  (two_pow_dvd_autocorr_ab_iff hcard hodd hf hAB b hb u).1 hdiv

/-! ## 5. Unconditional discharge for the small Kasami exponents `k = 1, 2` -/

/-
**Hyperplane divisibility for `k = 1` (`d 1 = 3`).**  Over `GF(2ⁿ)` with `n`
odd, `1 < n` and `s ≠ 0`, the Walsh support of `x ↦ x^{d 1}` at multiplier `s`
meets the trace hyperplanes in direction `a` with count difference divisible by
`2^{(n-1)/2}`.  This is unconditional, built on `kasami_one_crossCorr_hdiv`.
-/
theorem kasami_one_walsh_hyperplane_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 1 < n) (a s : F) (hs : s ≠ 0) :
    (2 : ℤ) ^ ((n - 1) / 2)
      ∣ hyperplaneDiff (walshSupport (fun x : F => x ^ d 1) s) a := by
  convert Vanish.Foundations.hyperplaneDiff_div_of_crossCorr_hdiv hcard hodd _ _ s hs a ( kasami_one_crossCorr_hdiv hcard hodd a s ) using 1;
  · convert KasamiAB.kasami_bijective hcard 1 ( by decide ) ( Nat.coprime_one_left n ) hodd ( by linarith ) using 1;
  · exact KasamiAB.kasami_is_ab hcard 1 ( by decide ) hkn ( Nat.coprime_one_left _ ) hodd ( by linarith )

/-
**Hyperplane divisibility for `k = 2` (`d 2 = 13`).**  Over `GF(2ⁿ)` with `n`
odd, `2 < n` and `s ≠ 0`, the Walsh support of `x ↦ x^{d 2}` at multiplier `s`
meets the trace hyperplanes in direction `a` with count difference divisible by
`2^{(n-1)/2}`.  Unconditional, built on `kasami_two_crossCorr_hdiv`.
-/
theorem kasami_two_walsh_hyperplane_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (hkn : 2 < n) (a s : F) (hs : s ≠ 0) :
    (2 : ℤ) ^ ((n - 1) / 2)
      ∣ hyperplaneDiff (walshSupport (fun x : F => x ^ d 2) s) a := by
  apply_mod_cast hyperplaneDiff_div_of_crossCorr_hdiv hcard hodd;
  · apply KasamiAB.kasami_bijective hcard 2 (by norm_num) (by
    exact Nat.prime_two.coprime_iff_not_dvd.mpr ( by simpa [ ← even_iff_two_dvd ] using hodd )) hodd (by omega);
  · apply KasamiAB.kasami_is_ab hcard 2 (by norm_num) (by
    exact hkn) (by
    exact Nat.prime_two.coprime_iff_not_dvd.mpr ( by simpa [ ← even_iff_two_dvd ] using hodd )) (by omega);
    linarith;
  · exact hs;
  · exact_mod_cast Vanish.Foundations.kasami_two_crossCorr_hdiv hcard hodd a s

end Vanish.Foundations