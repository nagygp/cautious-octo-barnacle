import Mathlib
import RequestProject.Foundations.FirstPrinciples.Decomp.PadicGammaDecomp

/-!
# Transcription — Leaf L3, module 1: the Gross–Koblitz statement and its `Γ_p`-unit core

This module opens the transcription of leaf **L3** (the integer Gross–Koblitz
factorization `g = ± 2^{s₂(e)} · odd`, `FirstPrinciplesTranscriptionRoadmap.md`),
"the next chapter after L2": leaf L2 (`PadicGammaDecomp`) supplied Morita's
`p`-adic Gamma function `Γ_p` and the fact that **every value `Γ_p(x)` is a unit**
(`padicGamma_unit`); this module is the Gross–Koblitz *application* of it.

The Gross–Koblitz formula expresses the Teichmüller Gauss sum as
`g = − π^{s₂(e)} · ∏_i Γ_p(⟨…⟩)` over `ℚ_p(π)` with `π` a uniformizer of `p`-power
valuation, each `Γ_p`-factor a **unit**.  The whole `2`-adic valuation therefore
comes from the `π^{s₂(e)}` prefactor.  The arithmetic core of that extraction — that
a finite **product of `Γ_p`-units is a unit**, hence contributes nothing to the
valuation — is proved here as a **real proof**:

* `padicGamma_isUnit` — re-export of `padicGamma_unit` (L2): `IsUnit (Γ_p x)`;
* `padicGamma_prod_isUnit` — a finite product `∏_{i∈s} Γ_p (f i)` is a unit;
* `padicGamma_prod_norm` — such a product has `p`-adic norm `1`.

It then gives the **real reduction** `gaussInt_factor_of_padic_grossKoblitz`: *given*
the Gross–Koblitz `2`-adic identity `(g : ℤ₂) = (−1)^c · 2^c · u` with `u` a unit
(the genuine deep input, the Gross–Koblitz formula itself, abstracted into the
hypothesis), the integer Gauss sum `g` factors as `± 2^{c} · (odd integer)`.  This
is the bridge that lets `StickelbergerDecomp.kasamiGaussInt_factor_two_pow` be
discharged once the `2`-adic identity is supplied; here it is proved in full.

## Sources

* B. Gross, N. Koblitz, *Gauss sums and the p-adic Γ-function*, Ann. of Math. 109
  (1979), 569–581.
* L. Washington, *Introduction to Cyclotomic Fields*, Ch. 6.
* A. Robert, *A Course in p-adic Analysis*, Ch. VII.
* Project: `PadicGammaDecomp.padicGamma`, `PadicGammaDecomp.padicGamma_unit`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open Vanish.Foundations.FirstPrinciples.Decomp

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **`Γ_p` is a unit (re-export of the L2 result).**  Morita's `p`-adic Gamma
function takes unit values everywhere. -/
theorem padicGamma_isUnit (x : ℤ_[p]) : IsUnit (padicGamma x) :=
  padicGamma_unit x

/-- **A product of `Γ_p`-units is a unit (real proof).**  Any finite product
`∏_{i∈s} Γ_p (f i)` is a unit of `ℤ_[p]`; in the Gross–Koblitz formula this is the
product of Γ_p-factors, contributing nothing to the `2`-adic valuation. -/
theorem padicGamma_prod_isUnit {ι : Type*} (s : Finset ι) (f : ι → ℤ_[p]) :
    IsUnit (∏ i ∈ s, padicGamma (f i)) :=
  IsUnit.prod_iff.mpr (fun i _ => padicGamma_isUnit (f i))

/-- **A product of `Γ_p`-units has norm one (real proof).**  Consequently its
`p`-adic valuation is `0`. -/
theorem padicGamma_prod_norm {ι : Type*} (s : Finset ι) (f : ι → ℤ_[p]) :
    ‖∏ i ∈ s, padicGamma (f i)‖ = 1 :=
  PadicInt.isUnit_iff.mp (padicGamma_prod_isUnit s f)

/-
**Integer factorization from the Gross–Koblitz `2`-adic identity (real proof).**
The genuine deep input — the Gross–Koblitz formula `g = − π^{c} · ∏_i Γ_p(⟨…⟩)`
with each `Γ_p`-factor a unit (`padicGamma_prod_isUnit`) — is abstracted into the
hypothesis `(g : ℤ₂) = (−1)^c · 2^c · u`, `u` a unit.  *From it* the integer Gauss
sum `g` factors as `± 2^{c} · (odd integer)`, where `c = s₂(e)`.  This is the real
bridge underlying `StickelbergerDecomp.kasamiGaussInt_factor_two_pow`.
-/
theorem gaussInt_factor_of_padic_grossKoblitz (g : ℤ) (c : ℕ)
    (u : ℤ_[2]) (hu : IsUnit u) (hGK : (g : ℤ_[2]) = (-1) ^ c * 2 ^ c * u) :
    ∃ m : ℤ, Odd m ∧ (g = 2 ^ c * m ∨ g = -(2 ^ c * m)) := by
  obtain ⟨ m, hm ⟩ := hu.exists_left_inv; replace hm := congr_arg ( fun x => x ) hm; simp_all +decide [ ← mul_assoc, ← eq_sub_iff_add_eq' ] ;
  -- From the hypothesis `hGK`, we know that `g = (-1)^c * 2^c * u` with `u` a unit.
  -- Since `u` is a unit, `(-1)^c * u` is also a unit.
  have h_unit : IsUnit ((-1 : ℤ_[2]) ^ c * u) := by
    exact IsUnit.mul ( by cases c <;> aesop ) hu;
  have h_val : (padicValRat 2 (g : ℚ) : ℤ) = c := by
    have h_val : ‖(g : ℤ_[2])‖ = (2 : ℝ) ^ (-c : ℤ) := by
      have h_norm : ‖(-1 : ℤ_[2]) ^ c * u‖ = 1 :=
        PadicInt.isUnit_iff.mp h_unit
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      erw [ PadicInt.norm_p ] ; norm_num;
      norm_num [ ← inv_pow ];
    have h_val : ‖(g : ℤ_[2])‖ = (2 : ℝ) ^ (-padicValRat 2 (g : ℚ) : ℤ) := by
      convert PadicInt.norm_eq_zpow_neg_valuation _;
      · norm_num [ PadicInt.valuation ];
      · aesop;
    simp_all +decide [ zpow_neg, zpow_ofNat ];
  -- From the hypothesis `h_val`, we know that `2^c ∣ g` and `¬ (2^(c+1) ∣ g)`.
  have h_div : (2 : ℤ) ^ c ∣ g ∧ ¬(2 : ℤ) ^ (c + 1) ∣ g := by
    have h_div : padicValInt 2 g = c := by
      convert h_val using 1;
      norm_num [ padicValRat ];
    rw [ ← h_div ];
    exact ⟨ by simpa using Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ ), by simpa using Int.natCast_dvd.not.mpr ( Nat.pow_succ_factorization_not_dvd ( by aesop ) ( by decide ) ) ⟩;
  obtain ⟨ m, rfl ⟩ := h_div.1; simp_all +decide [ parity_simps ] ;
  exact ⟨ m, Int.odd_iff.mpr ( Int.emod_two_ne_zero.mp fun h => h_div <| mul_dvd_mul_left _ <| Int.dvd_of_emod_eq_zero h ), Or.inl rfl ⟩

end Vanish.Foundations.FirstPrinciples.Transcribe