import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.TraceMonomial

/-!
# Transcription — Leaf L1, module 5: assembling the Gauss-sum bridge `R(s) = ± g`

This is the **fifth and final rung** of the additive→multiplicative character-sum
bridge `GaussSumDecomp.kasami_crossCorr_eq_gaussInt` (leaf **L1** in
`FirstPrinciplesTranscriptionRoadmap.md`).  It assembles the analytic heart
(module 3, `MonomialGaussExpansion.monomial_addCharSum_eq_gaussSum_sum`) and the
Kasami Frobenius/trace → monomial substitution (module 4,
`TraceMonomial.kasami_autocorr_eq_monomial_addCharSum`).

It proves, as a **real proof**, the full Gauss-sum *expansion* of the Kasami
cross-correlation:

* `kasami_autocorr_eq_gaussSum_sum` — there is a unit `c`, an exponent `e ≥ 1`, and
  a multiplicative character `χ₁` of order exactly `d = gcd(e, q−1)` with
  `(R_a(s) : ℂ) = ∑_{j=1}^{d−1} (χ₁ʲ)⁻¹(c)·g(χ₁ʲ, chiC)`.

This is genuinely new content: it combines module 4's monomial form, the existence
of a character of prescribed order over `ℂ`
(`MulChar.exists_mulChar_orderOf`, via a primitive root `exp(2πi/d)`), and module
3's expansion.

It then states, as the single classical **leaf**, the **single-coset collapse**: the
character-power sum reduces to `±` *one* Teichmüller Gauss sum
`g(χ₂, chiC)`.  Classically this is the Stickelberger/cyclotomic-coset fact that
only the characters in one `2`-cyclotomic coset of the Kasami exponent survive and
they conjugate-combine to a single (rational-integer-valued, since `chiC` is
`±1`-valued) Gauss sum (Lidl–Niederreiter Ch. 5; Gross–Koblitz 1979).  This is the
object whose `2`-adic valuation leaf L3 then computes.

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 5.
* Ireland–Rosen, Ch. 8, 14.
* Mathlib: `gaussSum`, `MulChar.exists_mulChar_orderOf`, `Complex.isPrimitiveRoot_exp`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open MulChar AddChar WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Gauss-sum expansion of the Kasami cross-correlation (real proof).**
Combining the Kasami monomial substitution (module 4) with the monomial → Gauss-sum
expansion (module 3) and the existence of a character of prescribed order, the
cross-correlation `R_a(s)`, cast to `ℂ`, is a sum of Teichmüller Gauss sums:
there are a unit `c`, an exponent `e ≥ 1`, and a multiplicative character `χ₁` of
order `d = gcd(e, q−1)` with
`(R_a(s) : ℂ) = ∑_{j=1}^{d−1} (χ₁ʲ)⁻¹(c)·g(χ₁ʲ, chiC)`. -/
theorem kasami_autocorr_eq_gaussSum_sum {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F) (hs : s ≠ 0) :
    ∃ (c : Fˣ) (e : ℕ) (χ₁ : MulChar F ℂ),
      1 ≤ e ∧ orderOf χ₁ = Nat.gcd e (Fintype.card F - 1) ∧
      (autocorrScaled (fun x : F => x ^ d k) s a : ℂ)
        = ∑ j ∈ Finset.Ico 1 (orderOf χ₁),
            ((χ₁ ^ j)⁻¹ (c : F)) * gaussSum (χ₁ ^ j) (chiC : AddChar F ℂ) := by
  obtain ⟨c, e, he, hc, hR⟩ :=
    kasami_autocorr_eq_monomial_addCharSum hcard hk hkn hcop hnodd a ha s hs
  have hgcd_dvd : Nat.gcd e (Fintype.card F - 1) ∣ Fintype.card F - 1 := Nat.gcd_dvd_right _ _
  have hgcd_pos : 0 < Nat.gcd e (Fintype.card F - 1) := Nat.gcd_pos_of_pos_left _ he
  obtain ⟨χ₁, hχ₁⟩ :=
    MulChar.exists_mulChar_orderOf F hgcd_dvd
      (Complex.isPrimitiveRoot_exp _ hgcd_pos.ne')
  refine ⟨Units.mk0 c hc, e, χ₁, he, hχ₁, ?_⟩
  rw [hR]
  have hord : orderOf χ₁ = Nat.gcd e (Fintype.card F - 1) := hχ₁
  have := monomial_addCharSum_eq_gaussSum_sum (chiC : AddChar F ℂ) chiC_primitive
    (Units.mk0 c hc) e he χ₁ hord
  simpa using this

/-!
**⚠ FALSE as stated (single-Gauss-sum collapse).**  The leaf below
(`kasami_autocorr_eq_pm_single_gaussSum`) claims `(R_a(s) : ℂ) = ± g(χ₂, χ)` for a
*single* Teichmüller Gauss sum.  This is false: `R_a(s)` is a rational integer that
takes values such as `8` and `±32` over `GF(2⁵)` (see
`KasamiMonomialCollapseDisproof.lean`), whereas any *nonzero* Gauss sum for a
nontrivial multiplicative character over `GF(2⁵)` has modulus `√32` (so it is not a
rational integer), the trivial character gives `g = -1`, and no Gauss sum is `0`
for a primitive `ψ`.  Hence `±` one Gauss sum can never equal these integer
values.  The correct, already-*green* statement is `kasami_autocorr_eq_gaussSum_sum`
above: `R` is a *sum of several* Gauss sums.  This `sorry` is unprovable and is
retained only to document the corrected architecture.
-/

/-- **The single-coset collapse (L1 module 5 leaf).**  The character-power
Gauss-sum expansion of the Kasami cross-correlation collapses to `±` a *single*
Teichmüller Gauss sum: there is a multiplicative character `χ₂` with
`(R_a(s) : ℂ) = ± g(χ₂, chiC)`.  Classically (Stickelberger / `2`-cyclotomic
cosets, Lidl–Niederreiter Ch. 5; Gross–Koblitz 1979) only the characters in one
coset of the Kasami exponent survive, and being conjugate they combine to a single
Gauss sum (rational-integer-valued, as `chiC` is `±1`-valued).  This Gauss sum is
the object whose `2`-adic valuation leaf L3 computes. -/
theorem kasami_autocorr_eq_pm_single_gaussSum {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F) (hs : s ≠ 0) :
    ∃ χ₂ : MulChar F ℂ,
      (autocorrScaled (fun x : F => x ^ d k) s a : ℂ) = gaussSum χ₂ (chiC : AddChar F ℂ)
        ∨ (autocorrScaled (fun x : F => x ^ d k) s a : ℂ) = - gaussSum χ₂ (chiC : AddChar F ℂ) := by
  sorry

end Vanish.Foundations.FirstPrinciples.Transcribe
