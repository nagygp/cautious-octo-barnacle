import Mathlib
import RequestProject.Foundations.ChiBridge
import RequestProject.Foundations.FirstPrinciples.Transcribe.MonomialGaussExpansion
import RequestProject.MTuple.Count
import RequestProject.APN.Defs

/-!
# Transcription — Leaf L1, module 4: the Kasami Frobenius/trace → monomial substitution

This module is the **fourth rung** of the additive→multiplicative character-sum
bridge `GaussSumDecomp.kasami_crossCorr_eq_gaussInt` (leaf **L1** in
`FirstPrinciplesTranscriptionRoadmap.md`).  Module 3
(`MonomialGaussExpansion`) proved the *analytic heart* — a monomial additive
character sum `∑_x ψ(c·xᵐ)` expands into multiplicative-character Gauss sums.  This
module connects that machinery to the **Kasami cross-correlation** itself.

It supplies, as **real proofs**, the elementary wiring that turns the project's
`ℤ`-valued sign character `WalshAB.χ = (-1)^{Tr}` into a genuine `ℂ`-valued
additive character `chiC` (so that Mathlib's `gaussSum` API applies), and recasts
the integer cross-correlation `autocorrScaled f s a` as the complex additive
character sum `∑_x chiC (s · Δf_a x)`:

* `chiC` — the `ℂ`-valued sign character `x ↦ (χ x : ℂ)` (a genuine `AddChar F ℂ`);
* `chiC_ne_one`, `chiC_primitive` — nontriviality and primitivity (a nontrivial
  additive character of a field is primitive);
* `autocorrScaled_cast_eq_chiC_sum` — `(R_a(s) : ℂ) = ∑_x chiC (s · Δf_a x)`.

It then states, as the single classical **leaf**, the genuinely Kasami-specific
content: the second-order trace expansion of `R(s)` for the Kasami power map
`x ↦ x^{d k}` collapses, via the Frobenius/quadratic structure of
`d k = 2^{2k} − 2^k + 1`, to a **single monomial** additive character sum
`∑_x chiC (c · x^{e})` (Lidl–Niederreiter Ch. 5; Kasami's original substitution).
Feeding this monomial form into module 3 is roadmap module 5 (`GaussSumBridge`).

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 5 (character sums; Frobenius).
* T. Kasami, *The weight enumerators for several classes of subcodes of the
  second order binary Reed–Muller codes*, Information and Control 18 (1971).
* Project: `WalshAB.χ`, `MTuple.deriv`, `autocorrScaled`, `ChiBridge.chiAddChar`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open MulChar AddChar WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The `ℂ`-valued sign character.**  The project's `ℤ`-valued
`WalshAB.χ x = (-1)^{Tr x}` composed with `ℤ ↪ ℂ` is a genuine additive character
`AddChar F ℂ`, so Mathlib's `gaussSum`/`jacobiSum` API (which needs a target field)
applies. -/
noncomputable def chiC : AddChar F ℂ where
  toFun x := (χ x : ℂ)
  map_zero_eq_one' := by simp [χ_zero]
  map_add_eq_mul' := by intro x y; rw [χ_mul]; push_cast; ring

@[simp] theorem chiC_apply (x : F) : (chiC : AddChar F ℂ) x = (χ x : ℂ) := rfl

/-- `chiC` is nontrivial: the trace is surjective, so some `x` has `Tr x ≠ 0`,
hence `chiC x = (-1 : ℂ) ≠ 1`. -/
theorem chiC_ne_one : (chiC : AddChar F ℂ) ≠ 1 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have hval : (chiC : AddChar F ℂ) y = (1 : AddChar F ℂ) y := by rw [h]
  rw [chiC_apply, AddChar.one_apply] at hval
  simp only [χ, hy] at hval
  norm_num at hval

/-- A nontrivial additive character of a field is primitive. -/
theorem chiC_primitive : (chiC : AddChar F ℂ).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one chiC_ne_one

/-- **The cross-correlation as a complex additive character sum.**  Casting the
integer `autocorrScaled f s a` to `ℂ` gives the `chiC`-sum over the second
derivative `Δf_a x = f(x+a)+f(x)`:  `(R_a(s) : ℂ) = ∑_x chiC (s · Δf_a x)`. -/
theorem autocorrScaled_cast_eq_chiC_sum (f : F → F) (s a : F) :
    (autocorrScaled f s a : ℂ) = ∑ x : F, (chiC : AddChar F ℂ) (s * deriv f a x) := by
  rw [autocorrScaled_eq]
  push_cast
  simp [chiC_apply]

/-- **Shift reduction of the Kasami cross-correlation (to the `a = 1` case).**  The
linear substitution `x = a·y` (a bijection since `a ≠ 0`) absorbs the shift and
rescales the coefficient by `a^{d k}`:
`(R_a(s) : ℂ) = ∑_y chiC (s·a^{d k}·((y+1)^{d k} + y^{d k}))`.  This is the clean,
Mathlib-rooted first half of the Kasami trace → monomial collapse: it reduces the
general leaf to the shift-free case `a = 1`, leaving only the genuinely
Kasami-specific monomial collapse (`kasami_autocorr_eq_monomial_addCharSum`).  Real
proof (reindexing by `Equiv.mulLeft₀`). -/
theorem autocorrScaled_chiC_reduce_shift (k : ℕ) (a : F) (ha : a ≠ 0) (s : F) :
    (autocorrScaled (fun x : F => x ^ d k) s a : ℂ)
      = ∑ y : F, (chiC : AddChar F ℂ) (s * a ^ (d k) * ((y + 1) ^ (d k) + y ^ (d k))) := by
  rw [autocorrScaled_cast_eq_chiC_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ a ha)
        (fun x : F => (chiC : AddChar F ℂ) (s * MTuple.deriv (fun x : F => x ^ d k) a x))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  simp only [Equiv.mulLeft₀_apply, MTuple.deriv]
  rw [show a * y + a = a * (y + 1) by ring, mul_pow, mul_pow]
  ring

/-!
**⚠ DISPROVED (see `KasamiMonomialCollapseDisproof.lean`).**  The two leaves below
(`kasami_monomial_collapse_one` and `kasami_autocorr_eq_monomial_addCharSum`) are
**false as stated**: the Kasami second-derivative sign-character sum does *not*
collapse to a single monomial character sum.  For genuine Kasami parameters
`n = 5`, `k = 2` (`d k = 13`) and `c₀ = 1` the sum equals `8`, while every single
monomial sign-character sum over `GF(2⁵)` lies in `{0, −30, 32}` (the units form a
group of prime order `31`).  See `MonomialCollapseDisproof.monomial_collapse_fails`
for the `native_decide`-verified counterexample.  The correct, already-*green* form
of this rung is `GaussSumBridge.kasami_autocorr_eq_gaussSum_sum` (a sum of *several*
Gauss sums).  These `sorry`s are therefore unprovable and are retained only to
document the corrected architecture; nothing sound depends on them.
-/

/-- **Shift-free Kasami monomial collapse (the remaining deep sub-leaf).**  With the
shift absorbed by `autocorrScaled_chiC_reduce_shift`, the genuinely Kasami-specific
content is the collapse of the shift-free second-derivative character sum
`∑_y chiC (c₀·((y+1)^{d k} + y^{d k}))` to a **single monomial** character sum
`∑_x chiC (c·x^{e})`.  This is Kasami's substitution (Kasami 1971; Lidl–Niederreiter
Ch. 5), the sole remaining classical input of Module 4 — now stated over the
shift-free case `a = 1`, strictly closer to Mathlib than the general leaf. -/
theorem kasami_monomial_collapse_one {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (c₀ : F) (hc₀ : c₀ ≠ 0) :
    ∃ (c : F) (e : ℕ), 1 ≤ e ∧ c ≠ 0 ∧
      (∑ y : F, (chiC : AddChar F ℂ) (c₀ * ((y + 1) ^ (d k) + y ^ (d k)))
        = ∑ x : F, (chiC : AddChar F ℂ) ((c : F) * x ^ e)) := by
  sorry

/-- **The Kasami trace → monomial substitution (L1 module 4 leaf).**  For a
non-degenerate Kasami frequency `s ≠ 0`, the second-order trace expansion of the
cross-correlation `R(s) = ∑_x χ(s·((x+a)^{d k}+x^{d k}))` collapses — via the
Frobenius/quadratic structure of the Kasami exponent `d k = 2^{2k} − 2^k + 1` —
to a **single monomial** additive character sum `∑_x chiC (c · x^{e})` with `c ≠ 0`
and `e ≥ 1`.  This is the genuinely Kasami-specific classical input (Kasami 1971;
Lidl–Niederreiter Ch. 5); the elementary wiring around it
(`autocorrScaled_cast_eq_chiC_sum`) is proved above, and feeding the monomial form
into `monomial_addCharSum_eq_gaussSum_sum` is roadmap module `GaussSumBridge`. -/
theorem kasami_autocorr_eq_monomial_addCharSum {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (a : F) (ha : a ≠ 0) (s : F) (hs : s ≠ 0) :
    ∃ (c : F) (e : ℕ), 1 ≤ e ∧ c ≠ 0 ∧
      (autocorrScaled (fun x : F => x ^ d k) s a : ℂ)
        = ∑ x : F, (chiC : AddChar F ℂ) ((c : F) * x ^ e) := by
  obtain ⟨c, e, he, hc, hcol⟩ :=
    kasami_monomial_collapse_one hcard hk hkn hcop hnodd (s * a ^ (d k))
      (mul_ne_zero hs (pow_ne_zero _ ha))
  exact ⟨c, e, he, hc, by rw [autocorrScaled_chiC_reduce_shift k a ha s, hcol]⟩

end Vanish.Foundations.FirstPrinciples.Transcribe
