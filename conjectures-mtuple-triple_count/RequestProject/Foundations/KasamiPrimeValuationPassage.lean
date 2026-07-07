import RequestProject.Foundations.KasamiGrossKoblitzDivisibility
import RequestProject.Foundations.KasamiLegendreValuation
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-7: the `𝔭`-to-`2`-adic valuation passage

This module is the **seventh from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
the rung explicitly marked **TODO** there, building on A-fp-6
(`KasamiGrossKoblitzValue.lean`) and the divisibility assembly
(`KasamiGrossKoblitzDivisibility.lean`).

The Gross–Koblitz / Stickelberger formula naturally computes the valuation of the
Gauss sum at the cyclotomic prime `𝔭` above `2`.  Input (A) is phrased with the
*rational* `2`-adic valuation `padicValInt 2` of the integer cross-correlation
value `R(s)`.  The passage between them is exactly the statement that `𝔭` is
**unramified** (`e = 1`, the residue content of A-fp-3
`KasamiCyclotomicPrime.lean`): the `𝔭`-adic valuation, restricted to rational
integers, *coincides* with the ordinary `2`-adic valuation.

This module proves that passage **from its defining divisibility property**, which
is the genuinely Mathlib-rooted foundational content:

* a valuation `vp : ℤ → ℕ` characterized by `2^m ∣ x ↔ m ≤ vp x` on non-zero
  integers (the `e = 1` divisibility) *equals* `padicValInt 2`
  (`valuation_eq_padicValInt_of_dvd_iff`), via `padicValNat_dvd_iff`; and

* chaining this passage with the Gross–Koblitz value in `𝔭`-form
  (`vp(R(s)) = s₂(e s)`) discharges `hGKval` in the exact `padicValInt` form
  consumed by `KasamiGrossKoblitzDivisibility.lean`
  (`grossKoblitz_hGKval_of_passage`).

## Results

* `padicValInt_two_eq_padicValNat_natAbs` — the bridge `padicValInt 2 x =
  v₂(|x|)`.
* `valuation_eq_padicValInt_of_dvd_iff` — the `e = 1` passage: a divisibility-
  characterized valuation equals `padicValInt 2`.
* `grossKoblitz_hGKval_of_passage` — `hGKval` from the `𝔭`-form value and the
  passage.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  The provable content is the
divisibility-uniqueness of `padicValInt 2` (`padicValNat_dvd_iff`).  The genuinely
deep inputs — the Gross–Koblitz value in `𝔭`-form, and that `𝔭` is unramified so
that its valuation satisfies the rational `2`-power divisibility characterization
— are carried as named hypotheses rather than axioms or `sorry`.

## Sources

Gross–Koblitz (Ann. Math. 1979); Washington, *Cyclotomic Fields*, Ch. 6
(decomposition / ramification, `e f g = [L:ℚ]`); Ireland–Rosen, Ch. 14.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **The integer-to-natural `2`-adic bridge.**  `padicValInt 2 x = v₂(|x|)`. -/
theorem padicValInt_two_eq_padicValNat_natAbs (x : ℤ) :
    padicValInt 2 x = padicValNat 2 x.natAbs := rfl

/-
**The `e = 1` valuation passage (uniqueness from divisibility).**  A valuation
`vp : ℤ → ℕ` whose value at a non-zero integer is characterized by `2`-power
divisibility, `2^m ∣ x ↔ m ≤ vp x`, *coincides* with the rational `2`-adic
valuation `padicValInt 2`.  This is the unramified-prime (`e = 1`) content: the
`𝔭`-adic valuation, restricted to `ℤ`, is the ordinary `2`-adic valuation.
-/
theorem valuation_eq_padicValInt_of_dvd_iff (vp : ℤ → ℕ)
    (hvp : ∀ (x : ℤ) (m : ℕ), x ≠ 0 → ((2 : ℤ) ^ m ∣ x ↔ m ≤ vp x)) :
    ∀ x : ℤ, x ≠ 0 → vp x = padicValInt 2 x := by
  intros x hx_nonzero
  apply Nat.le_antisymm;
  · contrapose! hvp;
    use x, padicValInt 2 x + 1;
    refine' ⟨ hx_nonzero, Or.inr ⟨ _, _ ⟩ ⟩ <;> norm_cast;
    convert Int.natCast_dvd.not.mpr ( Nat.pow_succ_factorization_not_dvd ( by positivity ) ( by simp +decide [ * ] : Nat.Prime 2 ) ) using 1;
  · contrapose! hvp;
    exact ⟨ x, vp x + 1, hx_nonzero, Or.inl ⟨ by exact dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt hvp ) ) ( by exact_mod_cast Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ ) ), Nat.lt_succ_self _ ⟩ ⟩

/-- **`hGKval` from the `𝔭`-form value and the passage.**  Given the Gross–Koblitz
value in `𝔭`-form `vp(R(s)) = s₂(e s)` (`hGKp`) and the `e = 1` passage
`vp = padicValInt 2` on non-zero integers (`hpass`), the `2`-adic valuation of each
non-zero cross-correlation value is the binary digit sum — exactly the `hGKval`
premise consumed by `kasami_crossCorr_hdiv_of_grossKoblitz`. -/
theorem grossKoblitz_hGKval_of_passage {k : ℕ} (a : F) (e : F → ℕ) (vp : ℤ → ℕ)
    (hpass : ∀ x : ℤ, x ≠ 0 → vp x = padicValInt 2 x)
    (hGKp : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
        vp (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s)) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a ≠ 0 →
      padicValInt 2 (autocorrScaled (fun x : F => x ^ d k) s a) = binDigitSum (e s) := by
  intro s hs
  rw [← hpass _ hs]
  exact hGKp s hs

end Vanish.Foundations