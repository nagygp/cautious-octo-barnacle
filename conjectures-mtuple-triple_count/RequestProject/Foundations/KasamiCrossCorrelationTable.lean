import RequestProject.Foundations.KasamiCrossCorrelationGeneralK
import RequestProject.Foundations.ValueDistribution

/-!
# Foundations, Layer 10 — the closed-form value/multiplicity table

This module continues **Layer 9** (`KasamiCrossCorrelationGeneralK.lean`) towards
**Layer 10** of the "Kasami is Vanish" roadmap (`Docs/VanishFutureDirections.md`):
the *closed-form three- or five-valued value/multiplicity table* of the
cross-correlation `R(s) = autocorrScaled f s a = ∑_x χ(s·Δf_a x)`.  As flagged in
Layers 6–7, this is the **MacWilliams/Pless power-moment continuation**: it needs
the higher power moments (in particular the fourth) and weight divisibility.

## The general power moment (the Pless engine)

Layer 9 supplied the first and second moments by hand.  Here the entire family is
unified in a single line, since the `c ≡ 1` case of `MTuple.card_mul_preCount`
*is* the `m`-th power moment:

* `crossCorr_power_moment` — `∑_s R(s)^m = q · #{ x : Fin m → F | ∑ᵢ Δf_a(xᵢ) = 0 }`
  (the `m`-th power moment as a derivative-collision count);
* `crossCorr_fourth_moment` — the `m = 4` specialization (the named missing
  ingredient), and `crossCorr_third_moment` (`m = 3`).

These are exactly the Pless power moments that the value/multiplicity table
consumes.

## Reading multiplicities off the moments (MacWilliams/Pless)

Given the *value set* of a finite integer-valued function, its power moments
determine the multiplicities by a Vandermonde solve:

* `threeValued_moment_eqs` — for a `{0, A, -A}`-valued `g`, the first two moments
  give the signed/total support counts `#{g=A} ± #{g=-A}`;
* `fiveValued_moment_eqs` — for a `{0, ±A, ±B}`-valued `g` (the five distinct
  values), the first four moments give `#{g=A} ± #{g=-A}` and `#{g=B} ± #{g=-B}`.

Both are crypto-free, function-agnostic algebra (reusing the sign-distribution
pearls of `ValueDistribution.lean`).

## The closed-form tables

* **`k = 1` (cube/Gold), unconditional.**  Layer 7 pinned the cube
  cross-correlation support to `{0, a^{-3}}` with `R(0) = q`.  Combined with the
  first moment this gives the *complete* three-valued table:
  `cube_crossCorr_three_valued` (`R(s) ∈ {0, q, -q}`) and `cube_crossCorr_table`
  (`#{R = q} = 1`, `#{R = -q} = 1`, `#{R = 0} = q - 2`).

* **General `k`, conditional on the value set.**  Feeding the power moments to the
  Pless solve, *once the value set `{0, ±A, ±B}` is known* (the deep Kasami-1971 /
  Canteaut–Charpin–Dobbertin input — weight divisibility of the Kasami code), the
  multiplicities are determined: `crossCorr_threeValued_table`,
  `crossCorr_fiveValued_table`, and their Kasami specializations.  This isolates
  the remaining deep input exactly to the *value set itself*.

## Sources

Kasami (1971); Canteaut–Charpin–Dobbertin (SIAM 2000); MacWilliams–Sloane (the
Pless power moments); Chabaud–Vaudenay §3.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The general power moment (the Pless engine) -/

/-
**The `m`-th power moment of the cross-correlation.**  For any `f` and `a`,
`∑_s R(s)^m = q · #{ x : Fin m → F | ∑ᵢ Δf_a(xᵢ) = 0 }`.  This is the `c ≡ 1`
case of Fourier inversion (`MTuple.card_mul_preCount`): the `m`-fold product
`∏ᵢ R(t·1)` collapses to `R(t)^m`.
-/
theorem crossCorr_power_moment (m : ℕ) (f : F → F) (a : F) :
    ∑ s : F, (autocorrScaled f s a) ^ m
      = (Fintype.card F : ℤ) * (MTuple.preCount m f a (fun _ => 1) : ℤ) := by
  -- By definition of `preCount`, we can rewrite the right-hand side of the equation.
  rw [MTuple.card_mul_preCount];
  simp +decide [ Finset.prod_const, Finset.card_univ ]

/-- **Fourth moment of the cross-correlation.**  `∑_s R(s)^4 = q · #{ x : Fin 4 → F
| ∑ᵢ Δf_a(xᵢ) = 0 }`.  The MacWilliams/Pless ingredient flagged in Layers 6–7. -/
theorem crossCorr_fourth_moment (f : F → F) (a : F) :
    ∑ s : F, (autocorrScaled f s a) ^ 4
      = (Fintype.card F : ℤ) * (MTuple.preCount 4 f a (fun _ => 1) : ℤ) :=
  crossCorr_power_moment 4 f a

/-- **Third moment of the cross-correlation.**  `∑_s R(s)^3 = q · #{ x : Fin 3 → F
| ∑ᵢ Δf_a(xᵢ) = 0 }`. -/
theorem crossCorr_third_moment (f : F → F) (a : F) :
    ∑ s : F, (autocorrScaled f s a) ^ 3
      = (Fintype.card F : ℤ) * (MTuple.preCount 3 f a (fun _ => 1) : ℤ) :=
  crossCorr_power_moment 3 f a

/-! ### Kasami specializations of the power moment -/

variable {n k : ℕ}

/-- **Kasami cross-correlation: `m`-th power moment.** -/
theorem kasami_crossCorr_power_moment (m : ℕ) (a : F) :
    ∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ m
      = (Fintype.card F : ℤ)
        * (MTuple.preCount m (fun x : F => x ^ d k) a (fun _ => 1) : ℤ) :=
  crossCorr_power_moment m _ a

/-- **Kasami cross-correlation: fourth moment.** -/
theorem kasami_crossCorr_fourth_moment (a : F) :
    ∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
      = (Fintype.card F : ℤ)
        * (MTuple.preCount 4 (fun x : F => x ^ d k) a (fun _ => 1) : ℤ) :=
  crossCorr_power_moment 4 _ a

/-! ## Reading multiplicities off the moments (MacWilliams/Pless) -/

/-
**Three-valued Pless solve.**  For a `{0, A, -A}`-valued integer function `g`
with `A ≠ 0`, the first two power moments give the signed and total support
counts:
`A·(#{g=A} − #{g=-A}) = ∑ g` and `A²·(#{g=A} + #{g=-A}) = ∑ g²`.
-/
theorem threeValued_moment_eqs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) (A : ℤ) (hA : A ≠ 0)
    (hg : ∀ i, g i = 0 ∨ g i = A ∨ g i = -A) :
    A * (((univ.filter (fun i => g i = A)).card : ℤ)
          - ((univ.filter (fun i => g i = -A)).card : ℤ)) = ∑ i, g i
    ∧ A ^ 2 * (((univ.filter (fun i => g i = A)).card : ℤ)
          + ((univ.filter (fun i => g i = -A)).card : ℤ)) = ∑ i, g i ^ 2 := by
  constructor;
  · -- By definition of $g$, we can split the sum into three parts: the sum over indices where $g(i) = 0$, the sum over indices where $g(i) = A$, and the sum over indices where $g(i) = -A$.
    have h_split : ∑ i, g i = ∑ i ∈ Finset.univ.filter (fun i => g i = A), A + ∑ i ∈ Finset.univ.filter (fun i => g i = -A), -A := by
      rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rcases hg i with ( h | h | h ) <;> simp +decide [ h ] ;
      · grind;
      · grind;
      · grind
    generalize_proofs at *; (
    simp_all +decide [ mul_sub ] ; ring;);
  · rw [ Finset.card_filter, Finset.card_filter ];
    push_cast [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
    rw [ ← Finset.sum_add_distrib, Finset.mul_sum ];
    grind

/-
**Five-valued Pless solve.**  For a `{0, ±A, ±B}`-valued integer function `g`
with the five values distinct (`A ≠ 0`, `B ≠ 0`, `A ≠ B`, `A ≠ -B`), the first
four power moments give the signed and total support counts of the two value
pairs.
-/
theorem fiveValued_moment_eqs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (hg : ∀ i, g i = 0 ∨ g i = A ∨ g i = -A ∨ g i = B ∨ g i = -B) :
    let pA : ℤ := (univ.filter (fun i => g i = A)).card
    let mA : ℤ := (univ.filter (fun i => g i = -A)).card
    let pB : ℤ := (univ.filter (fun i => g i = B)).card
    let mB : ℤ := (univ.filter (fun i => g i = -B)).card
    (∑ i, g i = A * (pA - mA) + B * (pB - mB))
    ∧ (∑ i, g i ^ 2 = A ^ 2 * (pA + mA) + B ^ 2 * (pB + mB))
    ∧ (∑ i, g i ^ 3 = A ^ 3 * (pA - mA) + B ^ 3 * (pB - mB))
    ∧ (∑ i, g i ^ 4 = A ^ 4 * (pA + mA) + B ^ 4 * (pB + mB)) := by
  refine' ⟨ _, _, _, _ ⟩;
  · push_cast [ Finset.card_filter ];
    rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum ];
    rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rcases hg i with ( h | h | h | h | h ) <;> simp +decide [ h ] ; ring;
    · aesop;
    · grind;
    · lia;
    · grind;
    · grind;
  · rw [ Finset.sum_congr rfl fun i _ => show g i ^ 2 = if g i = A then A ^ 2 else if g i = -A then A ^ 2 else if g i = B then B ^ 2 else if g i = -B then B ^ 2 else 0 from ?_ ];
    · push_cast [ Finset.sum_ite ];
      simp +decide [ Finset.filter_filter, mul_add, add_assoc, add_left_comm, add_comm ];
      rw [ show ( Finset.filter ( fun x => ¬g x = A ∧ g x = -A ) Finset.univ ) = Finset.filter ( fun x => g x = -A ) Finset.univ from ?_, show ( Finset.filter ( fun x => ( ¬g x = A ∧ ¬g x = -A ) ∧ g x = B ) Finset.univ ) = Finset.filter ( fun x => g x = B ) Finset.univ from ?_, show ( Finset.filter ( fun x => ( ( ¬g x = A ∧ ¬g x = -A ) ∧ ¬g x = B ) ∧ g x = -B ) Finset.univ ) = Finset.filter ( fun x => g x = -B ) Finset.univ from ?_ ] ; ring; all_goals grind;
    · grind;
  · push_cast [ Finset.card_filter ];
    rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum ];
    rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rcases hg i with ( h | h | h | h | h ) <;> simp +decide [ h ] ; ring;
    · aesop;
    · grind;
    · lia;
    · grind;
    · grind;
  · rw [ Finset.sum_congr rfl fun i _ => show g i ^ 4 = if g i = A then A ^ 4 else if g i = -A then A ^ 4 else if g i = B then B ^ 4 else if g i = -B then B ^ 4 else 0 from ?_ ];
    · simp +decide [ Finset.sum_ite, mul_add, add_assoc ];
      simp +decide [ Finset.filter_filter, mul_comm ];
      congr <;> ext i <;> by_cases hi : g i = A <;> by_cases hi' : g i = -A <;> by_cases hi'' : g i = B <;> simp +decide [ hi, hi', hi'' ];
      all_goals omega;
    · grind

/-! ## The closed-form table at `k = 1` (cube/Gold) — unconditional -/

/-
**The cube cross-correlation is three-valued.**  For `n` odd and `a ≠ 0`,
`R(s) = ∑_x χ(s·Δ(x³)_a x) ∈ {0, q, -q}`.  (The support is `{0, a^{-3}}`
(`cube_autocorr_eq_zero`) with `R(0) = q` (`cube_autocorr_zero`); the first moment
`∑_s R(s) = 0` forces `R(a^{-3}) = -q`.)
-/
theorem cube_crossCorr_three_valued (hodd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (s : F) :
    autocorrScaled (fun x : F => x ^ 3) s a = 0
    ∨ autocorrScaled (fun x : F => x ^ 3) s a = (Fintype.card F : ℤ)
    ∨ autocorrScaled (fun x : F => x ^ 3) s a = -(Fintype.card F : ℤ) := by
  by_cases hs : s = 0 <;> by_cases hs' : s * a ^ 3 = 1 <;> simp_all +decide [ cube_autocorr_zero, cube_autocorr_eq_zero ];
  have h_sum : ∑ s ∈ Finset.univ \ {0, 1 / a ^ 3}, autocorrScaled (fun x => x ^ 3) s a = 0 := by
    refine' Finset.sum_eq_zero fun x hx => _;
    apply Vanish.Foundations.cube_autocorr_eq_zero a ha x; simp_all +decide [ div_eq_mul_inv ] ;
    grind;
  have h_sum : ∑ s ∈ ({0, 1 / a ^ 3} : Finset F), autocorrScaled (fun x => x ^ 3) s a = 0 := by
    convert crossCorr_first_moment ( fun x : F => x ^ 3 ) _ a ha using 1;
    · rw [ ← Finset.sum_sdiff ( Finset.subset_univ { 0, 1 / a ^ 3 } ) ] ; aesop;
    · convert KasamiAB.kasami_bijective hcard 1 ( by decide ) ( by simp +decide ) hodd ( Odd.pos hodd ) using 1;
  grind +suggestions

/-
**The closed-form cube cross-correlation table.**  For `n` odd and `a ≠ 0`,
`R` takes the value `q` exactly once (at `s = 0`), the value `-q` exactly once
(at `s = a^{-3}`), and `0` on the remaining `q - 2` frequencies.
-/
theorem cube_crossCorr_table (hodd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) :
    (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ 3) s a = (Fintype.card F : ℤ))).card = 1
    ∧ (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ 3) s a = -(Fintype.card F : ℤ))).card = 1
    ∧ (univ.filter (fun s : F =>
        autocorrScaled (fun x : F => x ^ 3) s a = 0)).card = Fintype.card F - 2 := by
  obtain ⟨ k, hk ⟩ := hodd;
  have h_unique : ∀ s : F, s ≠ 0 → s * a ^ 3 ≠ 1 → autocorrScaled (fun x => x ^ 3) s a = 0 := by
    grind +suggestions;
  have h_unique : autocorrScaled (fun x => x ^ 3) (a ^ (-3 : ℤ)) a = -↑(Fintype.card F) := by
    have h_unique : ∑ s ∈ Finset.univ.erase 0, autocorrScaled (fun x => x ^ 3) s a = -↑(Fintype.card F) := by
      convert Vanish.Foundations.crossCorr_first_moment_nonzero ( fun x => x ^ 3 ) _ a ha using 1;
      have h_bijective : ∀ x : F, x ≠ 0 → x ^ 3 = 1 → x = 1 := by
        intro x hx hx3
        have h_order : x ^ (Fintype.card F - 1) = 1 := by
          exact FiniteField.pow_card_sub_one_eq_one x hx;
        have h_order : x ^ (Nat.gcd 3 (Fintype.card F - 1)) = 1 := by
          rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
        have h_gcd : Nat.gcd 3 (2 ^ n - 1) = 1 := by
          rw [ ← Nat.mod_add_div ( 2 ^ n ) 3 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hk ] ;
        aesop;
      have h_bijective : ∀ x : F, x ≠ 0 → ∀ y : F, y ≠ 0 → x ^ 3 = y ^ 3 → x = y := by
        intros x hx y hy hxy
        have h_eq : (x / y) ^ 3 = 1 := by
          rw [ div_pow, hxy, div_self ( pow_ne_zero 3 hy ) ];
        exact eq_of_div_eq_one ( h_bijective _ ( div_ne_zero hx hy ) h_eq );
      have h_bijective : Function.Injective (fun x : F => x ^ 3) := by
        intro x y hxy;
        by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp +decide [ hx, hy ] at hxy ⊢;
        · exact absurd hxy.symm ( pow_ne_zero 3 hy );
        · exact h_bijective x hx y hy hxy;
      exact ⟨ h_bijective, Finite.injective_iff_surjective.mp h_bijective ⟩;
    rw [ ← h_unique, Finset.sum_eq_single ( a ^ ( -3 : ℤ ) ) ] <;> simp_all +decide [ zpow_neg, zpow_ofNat ];
    grind;
  have h_unique : ∀ s : F, s ≠ 0 → s ≠ a ^ (-3 : ℤ) → autocorrScaled (fun x => x ^ 3) s a = 0 := by
    intro s hs hs'; specialize ‹∀ s : F, s ≠ 0 → s * a ^ 3 ≠ 1 → autocorrScaled ( fun x => x ^ 3 ) s a = 0› s hs; simp_all +decide [ zpow_neg, zpow_ofNat ] ;
    exact h_unique ( by intro h; exact hs' ( eq_inv_of_mul_eq_one_left h ) );
  have h_unique : Finset.filter (fun s => autocorrScaled (fun x => x ^ 3) s a = ↑(Fintype.card F)) Finset.univ = {0} ∧ Finset.filter (fun s => autocorrScaled (fun x => x ^ 3) s a = -↑(Fintype.card F)) Finset.univ = {a ^ (-3 : ℤ)} := by
    constructor <;> ext s <;> by_cases hs : s = 0 <;> by_cases hs' : s = a ^ ( -3 : ℤ ) <;> simp_all +decide;
    · grind +suggestions;
    · convert cube_autocorr_zero a using 1;
      exact_mod_cast hcard.symm;
    · norm_num [ neg_eq_iff_add_eq_zero ];
    · positivity;
    · rw [ Vanish.Foundations.cube_autocorr_zero ];
      linarith [ pow_pos ( zero_lt_two' ℤ ) ( 2 * k + 1 ) ];
  have h_unique : Finset.filter (fun s => autocorrScaled (fun x => x ^ 3) s a = 0) Finset.univ = Finset.univ \ ({0} ∪ {a ^ (-3 : ℤ)}) := by
    grind;
  grind

/-! ## The conditional table for general `k` (value set supplied) -/

/-
**Three-valued cross-correlation table from the moments.**  If the
cross-correlation of a bijective APN `f` is `{0, A, -A}`-valued (`A ≠ 0`), then
its support counts are pinned down by the first two moments: `#{R=A} = #{R=-A}`
and `A²·(#{R=A} + #{R=-A}) = 2·q²`.
-/
theorem crossCorr_threeValued_table (f : F → F) (hbij : Function.Bijective f)
    (hapn : IsAPN f) (a : F) (ha : a ≠ 0) (A : ℤ) (hA : A ≠ 0)
    (hval : ∀ s : F, autocorrScaled f s a = 0
      ∨ autocorrScaled f s a = A ∨ autocorrScaled f s a = -A) :
    A * (((univ.filter (fun s : F => autocorrScaled f s a = A)).card : ℤ)
          - ((univ.filter (fun s : F => autocorrScaled f s a = -A)).card : ℤ)) = 0
    ∧ A ^ 2 * (((univ.filter (fun s : F => autocorrScaled f s a = A)).card : ℤ)
          + ((univ.filter (fun s : F => autocorrScaled f s a = -A)).card : ℤ))
        = 2 * (Fintype.card F : ℤ) ^ 2 := by
  convert Vanish.Foundations.threeValued_moment_eqs ( fun s => autocorrScaled f s a ) A hA hval using 1;
  · rw [ Vanish.Foundations.crossCorr_first_moment f hbij a ha ];
  · rw [ Vanish.Foundations.crossCorr_second_moment f hapn a ha ]

/-
**Five-valued cross-correlation table from the moments.**  If the
cross-correlation of a bijective APN `f` is `{0, ±A, ±B}`-valued (five distinct
values), then the support counts of the two value pairs are pinned down by the
first four moments: the signed counts by `M₁ = 0`, `M₃ = q·N₃`, and the total
counts by `M₂ = 2q²`, `M₄ = q·N₄` (with `Nₘ = #{x : Fin m → F | ∑ᵢ Δf_a(xᵢ) = 0}`).
-/
theorem crossCorr_fiveValued_table (f : F → F) (hbij : Function.Bijective f)
    (hapn : IsAPN f) (a : F) (ha : a ≠ 0) (A B : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (hval : ∀ s : F, autocorrScaled f s a = 0
      ∨ autocorrScaled f s a = A ∨ autocorrScaled f s a = -A
      ∨ autocorrScaled f s a = B ∨ autocorrScaled f s a = -B) :
    let pA : ℤ := (univ.filter (fun s : F => autocorrScaled f s a = A)).card
    let mA : ℤ := (univ.filter (fun s : F => autocorrScaled f s a = -A)).card
    let pB : ℤ := (univ.filter (fun s : F => autocorrScaled f s a = B)).card
    let mB : ℤ := (univ.filter (fun s : F => autocorrScaled f s a = -B)).card
    (0 = A * (pA - mA) + B * (pB - mB))
    ∧ (2 * (Fintype.card F : ℤ) ^ 2 = A ^ 2 * (pA + mA) + B ^ 2 * (pB + mB))
    ∧ ((Fintype.card F : ℤ) * (MTuple.preCount 3 f a (fun _ => 1) : ℤ)
        = A ^ 3 * (pA - mA) + B ^ 3 * (pB - mB))
    ∧ ((Fintype.card F : ℤ) * (MTuple.preCount 4 f a (fun _ => 1) : ℤ)
        = A ^ 4 * (pA + mA) + B ^ 4 * (pB + mB)) := by
  have := @Vanish.Foundations.fiveValued_moment_eqs;
  convert this ( fun s => autocorrScaled f s a ) A B hA hB hAB hAnB hval using 1;
  rw [ Vanish.Foundations.crossCorr_first_moment f hbij a ha, Vanish.Foundations.crossCorr_second_moment f hapn a ha, Vanish.Foundations.crossCorr_power_moment 3 f a, Vanish.Foundations.crossCorr_power_moment 4 f a ]

/-! ### Kasami specializations of the conditional tables -/

/-- **Kasami three-valued cross-correlation table from the moments.**  If the
general-`k` Kasami cross-correlation is `{0, A, -A}`-valued, its support counts are
pinned down by the first two moments. -/
theorem kasami_crossCorr_threeValued_table (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (A : ℤ) (hA : A ≠ 0)
    (hval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a = 0
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = A
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = -A) :
    A * (((univ.filter (fun s : F =>
            autocorrScaled (fun x : F => x ^ d k) s a = A)).card : ℤ)
          - ((univ.filter (fun s : F =>
            autocorrScaled (fun x : F => x ^ d k) s a = -A)).card : ℤ)) = 0
    ∧ A ^ 2 * (((univ.filter (fun s : F =>
            autocorrScaled (fun x : F => x ^ d k) s a = A)).card : ℤ)
          + ((univ.filter (fun s : F =>
            autocorrScaled (fun x : F => x ^ d k) s a = -A)).card : ℤ))
        = 2 * (Fintype.card F : ℤ) ^ 2 :=
  crossCorr_threeValued_table _
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha A hA hval

/-- **Kasami five-valued cross-correlation table from the moments.**  If the
general-`k` Kasami cross-correlation is `{0, ±A, ±B}`-valued (five distinct
values), the support counts of the two value pairs are pinned down by the first
four moments.  The remaining deep input is the value set `{±A, ±B}` itself
(Kasami-1971 / Canteaut–Charpin–Dobbertin weight divisibility). -/
theorem kasami_crossCorr_fiveValued_table (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)
    (a : F) (ha : a ≠ 0) (A B : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) (hAnB : A ≠ -B)
    (hval : ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a = 0
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = A
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = -A
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = B
      ∨ autocorrScaled (fun x : F => x ^ d k) s a = -B) :
    let pA : ℤ := (univ.filter (fun s : F =>
      autocorrScaled (fun x : F => x ^ d k) s a = A)).card
    let mA : ℤ := (univ.filter (fun s : F =>
      autocorrScaled (fun x : F => x ^ d k) s a = -A)).card
    let pB : ℤ := (univ.filter (fun s : F =>
      autocorrScaled (fun x : F => x ^ d k) s a = B)).card
    let mB : ℤ := (univ.filter (fun s : F =>
      autocorrScaled (fun x : F => x ^ d k) s a = -B)).card
    (0 = A * (pA - mA) + B * (pB - mB))
    ∧ (2 * (Fintype.card F : ℤ) ^ 2 = A ^ 2 * (pA + mA) + B ^ 2 * (pB + mB))
    ∧ ((Fintype.card F : ℤ)
          * (MTuple.preCount 3 (fun x : F => x ^ d k) a (fun _ => 1) : ℤ)
        = A ^ 3 * (pA - mA) + B ^ 3 * (pB - mB))
    ∧ ((Fintype.card F : ℤ)
          * (MTuple.preCount 4 (fun x : F => x ^ d k) a (fun _ => 1) : ℤ)
        = A ^ 4 * (pA + mA) + B ^ 4 * (pB + mB)) :=
  crossCorr_fiveValued_table _
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn)
    a ha A B hA hB hAB hAnB hval

end Vanish.Foundations