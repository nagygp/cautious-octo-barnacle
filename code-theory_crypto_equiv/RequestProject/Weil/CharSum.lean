import Mathlib

/-!
# One-variable additive character sums

This file sets up the basic object of the whole development: the *one-variable additive
character sum*
$$ S(\psi, f) \;=\; \sum_{x \in \mathbb F_q} \psi\bigl(f(x)\bigr), $$
where `F = 𝔽_q` is a finite field, `ψ : AddChar F ℂ` is an additive character with values in
`ℂ`, and `f ∈ F[X]` is a one-variable polynomial.

The **headline Weil bound** (proved in `RequestProject.Weil.WeilBound`) states that, for a
*nontrivial* `ψ` and a polynomial `f` whose degree `d` is prime to the characteristic,
$$ \bigl\| S(\psi, f) \bigr\| \;\le\; (d-1)\,\sqrt q. $$

This module records the elementary structural facts about `charSum` that the later modules
use freely.  These foundational lemmas are proved here; the deep obligations of the
development live in `RequestProject.Weil.Stepanov` and `RequestProject.Weil.WeilBound`.

## Main definitions
* `Weil.charSum ψ f` — the character sum `∑ x, ψ (f.eval x)`.

## Main statements (skeletons)
* `Weil.charSum_one` — for the trivial character the sum is `q`.
* `Weil.charSum_const` — the sum of a constant polynomial.
* `Weil.norm_charSum_le_card` — the trivial bound `‖S‖ ≤ q`.
* `Weil.charSum_linear_eq_zero` — a nontrivial character against a *linear* polynomial sums to `0`
  (this is the `d = 1` edge case of the Weil bound).
* `Weil.charSum_mulShift` — twisting the character by `mulShift c` equals scaling the polynomial by
  `c`; used to reduce the Weil bound to a single fixed nontrivial character.
-/

open scoped BigOperators
open Polynomial

namespace Weil

variable {F : Type*} [Field F] [Fintype F]

/-- The one-variable additive character sum `S(ψ, f) = ∑_{x ∈ F} ψ (f(x))`. -/
noncomputable def charSum (ψ : AddChar F ℂ) (f : F[X]) : ℂ :=
  ∑ x : F, ψ (f.eval x)

/-
For the trivial character `1`, the character sum is the cardinality of the field.
-/
lemma charSum_one (f : F[X]) :
    charSum (1 : AddChar F ℂ) f = (Fintype.card F : ℂ) := by
  simp +decide [ charSum ]

/-
The character sum of a constant polynomial `C c` is `q · ψ c`.
-/
lemma charSum_const (ψ : AddChar F ℂ) (c : F) :
    charSum ψ (Polynomial.C c) = (Fintype.card F : ℂ) * ψ c := by
  unfold charSum; simp +decide [ Finset.card_univ ] ;

/-
The trivial bound: each summand has norm `1`, so `‖S(ψ, f)‖ ≤ q`.
-/
lemma norm_charSum_le_card (ψ : AddChar F ℂ) (f : F[X]) :
    ‖charSum ψ f‖ ≤ (Fintype.card F : ℝ) := by
  convert norm_sum_le _ _;
  rw [ Finset.sum_congr rfl fun x _ => by rw [ AddChar.norm_apply ] ] ; norm_num

/-
A nontrivial character summed against a *linear* polynomial vanishes.  This is precisely the
`d = 1` case of the Weil bound, where the bound reads `‖S‖ ≤ 0`.
-/
lemma charSum_linear_eq_zero (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : F[X])
    (hf : f.natDegree = 1) : charSum ψ f = 0 := by
  -- Write $f = C a * X + C b$ with $a \neq 0$.
  obtain ⟨a, b, ha⟩ : ∃ a b : F, a ≠ 0 ∧ f = Polynomial.C a * Polynomial.X + Polynomial.C b := by
    exact ⟨ f.coeff 1, f.coeff 0, by rw [ ← hf, Polynomial.coeff_natDegree ] ; aesop, Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq hf ) ▸ by aesop ⟩;
  -- Then `charSum ψ f = ∑ x, ψ (a*x + b) = ψ b * ∑ x, ψ (a*x)`.
  have h_sum : charSum ψ f = ψ b * ∑ x : F, ψ (a * x) := by
    simp +decide [ *, charSum, Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ ← AddChar.map_add_eq_mul ] ; ring;
  -- The map `x ↦ a*x` is a bijection of `F` (a ≠ 0), so `∑ x, ψ(a*x) = ∑ y, ψ y`.
  have h_bij : ∑ x : F, ψ (a * x) = ∑ y : F, ψ y := by
    exact Equiv.sum_comp ( Equiv.mulLeft₀ a ha.1 ) fun x => ψ x;
  rw [ h_sum, h_bij, AddChar.sum_eq_zero_of_ne_one hψ, MulZeroClass.mul_zero ]

/-
Twisting the character by `mulShift c` (i.e. `a ↦ ψ (c * a)`) is the same as scaling the
polynomial by the constant `c`:
`charSum (ψ.mulShift c) f = charSum ψ (C c * f)`.

Since every nontrivial additive character of a finite field is of the form `ψ₀.mulShift c` for a
fixed `ψ₀` and some `c ≠ 0`, this lemma reduces the Weil bound to a single fixed nontrivial
character.
-/
lemma charSum_mulShift (ψ : AddChar F ℂ) (c : F) (f : F[X]) :
    charSum (ψ.mulShift c) f = charSum ψ (Polynomial.C c * f) := by
  refine' Finset.sum_congr rfl fun x _ => _;
  simp +decide [ AddChar.mulShift_apply ]

end Weil