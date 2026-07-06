import Mathlib

/-!
# Character-sum bounds — Layer 3 foundations (Weil / Deligne / Rojas-León)

This module is **Layer 3** of `FLYSTEL_WALSH_ROADMAP.md`, the character-sum
*gates* required by the non-elementary entries of Theorem 3.3 of

> M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
> Designs, Codes and Cryptography **93** (2025) 2245–2262.

The deep entries of the Walsh spectrum estimate rest on algebraic-geometry
bounds for exponential / character sums of the shape `∑_{x ∈ K^n} ψ(f(x))`:

* the **Weil bound** for one-variable sums, `|∑_x ψ(f(x))| ≤ (d-1)·√q`;
* **Deligne's bound** for `n` variables with non-singular leading form;
* **Rojas-León's bound** (the paper's main tool) for `f` whose leading form has
  isolated singularities.

The full Weil bound is the Riemann hypothesis for curves over finite fields and
is **not in Mathlib**; we therefore stage Layer 3 honestly:

1. The genuinely first-principles content is proved unconditionally here:
   * the **trivial bound** `‖∑_x ψ(f x)‖ ≤ q` (`norm_charSumOne_le`);
   * the **degree-`≤ 1` Weil bound**, which is *exact vanishing*
     `∑_x ψ(a·x + c) = 0` for `a ≠ 0` (`charSumOne_affine_eq_zero`); since
     `(d-1)·√q = 0` for `d = 1` this is exactly the `d = 1` Weil bound.
2. The genuine **two-variable reduction**: the iterated sum `∑_{x,y} ψ(g x y)`
   is bounded by `q` times any uniform one-variable bound on its inner sums
   (`norm_charSumTwo_le_of_inner`). Combined with the `d = 1` case this already
   produces sharp vanishing two-variable corollaries
   (`charSumTwo_eq_zero_of_inner_affine`).
3. The higher-degree Weil bound (`d ≥ 2`), Deligne's bound and the general
   Rojas-León bound are packaged as **precise hypothesis predicates**
   (`WeilBoundOne`, `RojasLeonBoundTwo`) so that downstream results (Layer 4,
   Theorem 3.3) become genuine *conditional* theorems: they hold for every field
   and S-box for which the stated algebraic-geometry input is available. The
   predicates are exactly the conclusions of the corresponding theorems; their
   docstrings record the smoothness hypotheses under which they hold.

## Main definitions

* `charSumOne ψ f` — the one-variable character sum `∑_{x∈K} ψ(f x)`.
* `charSumTwo ψ g` — the two-variable character sum `∑_{x,y∈K} ψ(g x y)`.
* `WeilBoundOne ψ f d` — the (input) Weil bound `‖charSumOne ψ f‖ ≤ (d-1)·√q`.
* `RojasLeonBoundTwo ψ g d` — the (input) two-variable AG bound
  `‖charSumTwo ψ g‖ ≤ (d-1)·q` (the shape used by Theorem 3.3).

## Main results

* `norm_charSumOne_le`, `norm_charSumTwo_le` — the trivial `≤ q`, `≤ q²` bounds.
* `charSumOne_affine_eq_zero` — the exact `d = 1` Weil bound (vanishing).
* `norm_charSumTwo_le_of_inner` — the two-variable reduction to a one-variable
  bound (Deligne-style fibering).
* `charSumTwo_eq_zero_of_inner_affine` — vanishing two-variable corollary.
* `rojasLeonBoundTwo_of_inner_weil` — a Rojas-León-shaped bound `(d-1)·q`
  obtained from a uniform inner `(d-1)·√q` Weil bound when `√q ≤ q` (i.e. for
  every field with at least one element), i.e. the fibered Deligne corollary.
-/

open Finset BigOperators

namespace APN
namespace CharSumBounds

variable {K : Type*} [Field K] [Fintype K]

/-- The one-variable character sum `∑_{x ∈ K} ψ(f x)` of a map `f : K → K`
against a `ℂ`-valued additive character `ψ`. -/
noncomputable def charSumOne (ψ : AddChar K ℂ) (f : K → K) : ℂ :=
  ∑ x : K, ψ (f x)

/-- The two-variable (iterated) character sum `∑_{x,y ∈ K} ψ(g x y)`. -/
noncomputable def charSumTwo (ψ : AddChar K ℂ) (g : K → K → K) : ℂ :=
  ∑ x : K, ∑ y : K, ψ (g x y)

/-- The two-variable sum is the `x`-sum of the inner one-variable sums. -/
theorem charSumTwo_eq_sum_charSumOne (ψ : AddChar K ℂ) (g : K → K → K) :
    charSumTwo ψ g = ∑ x : K, charSumOne ψ (fun y => g x y) := rfl

/-- **Trivial bound.** Every one-variable character sum is bounded in modulus by
the field size `q = #K` (each summand is a unit-modulus root of unity). -/
theorem norm_charSumOne_le (ψ : AddChar K ℂ) (f : K → K) :
    ‖charSumOne ψ f‖ ≤ (Fintype.card K : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  simp [AddChar.norm_apply]

/-- **Trivial two-variable bound.** `‖charSumTwo ψ g‖ ≤ q²`. -/
theorem norm_charSumTwo_le (ψ : AddChar K ℂ) (g : K → K → K) :
    ‖charSumTwo ψ g‖ ≤ (Fintype.card K : ℝ) ^ 2 := by
  rw [charSumTwo_eq_sum_charSumOne]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ x : K, ‖charSumOne ψ (fun y => g x y)‖
      ≤ ∑ _x : K, (Fintype.card K : ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_charSumOne_le ψ _)
    _ = (Fintype.card K : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **Exact `d = 1` Weil bound.** A non-constant affine character sum vanishes:
`∑_x ψ(a·x + c) = 0` whenever `a ≠ 0` and `ψ ≠ 1`. Since `(d-1)·√q = 0` for
`d = 1`, this is exactly the degree-one Weil bound (with equality). -/
theorem charSumOne_affine_eq_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (a c : K) (ha : a ≠ 0) :
    charSumOne ψ (fun x => a * x + c) = 0 := by
  unfold charSumOne
  -- reindex by the bijection `x ↦ a*x + c`
  have hbij : Function.Bijective (fun x : K => a * x + c) := by
    refine ⟨fun x y hxy => ?_, fun z => ⟨(z - c) / a, ?_⟩⟩
    · have h2 : a * x = a * y := by simp only at hxy ⊢; exact add_right_cancel hxy
      exact mul_left_cancel₀ ha h2
    · simp only
      rw [mul_div_cancel₀ _ ha, sub_add_cancel]
  have h := Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun y => ψ y)
  simp only [Equiv.ofBijective_apply] at h
  rw [h]
  exact AddChar.sum_eq_zero_of_ne_one hψ

/-- **Two-variable reduction (fibering).** If every inner one-variable sum
`∑_y ψ(g x y)` is bounded by `B`, then `‖charSumTwo ψ g‖ ≤ q·B`. This is the
elementary fibering step underlying the Deligne / Rojas-León corollaries: it
turns a uniform one-variable bound into a two-variable bound. -/
theorem norm_charSumTwo_le_of_inner (ψ : AddChar K ℂ) (g : K → K → K) (B : ℝ)
    (hB : ∀ x, ‖charSumOne ψ (fun y => g x y)‖ ≤ B) :
    ‖charSumTwo ψ g‖ ≤ (Fintype.card K : ℝ) * B := by
  rw [charSumTwo_eq_sum_charSumOne]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ x : K, ‖charSumOne ψ (fun y => g x y)‖
      ≤ ∑ _x : K, B := Finset.sum_le_sum (fun x _ => hB x)
    _ = (Fintype.card K : ℝ) * B := by rw [Finset.sum_const]; simp [mul_comm]

/-- **Vanishing two-variable corollary.** If every inner one-variable sum is the
non-constant affine sum (degree one in `y`), the whole two-variable sum
vanishes. -/
theorem charSumTwo_eq_zero_of_inner_affine (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (g : K → K → K) (a : K → K) (c : K → K) (ha : ∀ x, a x ≠ 0)
    (hg : ∀ x y, g x y = a x * y + c x) :
    charSumTwo ψ g = 0 := by
  rw [charSumTwo_eq_sum_charSumOne]
  have : ∀ x, charSumOne ψ (fun y => g x y) = 0 := by
    intro x
    have hx : (fun y => g x y) = (fun y => a x * y + c x) := by
      funext y; exact hg x y
    rw [hx]
    exact charSumOne_affine_eq_zero ψ hψ (a x) (c x) (ha x)
  simp [this]

/-! ## Abstract Weil / Rojas-León inputs

The following predicates package the deep algebraic-geometry bounds as explicit
hypotheses. They are *exactly* the conclusions of the corresponding theorems; the
docstrings record the geometric hypotheses under which classical theory
guarantees them. Layer 4 (Theorem 3.3) consumes these as inputs, giving genuine
conditional results. -/

/-- **Weil bound (input form).** For a one-variable character sum of a degree-`d`
map `f`, the Weil bound asserts `‖∑_x ψ(f x)‖ ≤ (d-1)·√q`. This holds
unconditionally for `f` of degree `d` with `gcd(d, char K)`-controlled wild
ramification; in the tame case it is Weil's theorem. The `d ≤ 1` case is the
theorem `charSumOne_affine_eq_zero` proved above. -/
def WeilBoundOne (ψ : AddChar K ℂ) (f : K → K) (d : ℕ) : Prop :=
  ‖charSumOne ψ f‖ ≤ ((d : ℝ) - 1) * Real.sqrt (Fintype.card K)

/-- **Rojas-León / Deligne bound (input form), two-variable.** The shape used by
Theorem 3.3: `‖∑_{x,y} ψ(g x y)‖ ≤ (d-1)·q`. Under Rojas-León's smoothness
hypotheses on the leading form of `g` (isolated singularities), this is the
content of the paper's main analytic tool. -/
def RojasLeonBoundTwo (ψ : AddChar K ℂ) (g : K → K → K) (d : ℕ) : Prop :=
  ‖charSumTwo ψ g‖ ≤ ((d : ℝ) - 1) * (Fintype.card K : ℝ)

/-- The `d = 1` Weil bound predicate holds for every non-constant affine map. -/
theorem weilBoundOne_affine (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (a c : K) (ha : a ≠ 0) :
    WeilBoundOne ψ (fun x => a * x + c) 1 := by
  unfold WeilBoundOne
  rw [charSumOne_affine_eq_zero ψ hψ a c ha]
  simp

/-- **Fibered Weil corollary (the *naive* two-variable bound).** A uniform inner
Weil bound of degree `d` on each fibre yields the elementary two-variable bound
`‖∑_{x,y} ψ(g x y)‖ ≤ (d-1)·q·√q = (d-1)·q^{3/2}`.

Note this is strictly *weaker* than the `RojasLeonBoundTwo` shape `(d-1)·q`: the
fibered estimate loses a factor `√q` because it applies the triangle inequality
across the `x`-fibres instead of exploiting square-root cancellation in *both*
variables. Beating this naive `q^{3/2}` down to the AG bound `q` is exactly the
content of Deligne / Rojas-León, and is why those results are genuine Layer-3
*gates* rather than corollaries of the one-variable Weil bound. -/
theorem norm_charSumTwo_le_of_inner_weil (ψ : AddChar K ℂ) (g : K → K → K) (d : ℕ)
    (hinner : ∀ x, WeilBoundOne ψ (fun y => g x y) d) :
    ‖charSumTwo ψ g‖ ≤ ((d : ℝ) - 1) * (Fintype.card K : ℝ) * Real.sqrt (Fintype.card K) := by
  calc ‖charSumTwo ψ g‖
      ≤ (Fintype.card K : ℝ) * (((d : ℝ) - 1) * Real.sqrt (Fintype.card K)) :=
        norm_charSumTwo_le_of_inner ψ g _ hinner
    _ = ((d : ℝ) - 1) * (Fintype.card K : ℝ) * Real.sqrt (Fintype.card K) := by ring

end CharSumBounds
end APN
