import Mathlib

/-!
# Foundational layer F3 (algebraic core) — Character-sum algebra

This module is the algebraic engine shared by *all* of Section 3 of

  M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
  Designs, Codes and Cryptography (2025) 93:2245–2262.

See `ROADMAP.md` for the global DAG of layers.  Every bound proved in the paper
is, after the Sorry-Audit (M3), a statement about the **finite exponential sum**
`∑ₓ ψ(g x)` for an additive character `ψ` and an explicit function `g`.  This
file collects the *small, elegant, reusable invariants* of such sums, **each
lemma performing exactly one algebraic manipulation, logical deduction or
identity** (per the brief).  These invariants then propagate upward: `WalshAlgebra`
specialises them to `walshTransform`, and `AffineCCZ` uses the reindexing
invariant to transport Walsh norms across CCZ-equivalence.

## Caramello-bridge view (M5)

The recurring "theory move" of the paper is *variable separation*: a 2-variable
character sum over `Fq × Fq` whose phase splits as `g₁(x) + g₂(y)` lives,
equivalently, in the **product theory** `F̂ × F̂`, where it factors as a product
of two 1-variable sums (`charSum_add_factor`).  The bridge functor is
`ψ(a+b) = ψ(a)·ψ(b)` (`AddChar.map_add_eq_mul`): it turns the *additive* local
structure of the phase into the *multiplicative* global structure of the sum.
Dually, every *bijective re-indexing* of the summation variable is invisible to
the sum (`charSum_comp_equiv`), and every *additive shift* of the phase is
invisible to its **norm** (`norm_charSum_add_const`), because each character
value is a unit of the circle (`AddChar.norm_apply`).

## DAG of this layer (each node = one logical step)

```
 [norm_apply]   [map_add_eq_mul]   [Equiv.sum_comp]   [sum_mul_sum]
      |               |                  |                  |
 norm_charSum_le  charSum_add_factor  charSum_comp_equiv  …
      |               |                  |
 norm_charSum_add_const   (shift-invariance of the norm)
```
-/

open scoped BigOperators

namespace Flystel.Foundations

section CharacterSum

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {β γ : Type*} [Fintype β] [Fintype γ]

/-! ## F3.1 — the basic norm bound (one node) -/

/-- **Atomic step (triangle inequality + unit norm).**
A character sum of `#β` terms has norm at most `#β`, because each summand
`ψ(g x)` lies on the unit circle (`AddChar.norm_apply`).  This is the trivial
"diagonal" bound that every Weil/Deligne/Rojas–León estimate improves upon. -/
theorem norm_charSum_le (ψ : AddChar G ℂ) (g : β → G) :
    ‖∑ x, ψ (g x)‖ ≤ (Fintype.card β : ℝ) := by
  calc ‖∑ x, ψ (g x)‖ ≤ ∑ x, ‖ψ (g x)‖ := norm_sum_le _ _
    _ = ∑ _x : β, (1 : ℝ) := by simp [AddChar.norm_apply]
    _ = (Fintype.card β : ℝ) := by simp [Finset.card_univ]

/-! ## F3.2 — variable separation / factorization (one node)

The Caramello bridge `F̂ × F̂`: an additive split of the phase becomes a
multiplicative split of the sum. -/

/-- **Atomic step (variable separation).**
If the phase separates additively as `g(x) + h(y)`, the 2-variable character sum
**factors** as the product of the two 1-variable sums.  This is the
`F̂ × F̂` product-theory move used in Theorems 3.3/3.5/3.6 for the masks with
`b₁ + b₂ = 0`. -/
theorem charSum_add_factor (ψ : AddChar G ℂ) (g : β → G) (h : γ → G) :
    ∑ p : β × γ, ψ (g p.1 + h p.2) = (∑ x, ψ (g x)) * (∑ y, ψ (h y)) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_congr rfl (fun p _ => AddChar.map_add_eq_mul ψ (g p.1) (h p.2))

/-! ## F3.3 — re-indexing invariance (one node)

The ISO lens: any bijection of the summation variable is invisible to the sum. -/

/-- **Atomic step (re-indexing).**
Pre-composing the phase with a bijection `e` of the index leaves the character
sum unchanged.  This is the engine behind `walsh_of_CCZEquiv`: an affine
permutation of the graph **is** an `Equiv`, so it re-indexes the Walsh sum. -/
theorem charSum_comp_equiv (ψ : AddChar G ℂ) (g : β → G) (e : β ≃ β) :
    ∑ x, ψ (g (e x)) = ∑ x, ψ (g x) :=
  Equiv.sum_comp e (fun x => ψ (g x))

omit [Fintype G] in
/-- **Atomic step (re-indexing, surjective form).**
Same statement for a `Function.Bijective` reindexer, packaged for callers that
have bijectivity rather than an `Equiv`. -/
theorem charSum_comp_bijective (ψ : AddChar G ℂ) (g : β → G) {e : β → β}
    (he : Function.Bijective e) :
    ∑ x, ψ (g (e x)) = ∑ x, ψ (g x) :=
  Fintype.sum_bijective e he _ _ (fun _ => rfl)

/-! ## F3.4 — shift-invariance of the norm (one node)

The COMPRESSION lens: an additive shift of the phase multiplies the sum by a
unit-norm scalar, hence is invisible to the **norm**. -/

omit [Fintype G] in
/-- **Atomic step (global phase factor).**
Adding a constant `c` to every phase pulls out the scalar `ψ(c)`, of norm one. -/
theorem charSum_add_const (ψ : AddChar G ℂ) (g : β → G) (c : G) :
    ∑ x, ψ (c + g x) = ψ c * ∑ x, ψ (g x) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => AddChar.map_add_eq_mul ψ c (g x))

/-- **Atomic step (shift-invariance of the norm).**
The norm of a character sum is unchanged by an additive constant in the phase,
because `‖ψ c‖ = 1` (`AddChar.norm_apply`).  This is what lets the paper drop the
`ψ(⟨(a,b),c⟩)` translation factor of Eq. (6)–(10) when bounding `|W_F|`. -/
theorem norm_charSum_add_const (ψ : AddChar G ℂ) (g : β → G) (c : G) :
    ‖∑ x, ψ (c + g x)‖ = ‖∑ x, ψ (g x)‖ := by
  rw [charSum_add_const, norm_mul, AddChar.norm_apply, one_mul]

/-! ## F3.5 — orthogonality (one node)

The single most pervasive invariant: a non-trivial character sums to **zero**
over the whole group.  This `∑ ψ = 0` identity is the `b = 0` ⁄ `b ≠ 0`
dichotomy underlying every Walsh computation (and is the engine of Fourier
inversion). -/

/-- **Atomic step (orthogonality of characters).**
The sum of a non-trivial additive character over the whole group is zero. -/
theorem sum_eq_zero_of_ne_one {ψ : AddChar G ℂ} (hψ : ψ ≠ 1) :
    ∑ x, ψ x = 0 :=
  AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

end CharacterSum

/-! ## F3.6 — the field linear-sum dichotomy (one node)

Over a finite *field* every non-trivial character is primitive
(`AddChar.IsPrimitive.of_ne_one`), so the *linear* character sum `∑ₓ ψ(c·x)`
is the trivial `q` when `c = 0` and `0` when `c ≠ 0`.  This is exactly the
bookkeeping of the constant ⁄ linear terms in every Walsh expansion. -/

section Field

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- **Atomic step (linear sum vanishes for `c ≠ 0`).**
For a non-trivial character `ψ` and `c ≠ 0`, `∑ₓ ψ(c·x) = 0`, because the shift
`mulShift ψ c` is again non-trivial (primitivity over a field) and orthogonality
applies. -/
theorem sum_char_linear_eq_zero {ψ : AddChar Fq ℂ} (hψ : ψ ≠ 1)
    {c : Fq} (hc : c ≠ 0) :
    ∑ x : Fq, ψ (c * x) = 0 := by
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hne : ψ.mulShift c ≠ 1 := hprim hc
  have hh : (∑ x : Fq, ψ (c * x)) = ∑ x : Fq, (ψ.mulShift c) x :=
    Finset.sum_congr rfl (fun x _ => by rw [AddChar.mulShift_apply])
  rw [hh]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne

/-- **Atomic step (linear sum is `q` for `c = 0`).**
The degenerate companion of `sum_char_linear_eq_zero`: at `c = 0` the phase is
constant `ψ 0 = 1`, so the sum counts the field. -/
theorem sum_char_linear_eq_card (ψ : AddChar Fq ℂ) :
    ∑ _x : Fq, ψ ((0 : Fq) * x) = (Fintype.card Fq : ℂ) := by
  simp [Finset.card_univ]

end Field

end Flystel.Foundations
