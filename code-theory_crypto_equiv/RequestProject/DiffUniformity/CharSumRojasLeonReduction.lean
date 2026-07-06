import Mathlib
import RequestProject.DiffUniformity.CharSumBounds
import RequestProject.DiffUniformity.FlystelWalshGaussSum
import RequestProject.DiffUniformity.CharSumMonomialWeil

/-!
# Reducing the two-variable Rojas–León bound to a one-variable Weil bound

This module makes the **Track 2** reduction precise and unconditional: for any
two-variable phase that is a *nondegenerate quadratic in the second variable*
(after completing the square) with an arbitrary residual `P` in the first
variable, the two-variable Rojas–León bound `RojasLeonBoundTwo` follows from the
**one-variable** Weil bound `WeilBoundOne` on `P` alone.

Concretely, if

```
g(x, y) = c·(y + s x)² + P x        (c ≠ 0),
```

then the inner sum over `y` is a translated quadratic Gauss sum of modulus `√q`,
so the two-variable sum **factors**:

```
∑_{x,y} ψ(g x y) = (∑_y ψ(c·y²)) · (∑_x ψ(P x)),
```

(`charSumTwo_eq_gauss_mul`). Taking moduli and feeding in any degree-`d`
one-variable Weil bound on `P` gives

```
‖∑_{x,y} ψ(g x y)‖ = √q · ‖∑_x ψ(P x)‖ ≤ √q · (d−1)·√q = (d−1)·q,
```

i.e. exactly the two-variable Rojas–León bound `RojasLeonBoundTwo ψ g d`
(`rojasLeonBoundTwo_of_factor`).

This is the genuine mechanism behind the `d = 3` Anemoi (`x³`) and `d = 5`
Poseidon (`x⁵`) sandwiches: integrating out the quadratic variable contributes a
`√q` exactly, leaving a one-variable degree-`d` sum. It therefore reduces the
*two-dimensional* algebraic-geometry input (Rojas–León / Deligne for surfaces) to
the *one-dimensional* Weil bound on the residual `P`.

When the residual `P` is a **monomial** `xᵈ`, the one-variable bound is itself
unconditional via `CharSumBounds.weilBoundOne_monomial` (Track 1), giving a fully
unconditional two-variable bound (`rojasLeonBoundTwo_of_factor_monomial`). For the
concrete Anemoi/Poseidon deep entries the residual `P` is a genuine degree-`d`
polynomial (a cubic resp. quintic with lower-order terms produced by completing
the square), so their fully unconditional bound still rests on the general
one-variable degree-`d` Weil bound for `P` — now a strictly *one-dimensional*
gate.

## Main results

* `charSumTwo_eq_gauss_mul` — the completing-the-square factorisation.
* `rojasLeonBoundTwo_of_factor` — the `2D → 1D` reduction of the Rojas–León bound.
* `rojasLeonBoundTwo_of_factor_monomial` — the unconditional monomial instance.
-/

open Finset BigOperators

namespace APN
namespace CharSumBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**Completing the square in the second variable factors the two-variable sum.**
If `g(x, y) = c·(y + s x)² + P x`, then `∑_{x,y} ψ(g x y)` factors as the
product of the quadratic Gauss sum `∑_y ψ(c·y²)` and the one-variable residual
sum `∑_x ψ(P x)`.
-/
theorem charSumTwo_eq_gauss_mul (ψ : AddChar F ℂ) (c : F) (s P : F → F)
    (g : F → F → F) (hg : ∀ x y, g x y = c * (y + s x) ^ 2 + P x) :
    charSumTwo ψ g
      = charSumOne ψ (fun y => c * y ^ 2) * charSumOne ψ P := by
  -- We can factor out the constant factor `charSumOne ψ (fun y => c * y ^ 2)` from the sum.
  have h_factor : ∀ x : F, ∑ y : F, ψ (c * (y + s x) ^ 2 + P x) = charSumOne ψ (fun y => c * y ^ 2) * ψ (P x) := by
    intro x
    have h_inner_sum : ∑ y : F, ψ (c * (y + s x) ^ 2 + P x) = ∑ y : F, ψ (c * y ^ 2) * ψ (P x) := by
      have h_inner_sum : ∑ y : F, ψ (c * (y + s x) ^ 2 + P x) = ∑ y : F, ψ (c * (y + s x) ^ 2) * ψ (P x) := by
        exact Finset.sum_congr rfl fun _ _ => AddChar.map_add_eq_mul _ _ _;
      rw [ h_inner_sum, ← Equiv.sum_comp ( Equiv.addRight ( -s x ) ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    rw [ h_inner_sum, ← Finset.sum_mul, charSumOne ];
  simp_all +decide [ charSumTwo, charSumOne ];
  rw [ Finset.mul_sum _ _ _ ]

/-
**The `2D → 1D` Rojas–León reduction.** If the two-variable phase completes
the square in the second variable to `c·(y + s x)² + P x` with `c ≠ 0`, and the
residual `P` satisfies the degree-`d` one-variable Weil bound, then `g` satisfies
the two-variable Rojas–León bound `‖∑_{x,y} ψ(g x y)‖ ≤ (d−1)·q`.
-/
theorem rojasLeonBoundTwo_of_factor (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (c : F) (hc : c ≠ 0) (s P : F → F) (g : F → F → F) (d : ℕ)
    (hg : ∀ x y, g x y = c * (y + s x) ^ 2 + P x)
    (hWeil : WeilBoundOne ψ P d) :
    RojasLeonBoundTwo ψ g d := by
  unfold RojasLeonBoundTwo WeilBoundOne at *;
  convert mul_le_mul_of_nonneg_left hWeil ( Real.sqrt_nonneg ( Fintype.card F ) ) using 1;
  · rw [ charSumTwo_eq_gauss_mul ψ c s P g hg, norm_mul, CharSumBounds.norm_charSumOne_const_mul_sq ψ hψ hF c hc ];
  · ring ; norm_num

/-- **Unconditional monomial instance.** If the two-variable phase completes the
square to `c·(y + s x)² + a·xᵈ` (`c ≠ 0`, `a` arbitrary but the residual a pure
monomial `a·xᵈ`... taken here as `xᵈ`), then the two-variable Rojas–León bound
holds unconditionally, by Track 1's monomial Weil bound. -/
theorem rojasLeonBoundTwo_of_factor_monomial (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hF : ringChar F ≠ 2) (c : F) (hc : c ≠ 0) (s : F → F) (g : F → F → F) (d : ℕ)
    (hd : 1 ≤ d)
    (hg : ∀ x y, g x y = c * (y + s x) ^ 2 + x ^ d) :
    RojasLeonBoundTwo ψ g d := by
  have hψ1 : ψ ≠ 1 := by
    rintro rfl
    obtain ⟨a, ha⟩ := exists_ne (0 : F)
    exact (hψ ha) (by ext x; simp [AddChar.mulShift_apply])
  exact rojasLeonBoundTwo_of_factor ψ hψ1 hF c hc s (fun x => x ^ d) g d hg
    (weilBoundOne_monomial ψ hψ d hd)

end CharSumBounds
end APN