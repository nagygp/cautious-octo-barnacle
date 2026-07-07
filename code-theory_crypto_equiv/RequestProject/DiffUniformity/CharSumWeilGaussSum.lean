import Mathlib
import RequestProject.DiffUniformity.CharSumBounds

/-!
# The Gauss-sum magnitude gate and the Gauss-sum route to the `d ≥ 3` Weil bound

This module attacks the higher-degree (`d ≥ 3`) one-variable Weil bound
(`CharSumBounds.WeilBoundOne`) along the classical **Gauss-sum** route, isolating
and discharging its quantitative core.

Every Gauss/Jacobi-sum proof of the Weil bound rests on one exact magnitude fact:
for a nontrivial multiplicative character `χ` and a primitive additive character
`ψ` of a finite field, the Gauss sum has modulus exactly `√q`. Mathlib provides
the quadratic special case (`gaussSum_sq`, used in
`FlystelWalshGaussSum.lean`) and the product identity
`gaussSum_mul_gaussSum_eq_card`, but **not** the general magnitude. We prove it
here for ℂ-valued characters:

```
‖gaussSum χ ψ‖ = √q       (χ ≠ 1, ψ primitive).
```

The proof computes `‖g‖² = g · conj g = gaussSum χ ψ · gaussSum χ⁻¹ ψ⁻¹ = q` using
that complex conjugation sends character values to their inverses
(`MulChar.star_eq_inv`, `AddChar.starComp_apply`).

With the magnitude in hand, the **degree-`d` Weil bound** reduces to a purely
algebraic decomposition step: whenever the character sum of `f` can be written as
a sum of at most `d − 1` Gauss sums of nontrivial characters, the Weil bound
`‖∑_x ψ(f x)‖ ≤ (d − 1)·√q` follows immediately
(`weilBoundOne_of_eq_sum_gaussSum`). For a monomial `f(x) = xᵈ` the required
decomposition is the classical character-orthogonality count of `d`-th roots; that
combinatorial input (general `d`-th-root orthogonality, beyond the quadratic case
in Mathlib) is the sole remaining gap, here exposed as an explicit hypothesis.

## Main results

* `norm_gaussSum` — the exact magnitude `‖gaussSum χ ψ‖ = √q`.
* `weilBoundOne_of_eq_sum_gaussSum` — the Weil bound from a Gauss-sum
  decomposition of length `≤ d − 1`.
-/

open Finset BigOperators

namespace APN
namespace CharSumBounds

variable {F : Type*} [Field F] [Fintype F]

/-
**The exact Gauss-sum magnitude.** For a nontrivial ℂ-valued multiplicative
character `χ` and a primitive additive character `ψ` of a finite field,
`‖gaussSum χ ψ‖ = √q`. This is the quantitative heart of every Gauss/Jacobi-sum
proof of the Weil bound.
-/
theorem norm_gaussSum (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h_conj : starRingEnd ℂ (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
    unfold gaussSum;
    rw [ map_sum ];
    refine' Finset.sum_congr rfl fun x _ => _;
    have := CharP.char_ne_zero_of_finite F ( ringChar F );
    simp +decide [ ← MulChar.star_eq_inv, ← AddChar.starComp_apply ( Nat.pos_of_ne_zero this ) ];
  have h_norm_sq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    convert congr_arg Complex.re ( gaussSum_mul_gaussSum_eq_card hχ hψ ) using 1;
    rw [ ← h_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re ];
  rw [ ← h_norm_sq, Real.sqrt_sq ( norm_nonneg _ ) ]

/-
**The Weil bound from a Gauss-sum decomposition.** If the one-variable
character sum of `f` is a sum of Gauss sums of nontrivial characters indexed by a
finset `S` with `S.card ≤ d − 1`, then `f` obeys the degree-`d` Weil bound
`‖∑_x ψ(f x)‖ ≤ (d − 1)·√q`.
-/
theorem weilBoundOne_of_eq_sum_gaussSum (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (f : F → F) (d : ℕ) (S : Finset (MulChar F ℂ))
    (hScard : S.card ≤ d - 1) (hd : 1 ≤ d)
    (hS : ∀ χ ∈ S, χ ≠ 1)
    (hdecomp : charSumOne ψ f = ∑ χ ∈ S, gaussSum χ ψ) :
    WeilBoundOne ψ f d := by
  refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( S.card : ℝ ) ≤ d - 1 by exact le_tsub_of_add_le_right <| mod_cast Nat.succ_le_of_lt <| lt_of_le_of_lt hScard <| Nat.sub_lt hd zero_lt_one ) <| Real.sqrt_nonneg _ );
  exact hdecomp.symm ▸ le_trans ( norm_sum_le _ _ ) ( by simpa using Finset.sum_le_sum fun χ hχ => norm_gaussSum χ ( hS χ hχ ) ψ hψ |> le_of_eq )

end CharSumBounds
end APN