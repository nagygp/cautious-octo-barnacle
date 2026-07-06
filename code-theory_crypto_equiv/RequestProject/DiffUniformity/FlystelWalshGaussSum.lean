import Mathlib
import RequestProject.DiffUniformity.CharSumBounds

/-!
# The exact `d = 2` Weil bound via quadratic Gauss sums — discharging a Layer-3 gate

This module discharges the `d = 2` case of the one-variable Weil bound
(`CharSumBounds.WeilBoundOne`) **unconditionally**, i.e. without taking the
algebraic-geometry character-sum estimate as a hypothesis. It is the next step of
the Flystel / AG track (`FLYSTEL_WALSH_ROADMAP.md`, Layer 3).

The mechanism is the classical **quadratic Gauss sum** identity. Over a finite
field `F` of odd characteristic with a nontrivial additive character `ψ`, the
character sum of `x ↦ x²` is a Gauss sum of the quadratic multiplicative
character, and Mathlib's `gaussSum_sq` (`g² = χ(-1)·q`) pins its modulus exactly:

```
‖∑_{x ∈ F} ψ(x²)‖ = √q.
```

Completing the square reduces a general quadratic `a·x² + b·x + c` (`a ≠ 0`) to
this case, giving the exact `d = 2` Weil bound `‖∑_x ψ(f x)‖ ≤ (2−1)·√q = √q`.

## Main results

* `charSumOne_sq_eq_gaussSum` — `∑_x ψ(x²) = gaussSum χ_ℂ ψ` for the ℂ-valued
  quadratic character `χ_ℂ`.
* `norm_charSumOne_sq` — the exact magnitude `‖∑_x ψ(x²)‖ = √q`.
* `weilBoundOne_sq` — the `d = 2` Weil bound for `x ↦ x²`.
* `norm_charSumOne_quadratic`, `weilBoundOne_quadratic` — the same for a general
  quadratic `a·x² + b·x + c` with `a ≠ 0` (by completing the square).
-/

open Finset BigOperators

namespace APN
namespace CharSumBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ℂ-valued quadratic multiplicative character of `F`, the composition of the
integer-valued quadratic character with `ℤ → ℂ`. -/
noncomputable def quadCharC : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

/-- The ℂ-valued quadratic character is nontrivial in odd characteristic. -/
theorem quadCharC_ne_one (hF : ringChar F ≠ 2) : (quadCharC : MulChar F ℂ) ≠ 1 := by
  convert MulChar.ringHomComp_ne_one_iff ( show Function.Injective ( Int.castRingHom ℂ ) from Int.cast_injective ) |>.2 ( quadraticChar_ne_one hF ) using 1

/-- The ℂ-valued quadratic character is a quadratic character. -/
theorem quadCharC_isQuadratic : (quadCharC : MulChar F ℂ).IsQuadratic :=
  (quadraticChar_isQuadratic F).comp _

/-- `χ_ℂ(-1)` has modulus one (it is `±1`). -/
theorem norm_quadCharC_neg_one : ‖(quadCharC : MulChar F ℂ) (-1)‖ = 1 := by
  unfold quadCharC; norm_num;
  rw [ quadraticCharFun ] ; aesop

/-- **The square character sum is a Gauss sum.** Over a finite field of odd
characteristic, `∑_{x} ψ(x²) = gaussSum χ_ℂ ψ`, because the number of square roots
of `a` is `χ(a) + 1` and `∑_a ψ(a) = 0`. -/
theorem charSumOne_sq_eq_gaussSum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (hF : ringChar F ≠ 2) :
    charSumOne ψ (fun x => x ^ 2) = gaussSum (quadCharC : MulChar F ℂ) ψ := by
  unfold charSumOne gaussSum;
  -- By fiberwise summation, we can rewrite the left-hand side as $\sum_{a \in F} \sum_{x \in \{x \in F \mid x^2 = a\}} \psi(a)$.
  have h_fiberwise : ∑ x : F, ψ (x ^ 2) = ∑ a : F, ∑ x ∈ Finset.univ.filter (fun x => x ^ 2 = a), ψ a := by
    simp +decide only [sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  -- By `quadraticChar_card_sqrts hF a`, the cardinality of the fiber `{x | x^2 = a}` equals `quadraticChar F a + 1` as an integer.
  have h_card : ∀ a : F, (Finset.card (Finset.filter (fun x => x ^ 2 = a) Finset.univ) : ℂ) = (quadraticChar F a : ℂ) + 1 := by
    intro a
    have h_card_eq : (Finset.card (Finset.filter (fun x => x ^ 2 = a) Finset.univ) : ℤ) = (quadraticChar F a : ℤ) + 1 := by
      convert quadraticChar_card_sqrts hF a using 1;
      simp +decide
    exact_mod_cast h_card_eq;
  simp_all +decide [ Finset.sum_add_distrib, add_mul ];
  simp +decide [ quadCharC, AddChar.sum_eq_zero_of_ne_one hψ ]

/-- **The exact quadratic Gauss sum magnitude `‖∑_x ψ(x²)‖ = √q`.** -/
theorem norm_charSumOne_sq (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (hF : ringChar F ≠ 2) :
    ‖charSumOne ψ (fun x => x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  convert congr_arg Real.sqrt ?_ using 1;
  rw [ charSumOne_sq_eq_gaussSum ψ hψ hF ];
  have := gaussSum_sq ( quadCharC_ne_one hF ) ( quadCharC_isQuadratic ) ( AddChar.IsPrimitive.of_ne_one hψ );
  replace := congr_arg Complex.normSq this ; norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_pow ] at this ⊢;
  rw [ norm_quadCharC_neg_one ] at this ; aesop

/-- **The `d = 2` Weil bound for `x ↦ x²`, unconditionally.** -/
theorem weilBoundOne_sq (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (hF : ringChar F ≠ 2) :
    WeilBoundOne ψ (fun x => x ^ 2) 2 := by
  unfold WeilBoundOne
  rw [norm_charSumOne_sq ψ hψ hF]
  norm_num

/-- **Translation/scaling invariance.** For `a ≠ 0`, `∑_x ψ(a·x²)` has modulus
`√q`, since `t ↦ ψ(a·t)` is again a nontrivial additive character. -/
theorem norm_charSumOne_const_mul_sq (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (a : F) (ha : a ≠ 0) :
    ‖charSumOne ψ (fun x => a * x ^ 2)‖ = Real.sqrt (Fintype.card F) := by
  convert norm_charSumOne_sq ( AddChar.mulShift ψ ( a ) ) _ hF using 1;
  intro h;
  apply hψ;
  convert congr_arg ( fun f => f.mulShift a⁻¹ ) h using 1;
  ext x; simp +decide [ ha ] ;

/-- **The exact magnitude for a general quadratic.** For `a ≠ 0`,
`‖∑_x ψ(a·x² + b·x + c)‖ = √q`, by completing the square. -/
theorem norm_charSumOne_quadratic (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (a b c : F) (ha : a ≠ 0) :
    ‖charSumOne ψ (fun x => a * x ^ 2 + b * x + c)‖ = Real.sqrt (Fintype.card F) := by
  -- Complete the square. Since `ringChar F ≠ 2`, `(2 : F) ≠ 0` and `a ≠ 0`, so `2*a ≠ 0` is invertible. Set `s = b / (2*a)` and `k = c - b^2/(4*a)`. Then for every `x`, `a * x^2 + b*x + c = a * (x + s)^2 + k` (verify by `field_simp; ring`).
  set s : F := b / (2 * a)
  set k : F := c - b^2 / (4 * a)
  have h_complete_square : ∀ x : F, a * x^2 + b * x + c = a * (x + s)^2 + k := by
    intro x
    ring_nf at *;
    by_cases h : ( 2 : F ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm a ];
    · have := ringChar.spec F 2; simp_all +decide ;
      have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : ringChar F <;> simp_all +decide ;
      exact False.elim ( ha ( Subsingleton.elim _ _ ) );
    · grind;
  convert norm_charSumOne_const_mul_sq ψ hψ hF a ha using 1;
  simp +decide [ charSumOne, h_complete_square ];
  rw [ ← Equiv.sum_comp ( Equiv.addRight ( -s ) ) ] ; simp +decide [ AddChar.map_add_eq_mul ];
  simp +decide [ ← Finset.sum_mul _ _ _, AddChar.norm_apply ]

/-- **The exact `d = 2` Weil bound for a general quadratic, unconditionally.**
This discharges the `d = 2` instance of the Layer-3 `WeilBoundOne` gate. -/
theorem weilBoundOne_quadratic (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (a b c : F) (ha : a ≠ 0) :
    WeilBoundOne ψ (fun x => a * x ^ 2 + b * x + c) 2 := by
  unfold WeilBoundOne
  rw [norm_charSumOne_quadratic ψ hψ hF a b c ha]
  norm_num

end CharSumBounds
end APN