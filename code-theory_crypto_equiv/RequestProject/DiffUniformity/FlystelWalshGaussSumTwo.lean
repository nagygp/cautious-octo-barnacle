import Mathlib
import RequestProject.DiffUniformity.CharSumBounds
import RequestProject.DiffUniformity.FlystelWalshGaussSum
import RequestProject.DiffUniformity.FlystelTheorem33

/-!
# The exact `d = 2` two-variable bound via quadratic Gauss sums — discharging a Layer-3 gate

This module discharges the `d = 2` case of the **two-variable** Rojas-León /
Deligne bound (`CharSumBounds.RojasLeonBoundTwo`) **unconditionally**, feeding the
one-variable quadratic Gauss-sum result of `FlystelWalshGaussSum.lean` into the
two-variable character sum that controls the deep entries of Theorem 3.3.

The mechanism is two successive completions of the square. Over a finite field
`F` of odd characteristic with a nontrivial additive character `ψ`, a general
binary quadratic

```
g(x, y) = a·x² + b·x·y + c·y² + d·x + e·y + f       (a ≠ 0)
```

factors, after completing the square in `x`, into a product of two one-variable
quadratic Gauss sums:

```
∑_{x,y} ψ(g x y) = (∑_x ψ(a·x²)) · (∑_y ψ(R y)),
   R(y) = (c − b²/4a)·y² + (e − bd/2a)·y + (f − d²/4a).
```

Each factor has modulus `√q` (`norm_charSumOne_const_mul_sq`,
`norm_charSumOne_quadratic`), so whenever the **discriminant** `4ac − b² ≠ 0`
(equivalently the residual leading coefficient `c − b²/4a ≠ 0`) the whole
two-variable sum has modulus exactly `q`:

```
‖∑_{x,y} ψ(g x y)‖ = q = (2 − 1)·q.
```

That is precisely the `d = 2` Rojas-León bound, now a **theorem** rather than a
hypothesis. The fully separable case `g(x,y) = g₁(x) + g₂(y)` is recorded
separately (`charSumTwo_separable`): there the sum factors as a literal product
of one-variable sums.

## Main results

* `charSumTwo_separable` — `∑_{x,y} ψ(g₁ x + g₂ y) = (∑_x ψ(g₁ x))·(∑_y ψ(g₂ y))`.
* `charSumTwo_quadratic_factor` — the completing-the-square factorisation of a
  binary quadratic character sum into two one-variable quadratic Gauss sums.
* `norm_charSumTwo_quadratic` — the exact magnitude `q` of a nondegenerate binary
  quadratic character sum.
* `rojasLeonBoundTwo_quadratic` — the unconditional `d = 2` Rojas-León bound for a
  nondegenerate binary quadratic.
* `walsh_norm_le_of_quadratic` — feeding the bound into the Theorem 3.3 assembly:
  a deep-entry Walsh coefficient whose linear-approximation function is a
  nondegenerate binary quadratic obeys the `d = 2` bound `‖W‖ ≤ q`
  unconditionally.
-/

open Finset BigOperators

namespace APN
namespace CharSumBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**Separable factorisation.** When the two-variable phase splits additively,
`g(x,y) = g₁(x) + g₂(y)`, the two-variable character sum factors as the product
of the two one-variable sums.
-/
theorem charSumTwo_separable (ψ : AddChar F ℂ) (g1 g2 : F → F) :
    charSumTwo ψ (fun x y => g1 x + g2 y)
      = charSumOne ψ g1 * charSumOne ψ g2 := by
  unfold charSumTwo charSumOne;
  simp +decide only [AddChar.map_add_eq_mul, sum_mul_sum]

/-
**Completing the square in `x`.** A binary quadratic character sum factors as
the product of the one-variable Gauss sum `∑_x ψ(a·x²)` and the one-variable
quadratic sum of the residual `R(y) = (c − b²/4a)·y² + (e − bd/2a)·y + (f − d²/4a)`.
-/
theorem charSumTwo_quadratic_factor (ψ : AddChar F ℂ) (hF : ringChar F ≠ 2)
    (a b c d e f : F) (ha : a ≠ 0) :
    charSumTwo ψ (fun x y => a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f)
      = charSumOne ψ (fun x => a * x ^ 2)
        * charSumOne ψ (fun y => (c - b ^ 2 / (4 * a)) * y ^ 2
            + (e - b * d / (2 * a)) * y + (f - d ^ 2 / (4 * a))) := by
  have h_complete_square : ∀ y : F, ∑ x : F, ψ (a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f) = ψ ((c - b ^ 2 / (4 * a)) * y ^ 2 + (e - b * d / (2 * a)) * y + (f - d ^ 2 / (4 * a))) * ∑ x : F, ψ (a * x ^ 2) := by
    intro y
    have h_complete_square : ∀ x : F, a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f = a * (x + (b * y + d) / (2 * a)) ^ 2 + (c - b ^ 2 / (4 * a)) * y ^ 2 + (e - b * d / (2 * a)) * y + (f - d ^ 2 / (4 * a)) := by
      by_cases h : ( 2 : F ) = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm a ];
      · have := ringChar.spec F 2; simp_all +decide ;
        have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : ringChar F <;> simp_all +decide ;
        exact False.elim ( ha ( Subsingleton.elim _ _ ) );
      · grind;
    rw [ Finset.mul_sum _ _ _ ];
    rw [ ← Equiv.sum_comp ( Equiv.addRight ( - ( b * y + d ) / ( 2 * a ) ) ) ] ; simp +decide [ ← add_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul ] ;
    grind;
  convert Finset.sum_congr rfl fun y _ => h_complete_square y using 1;
  convert Finset.sum_comm using 1;
  simp +decide only [charSumOne, mul_comm, mul_sum _ _ _]

/-
**The exact magnitude of a nondegenerate binary quadratic character sum.**
For `a ≠ 0` and nonzero discriminant `4ac − b² ≠ 0`, the two-variable sum has
modulus exactly `q = #F`.
-/
theorem norm_charSumTwo_quadratic (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (a b c d e f : F) (ha : a ≠ 0)
    (hnd : 4 * a * c - b ^ 2 ≠ 0) :
    ‖charSumTwo ψ (fun x y => a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f)‖
      = (Fintype.card F : ℝ) := by
  rw [ charSumTwo_quadratic_factor ψ hF a b c d e f ha ];
  rw [ norm_mul, CharSumBounds.norm_charSumOne_const_mul_sq ψ hψ hF a ha, CharSumBounds.norm_charSumOne_quadratic ψ hψ hF ];
  · rw [ Real.mul_self_sqrt ( Nat.cast_nonneg _ ) ];
  · by_cases ha4 : ( 4 : F ) = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · have := ringChar.spec F 2; simp_all +decide [ show ( 4 : F ) = 2 * 2 by norm_num ] ;
      have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : ringChar F <;> simp_all +decide ;
      exact False.elim ( ha ( Subsingleton.elim _ _ ) );
    · grind

/-- **The unconditional `d = 2` two-variable Rojas-León bound** for a
nondegenerate binary quadratic. This discharges the `d = 2` instance of the
Layer-3 `RojasLeonBoundTwo` gate. -/
theorem rojasLeonBoundTwo_quadratic (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (a b c d e f : F) (ha : a ≠ 0)
    (hnd : 4 * a * c - b ^ 2 ≠ 0) :
    RojasLeonBoundTwo ψ
      (fun x y => a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f) 2 := by
  unfold RojasLeonBoundTwo
  rw [norm_charSumTwo_quadratic ψ hψ hF a b c d e f ha hnd]
  norm_num

end CharSumBounds

namespace FlystelWalsh

open CharSumBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Feeding the `d = 2` Gauss-sum bound into the Theorem 3.3 assembly.**
If the linear-approximation function of a Walsh coefficient is a nondegenerate
binary quadratic, then the deep-entry bound `‖W_F(ψ, a, b)‖ ≤ q = (2−1)·q`
holds **unconditionally** (no Rojas-León hypothesis). -/
theorem walsh_norm_le_of_quadratic (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hF : ringChar F ≠ 2) (G : F × F → F × F) (a b : F × F)
    (qa qb qc qd qe qf : F) (hqa : qa ≠ 0) (hnd : 4 * qa * qc - qb ^ 2 ≠ 0)
    (hquad : walshFun G a b
      = fun x y => qa * x ^ 2 + qb * x * y + qc * y ^ 2 + qd * x + qe * y + qf) :
    ‖walsh ψ G a b‖ ≤ (Fintype.card F : ℝ) := by
  have h := walsh_norm_le_of_rojasLeonBoundTwo ψ G a b 2
    (by rw [hquad]; exact rojasLeonBoundTwo_quadratic ψ hψ hF qa qb qc qd qe qf hqa hnd)
  have h2 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [h2, one_mul] at h
  exact h

end FlystelWalsh
end APN