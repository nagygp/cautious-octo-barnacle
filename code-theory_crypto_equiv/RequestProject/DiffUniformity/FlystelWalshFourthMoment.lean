import Mathlib
import RequestProject.DiffUniformity.FlystelWalshParseval

/-!
# Fourth moment of the field-level Walsh transform

This module is the next step of the Flystel / AG track (`FLYSTEL_WALSH_ROADMAP.md`),
extending the **Parseval (second moment)** identity of
`RequestProject/DiffUniformity/FlystelWalshParseval.lean` to the **fourth moment**.

Like Parseval, this identity is **unconditional** — it needs no algebraic-geometry
character-sum bound, only additive-character orthogonality (the same
`sum_char_dotProd` orthogonality used for Parseval, applied twice). For any
`F : K × K → K × K` over a finite field `K` (with `q = #K`) and any nontrivial
additive character `ψ`, the fourth moment of the Walsh spectrum equals `q⁴` times
the number of "second-order collision" quadruples:

```
∑_{a, b ∈ K²} ‖W_F(ψ, a, b)‖⁴
  = q⁴ · #{(x₁,x₂,x₃,x₄) ∈ (K²)⁴ : x₁ - x₂ + x₃ - x₄ = 0
                                   ∧ F x₁ - F x₂ + F x₃ - F x₄ = 0}.
```

The right-hand count is the discrete "sum-of-squares indicator" that governs the
differential/linear interplay (it is the Flystel analogue of the Pless fourth
power moment for codes); fixing the fourth moment is the precise quantitative
input behind the Sidelnikov–Chabaud–Vaudenay style nonlinearity bounds.

## Main results

* `secondOrderCollisions` — the Finset of collision quadruples.
* `walsh_fourth_moment` — the fourth-moment identity
  `∑_{a,b} ‖W_F(ψ,a,b)‖⁴ = q⁴ · #collisions`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The set of "second-order collision" quadruples
`(x₁, x₂, x₃, x₄) ∈ (K²)⁴` with `x₁ - x₂ + x₃ - x₄ = 0` and
`F x₁ - F x₂ + F x₃ - F x₄ = 0`. Its cardinality is the fourth-moment count. -/
noncomputable def secondOrderCollisions (F : K × K → K × K) :
    Finset ((K × K) × (K × K) × (K × K) × (K × K)) :=
  Finset.univ.filter fun p =>
    p.1 - p.2.1 + p.2.2.1 - p.2.2.2 = 0 ∧
      F p.1 - F p.2.1 + F p.2.2.1 - F p.2.2.2 = 0

/-
**Fourth moment of the field-level Walsh transform.** For any
`F : K × K → K × K` over a finite field `K` (`q = #K`) and any nontrivial additive
character `ψ`, the sum of the fourth powers of the Walsh moduli equals `q⁴` times
the number of second-order collision quadruples.
-/
theorem walsh_fourth_moment (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : K × K → K × K) :
    ∑ a : K × K, ∑ b : K × K, Complex.normSq (walsh ψ F a b) ^ 2
      = (Fintype.card K : ℝ) ^ 4 * (secondOrderCollisions F).card := by
  convert congr_arg Complex.re ( show ∑ a : K × K, ∑ b : K × K, ( walsh ψ F a b ) ^ 2 * ( starRingEnd ℂ ( walsh ψ F a b ) ) ^ 2 = ( Fintype.card K : ℂ ) ^ 4 * ( secondOrderCollisions F |> Finset.card : ℂ ) from ?_ ) using 1;
  · simp +decide [ ← mul_pow, Complex.normSq_eq_norm_sq ];
    simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, sq ];
  · norm_cast;
  · -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ a : K × K, ∑ b : K × K, (walsh ψ F a b) ^ 2 * (starRingEnd ℂ (walsh ψ F a b)) ^ 2 = ∑ x₁ : K × K, ∑ x₂ : K × K, ∑ x₃ : K × K, ∑ x₄ : K × K, ∑ a : K × K, ∑ b : K × K, ψ (dotProd a (x₁ - x₂ + x₃ - x₄)) * ψ (dotProd b (F x₁ - F x₂ + F x₃ - F x₄)) := by
      have h_fubini : ∀ a b : K × K, (walsh ψ F a b) ^ 2 * (starRingEnd ℂ (walsh ψ F a b)) ^ 2 = ∑ x₁ : K × K, ∑ x₂ : K × K, ∑ x₃ : K × K, ∑ x₄ : K × K, ψ (dotProd a (x₁ - x₂ + x₃ - x₄)) * ψ (dotProd b (F x₁ - F x₂ + F x₃ - F x₄)) := by
        intro a b
        have h_expand : (walsh ψ F a b) ^ 2 * (starRingEnd ℂ (walsh ψ F a b)) ^ 2 = (∑ x₁ : K × K, ψ (dotProd a x₁ + dotProd b (F x₁))) * (∑ x₂ : K × K, ψ (-(dotProd a x₂ + dotProd b (F x₂)))) * (∑ x₃ : K × K, ψ (dotProd a x₃ + dotProd b (F x₃))) * (∑ x₄ : K × K, ψ (-(dotProd a x₄ + dotProd b (F x₄)))) := by
          have h_expand : starRingEnd ℂ (walsh ψ F a b) = ∑ x : K × K, ψ (-(dotProd a x + dotProd b (F x))) := by
            unfold walsh;
            simp +decide [ AddChar.starComp_apply ];
            refine' Finset.sum_congr rfl fun x _ => _;
            rw [ show -dotProd b ( F x ) + -dotProd a x = - ( dotProd a x + dotProd b ( F x ) ) by ring, AddChar.map_neg_eq_inv ];
            rw [ Complex.inv_def ];
            simp +decide [ Complex.normSq_eq_norm_sq, AddChar.map_add_eq_mul ];
          rw [ h_expand ] ; ring!;
        simp +decide only [h_expand, Finset.sum_mul _ _ _];
        simp +decide only [mul_sum _ _ _, sum_mul];
        refine' Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => Finset.sum_congr rfl fun x₃ _ => Finset.sum_congr rfl fun x₄ _ => _;
        simp +decide [ ← AddChar.map_add_eq_mul, dotProd ] ; ring;
      simp +decide only [h_fubini, sum_sigma'];
      refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.snd.fst, x.snd.snd.snd.fst, x.snd.snd.snd.snd.fst, x.snd.snd.snd.snd.snd, x.fst, x.snd.fst ⟩ ) _ _ _ _ <;> simp +decide;
      · grind;
      · rintro ⟨ a, b, c, d, e, f ⟩ ; exact ⟨ _, _, _, _, _, _, _, _, _, _, _, _, rfl ⟩ ;
    have h_sum_char : ∀ x₁ x₂ x₃ x₄ : K × K, ∑ a : K × K, ∑ b : K × K, ψ (dotProd a (x₁ - x₂ + x₃ - x₄)) * ψ (dotProd b (F x₁ - F x₂ + F x₃ - F x₄)) = if x₁ - x₂ + x₃ - x₄ = 0 ∧ F x₁ - F x₂ + F x₃ - F x₄ = 0 then (Fintype.card K : ℂ) ^ 4 else 0 := by
      intro x₁ x₂ x₃ x₄
      have h_sum_char : ∀ w : K × K, ∑ a : K × K, ψ (dotProd a w) = if w = 0 then (Fintype.card K : ℂ) ^ 2 else 0 := by
        convert APN.FlystelWalsh.sum_char_dotProd ψ hψ using 1;
      simp +decide only [← Finset.mul_sum _ _ _, h_sum_char, ← sum_mul];
      grind;
    rw [ h_fubini, Finset.sum_congr rfl fun x₁ hx₁ => Finset.sum_congr rfl fun x₂ hx₂ => Finset.sum_congr rfl fun x₃ hx₃ => Finset.sum_congr rfl fun x₄ hx₄ => h_sum_char x₁ x₂ x₃ x₄ ];
    simp +decide [ Finset.sum_ite, secondOrderCollisions ];
    simp +decide only [card_filter];
    simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_mul _ _ _, mul_comm];
    simp +decide only [mul_boole, ← sum_product', Finset.mul_sum _ _ _];
    rfl

end FlystelWalsh
end APN