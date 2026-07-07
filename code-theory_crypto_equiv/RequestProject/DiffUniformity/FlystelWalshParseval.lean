import Mathlib
import RequestProject.DiffUniformity.FlystelWalsh

/-!
# Parseval / Plancherel identity for the field-level Walsh transform

This module is the next step of the Flystel / AG track (`FLYSTEL_WALSH_ROADMAP.md`):
it adds the **Parseval (Plancherel) identity** for the field-level Walsh transform
`walsh ψ F a b = ∑_{x ∈ K²} ψ(⟨a,x⟩ + ⟨b,F x⟩)` introduced in
`RequestProject/DiffUniformity/FlystelWalsh.lean`.

Unlike the deep entries of Theorem 3.3, this identity is **unconditional**: it needs
no algebraic-geometry character-sum bound, only additive-character orthogonality.
For any function `F : K × K → K × K` over a finite field `K` (with `q = #K`) and any
nontrivial additive character `ψ`,

```
∑_{a, b ∈ K²} ‖W_F(ψ, a, b)‖² = q⁶.
```

This is the discrete Plancherel theorem for the two-dimensional Walsh transform: it
fixes the total "linear potential" of the spectrum and is the lower-bound companion
to the `(d − 1)·p` upper bound of `FlystelTheorem33.lean`.

## Main results

* `sum_char_dotProd` — two-dimensional additive-character orthogonality:
  `∑_{a ∈ K²} ψ(⟨a, w⟩) = q² · [w = 0]`.
* `walsh_parseval` — the Parseval identity `∑_{a,b} ‖W_F(ψ,a,b)‖² = q⁶`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-
**Two-dimensional additive-character orthogonality.** For a nontrivial additive
character `ψ` of a finite field `K`, summing `ψ(⟨a, w⟩)` over all `a ∈ K²` gives
`q²` when `w = 0` and `0` otherwise.
-/
theorem sum_char_dotProd (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (w : K × K) :
    ∑ a : K × K, ψ (dotProd a w) = if w = 0 then (Fintype.card K : ℂ) ^ 2 else 0 := by
  split_ifs with hw;
  · convert APN.FlystelWalsh.walsh_zero_zero ψ ( fun _ => w );
    unfold walsh dotProd; simp +decide [ hw ] ;
  · -- By Fintype.sum_prod_type, we can split the sum into a product of sums.
    have h_split : ∑ a : K × K, ψ (a.1 * w.1 + a.2 * w.2) = (∑ a1 : K, ψ (a1 * w.1)) * (∑ a2 : K, ψ (a2 * w.2)) := by
      rw [ Finset.sum_mul_sum ];
      rw [ ← Finset.sum_product' ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ AddChar.map_add_eq_mul ] ;
    -- Since $w \neq 0$, at least one of $w.1$ or $w.2$ is non-zero.
    by_cases hw1 : w.1 = 0;
    · have := AddChar.sum_mulShift ( w.2 ) ( AddChar.IsPrimitive.of_ne_one hψ ) ; simp_all +decide [ dotProd ] ;
      exact fun h => hw ( Prod.ext hw1 h );
    · have h_sum_zero : ∑ a1 : K, ψ (a1 * w.1) = 0 := by
        have h_sum_zero : ψ.IsPrimitive := by
          exact?;
        convert AddChar.sum_mulShift ( w.1 ) h_sum_zero using 1;
        simp +decide [ hw1 ];
      exact h_split.trans ( by rw [ h_sum_zero, MulZeroClass.zero_mul ] )

/-
**Parseval / Plancherel identity for the field-level Walsh transform.** For any
`F : K × K → K × K` over a finite field `K` (`q = #K`) and any nontrivial additive
character `ψ`, the sum of the squared moduli of the Walsh coefficients equals `q⁶`.
-/
theorem walsh_parseval (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : K × K → K × K) :
    ∑ a : K × K, ∑ b : K × K, Complex.normSq (walsh ψ F a b)
      = (Fintype.card K : ℝ) ^ 6 := by
  -- By the properties of the Walsh transform and the Parseval's identity for finite fields, we have:
  have h_parseval : ∑ a : K × K, ∑ b : K × K, (walsh ψ F a b) * (starRingEnd ℂ (walsh ψ F a b)) = (Fintype.card K : ℂ) ^ 6 := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ a : K × K, ∑ b : K × K, (walsh ψ F a b) * (starRingEnd ℂ (walsh ψ F a b)) = ∑ x : K × K, ∑ y : K × K, ∑ a : K × K, ∑ b : K × K, ψ (dotProd a x + dotProd b (F x)) * ψ (-dotProd a y - dotProd b (F y)) := by
      have h_fubini : ∀ a b : K × K, (walsh ψ F a b) * (starRingEnd ℂ (walsh ψ F a b)) = ∑ x : K × K, ∑ y : K × K, ψ (dotProd a x + dotProd b (F x)) * ψ (-dotProd a y - dotProd b (F y)) := by
        -- By definition of the Walsh transform, we can expand the product.
        intro a b
        simp [walsh];
        have h_conj : ∀ x : K × K, starRingEnd ℂ (ψ (dotProd a x + dotProd b (F x))) = ψ (-dotProd a x - dotProd b (F x)) := by
          intro x
          have h_conj : starRingEnd ℂ (ψ (dotProd a x + dotProd b (F x))) = ψ (-(dotProd a x + dotProd b (F x))) := by
            convert AddChar.starComp_apply ( show 0 < ringChar K from ?_ ) _ using 1;
            exact CharP.char_is_prime_or_zero K ( ringChar K ) |> Or.rec ( fun h => h.pos ) fun h => by have := FiniteField.card K ( ringChar K ) ; aesop;
          exact h_conj.trans ( by rw [ neg_add' ] );
        simp +decide only [h_conj, Finset.sum_mul _ _ _, mul_sum];
      simp +decide only [h_fubini];
      simp +decide only [← sum_product'];
      refine' Finset.sum_bij ( fun x _ => ( x.2.2.1, x.2.2.2, x.1, x.2.1 ) ) _ _ _ _ <;> simp +decide;
    -- By the properties of the character ψ, we can simplify the expression inside the sum.
    have h_simplify : ∀ x y : K × K, ∑ a : K × K, ∑ b : K × K, ψ (dotProd a x + dotProd b (F x)) * ψ (-dotProd a y - dotProd b (F y)) = (∑ a : K × K, ψ (dotProd a (x - y))) * (∑ b : K × K, ψ (dotProd b (F x - F y))) := by
      intro x y
      have h_simplify : ∀ a b : K × K, ψ (dotProd a x + dotProd b (F x)) * ψ (-dotProd a y - dotProd b (F y)) = ψ (dotProd a (x - y)) * ψ (dotProd b (F x - F y)) := by
        intro a b; rw [ ← AddChar.map_add_eq_mul ] ; rw [ ← AddChar.map_add_eq_mul ] ; simp +decide [ dotProd ] ; ring;
      simp +decide only [h_simplify, sum_mul_sum];
    -- By the properties of the character ψ, we know that $\sum_{a} \psi(a \cdot (x - y)) = q^2$ if $x = y$ and $0$ otherwise.
    have h_char : ∀ x y : K × K, ∑ a : K × K, ψ (dotProd a (x - y)) = if x = y then (Fintype.card K : ℂ) ^ 2 else 0 := by
      intro x y; split_ifs with hxy; simp +decide [ hxy ] ; ring;
      · simp +decide [ dotProd ];
        ring;
      · convert sum_char_dotProd ψ hψ ( x - y ) using 1 ; simp +decide [ hxy ];
        exact fun h => False.elim <| hxy <| sub_eq_zero.mp h;
    simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
    ring;
  convert h_parseval using 3 ; simp +decide [ Complex.normSq, Complex.mul_conj ];
  norm_cast

end FlystelWalsh
end APN