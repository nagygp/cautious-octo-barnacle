import Mathlib
import RequestProject.DiffUniformity.FlystelWalshParseval

/-!
# Linear potential of an S-box and an unconditional Walsh lower bound (ZK link)

This module is the next step of the ZK / S-box track: it turns the unconditional
Parseval identity `walsh_parseval` (`∑_{a,b} ‖W_F(ψ,a,b)‖² = q⁶`) into a concrete
**lower bound** on the largest nonzero-mask Walsh coefficient of any S-box
`F : K × K → K × K` over a finite field `K`.

Linear cryptanalysis is governed by the *largest* absolute Walsh coefficient over
nonzero masks. Theorem 3.3 (`FlystelTheorem33.lean`) gives the deep `(d − 1)·p`
*upper* bound for the Flystel. Parseval supplies the matching *unconditional lower*
bound, valid for every S-box: the spectral mass `q⁶` cannot all sit on the trivial
coefficient `W_F(ψ,0,0) = q²`, so some nonzero mask carries at least the average of
the remaining mass. Concretely there is a mask `(a, b) ≠ 0` with

```
‖W_F(ψ, a, b)‖² ≥ q⁴ / (q² + 1).
```

For a permutation `F` (the ZK / Anemoi setting) the "axis" coefficients
`W_F(ψ, a, 0)` (`a ≠ 0`) and `W_F(ψ, 0, b)` (`b ≠ 0`) all vanish
(`walsh_zero_output_mask`, and `walsh_eq_zero_of_b_zero` from `FlystelWalsh.lean`),
so this entire linear potential is carried by the genuine two-sided approximations.

## Main results

* `walsh_zero_output_mask` — for a permutation `F` and a nonzero output mask `b`,
  `W_F(ψ, 0, b) = 0`.
* `exists_walsh_sq_ge` — the unconditional lower bound: some nonzero mask `(a, b)`
  satisfies `(q² + 1)·‖W_F(ψ,a,b)‖² ≥ q⁴`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-
**Vanishing of axis coefficients for a permutation.** If `F` is a bijection of
`K × K` and the output mask `b` is nonzero, then `W_F(ψ, 0, b) = 0`: the component
`x ↦ ⟨b, F x⟩` is balanced because `F` is a permutation.
-/
theorem walsh_zero_output_mask (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : K × K → K × K) (hF : Function.Bijective F) (b : K × K) (hb : b ≠ 0) :
    walsh ψ F 0 b = 0 := by
  convert sum_char_dotProd ψ hψ b using 1;
  · convert Equiv.sum_comp ( Equiv.ofBijective F hF ) ( fun x => ψ ( dotProd b x ) ) using 1;
    · unfold walsh dotProd; aesop;
    · exact Finset.sum_congr rfl fun _ _ => by unfold dotProd; ring;
  · aesop

/-
**Unconditional Walsh lower bound from Parseval.** For any `F : K × K → K × K`
over a finite field `K` (`q = #K ≥ 2`) and any nontrivial additive character `ψ`,
there is a nonzero mask `(a, b)` whose squared Walsh coefficient is at least the
average `q⁴ / (q² + 1)` of the non-trivial spectral mass; in cleared form,
`(q² + 1)·‖W_F(ψ,a,b)‖² ≥ q⁴`.
-/
theorem exists_walsh_sq_ge (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : K × K → K × K)
    (hcard : 2 ≤ Fintype.card K) :
    ∃ a b : K × K, (a, b) ≠ (0, 0) ∧
      (Fintype.card K : ℝ) ^ 4
        ≤ ((Fintype.card K : ℝ) ^ 2 + 1) * Complex.normSq (walsh ψ F a b) := by
  have h_avg : ∑ p ∈ Finset.univ.erase (0, 0), Complex.normSq (walsh ψ F p.1 p.2) = (Fintype.card K : ℝ) ^ 6 - (Fintype.card K : ℝ) ^ 4 := by
    convert congr_arg ( fun x : ℝ => x - Complex.normSq ( walsh ψ F 0 0 ) ) ( FlystelWalsh.walsh_parseval ψ hψ F ) using 1;
    · simp +decide [ Fintype.sum_prod_type ];
    · rw [ FlystelWalsh.walsh_zero_zero ] ; norm_cast;
      norm_num [ Complex.normSq, sq ];
      ring;
  contrapose! h_avg;
  refine' ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty _ fun p hp => _ ) _ );
  use fun p => ( Fintype.card K : ℝ ) ^ 4 / ( Fintype.card K ^ 2 + 1 );
  · exact Finset.card_pos.mp ( by simp +decide [ Finset.card_univ, hcard ] ; nlinarith );
  · rw [ lt_div_iff₀ ] <;> first | positivity | linarith [ h_avg p.1 p.2 ( by aesop ) ] ;
  · simp +decide [ Finset.card_univ, pow_succ' ];
    rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ show ( Fintype.card K : ℝ ) ≥ 2 by norm_cast, pow_pos ( show ( Fintype.card K : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( Fintype.card K : ℝ ) > 0 by positivity ) 4, pow_pos ( show ( Fintype.card K : ℝ ) > 0 by positivity ) 5, pow_pos ( show ( Fintype.card K : ℝ ) > 0 by positivity ) 6 ]

end FlystelWalsh
end APN