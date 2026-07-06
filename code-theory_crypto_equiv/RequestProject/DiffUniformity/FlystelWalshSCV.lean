import Mathlib
import RequestProject.DiffUniformity.FlystelWalshFourthMoment

/-!
# A Sidelnikov–Chabaud–Vaudenay style lower bound from the fourth moment

This module is the ZK-link (Track 2) next step: it combines the **second moment**
(Parseval, `walsh_parseval`: `∑ ‖W‖² = q⁶`) with the **fourth moment**
(`walsh_fourth_moment`: `∑ ‖W‖⁴ = q⁴·N`, with `N = #secondOrderCollisions F`) to
produce an **unconditional lower bound on the largest nonzero-mask Walsh
coefficient** — exactly the quantity that governs linear cryptanalysis, and the
field-level analogue of the Sidelnikov–Chabaud–Vaudenay nonlinearity bound.

The mechanism is the standard "moment" inequality: the fourth-power mass over the
nonzero masks cannot exceed the maximal coefficient times the second-power mass,
so

```
max_{(a,b) ≠ 0} ‖W_F(ψ, a, b)‖² ≥ (∑_{(a,b)≠0} ‖W‖⁴) / (∑_{(a,b)≠0} ‖W‖²)
                                = (q⁴·N − q⁸) / (q⁶ − q⁴).
```

The trivial coefficient `W_F(ψ,0,0) = q²` contributes `q⁴` to the second moment and
`q⁸` to the fourth, which is why it is subtracted out before averaging.

## Main results

* `exists_walsh_sq_ge_of_collisions` — there is a nonzero mask `(a, b)` with
  `(q⁶ − q⁴) · ‖W_F(ψ, a, b)‖² ≥ q⁴·N − q⁸`, i.e. the maximal nonzero Walsh
  square is at least `(q⁴·N − q⁸)/(q⁶ − q⁴)`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/--
**Lower bound on the largest nonzero-mask Walsh coefficient (SCV-style).**
For any `F : K × K → K × K` over a finite field `K` (`q = #K`) and any
nontrivial additive character `ψ`, some nonzero mask `(a, b)` satisfies

`(q⁶ − q⁴) · ‖W_F(ψ, a, b)‖² ≥ q⁴ · N − q⁸`,

where `N = #(secondOrderCollisions F)`. Equivalently, the maximal nonzero Walsh
square is `≥ (q⁴·N − q⁸)/(q⁶ − q⁴)`. This combines the Parseval second moment
with the fourth moment and isolates the trivial coefficient `q²`.
-/
theorem exists_walsh_sq_ge_of_collisions
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : K × K → K × K) :
    ∃ a b : K × K, (a, b) ≠ (0, 0) ∧
      ((Fintype.card K : ℝ) ^ 6 - (Fintype.card K : ℝ) ^ 4)
          * Complex.normSq (walsh ψ F a b)
        ≥ (Fintype.card K : ℝ) ^ 4 * (secondOrderCollisions F).card
            - (Fintype.card K : ℝ) ^ 8 := by
  obtain ⟨p₀, hp₀_mem, hp₀_max⟩ : ∃ p₀ : (K × K) × (K × K), p₀ ∈ Finset.univ.erase ((0, 0) : (K × K) × (K × K)) ∧ ∀ p ∈ Finset.univ.erase ((0, 0) : (K × K) × (K × K)), Complex.normSq (walsh ψ F p.1 p.2) ≤ Complex.normSq (walsh ψ F p₀.1 p₀.2) := by
    exact Finset.exists_max_image _ _ ⟨ ( ( 1, 0 ), ( 0, 0 ) ), by aesop ⟩;
  refine' ⟨ p₀.1, p₀.2, _, _ ⟩;
  · exact Finset.ne_of_mem_erase hp₀_mem;
  · have h_sum_le : ∑ p ∈ Finset.univ.erase ((0, 0) : (K × K) × (K × K)), Complex.normSq (walsh ψ F p.1 p.2) ^ 2 ≤ Complex.normSq (walsh ψ F p₀.1 p₀.2) * ∑ p ∈ Finset.univ.erase ((0, 0) : (K × K) × (K × K)), Complex.normSq (walsh ψ F p.1 p.2) := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun p hp => by nlinarith only [ hp₀_max p hp, Complex.normSq_nonneg ( walsh ψ F p.1 p.2 ) ] ;
    have := walsh_fourth_moment ψ hψ F; have := walsh_parseval ψ hψ F; simp_all +decide ;
    simp_all +decide [ ← Finset.sum_product', walsh_zero_zero ];
    convert h_sum_le using 1 ; ring

end FlystelWalsh
end APN