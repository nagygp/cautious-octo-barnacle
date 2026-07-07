import Mathlib
import RequestProject.DiffUniformity.FlystelWalshFourthMoment

/-!
# Spectral flatness bounds the second-order collision count

This module is the ZK-link (Track 2) next step: it is the **converse direction** to
the Sidelnikov–Chabaud–Vaudenay lower bound of `FlystelWalshSCV.lean`. Whereas the
SCV bound turns many collisions into a large Walsh coefficient, here a **flat**
Walsh spectrum (small linearity — the design goal for ZK-friendly S-boxes) forces
**few** second-order collisions.

The mechanism is again the two moments: writing `‖W‖⁴ = ‖W‖² · ‖W‖²` and bounding
one factor by the assumed uniform bound `M` over the nonzero masks,

```
q⁴·N − q⁸ = ∑_{(a,b)≠0} ‖W‖⁴ ≤ M · ∑_{(a,b)≠0} ‖W‖² = M · (q⁶ − q⁴),
```

so `q⁴·N ≤ q⁸ + M·(q⁶ − q⁴)`. The trivial coefficient `W_F(ψ,0,0) = q²` contributes
`q⁴` to the second moment and `q⁸` to the fourth and is isolated before bounding.

## Main results

* `secondOrderCollisions_card_le_of_walsh_sq_le` — if every nonzero-mask Walsh
  square is `≤ M`, then `q⁴·N ≤ q⁸ + M·(q⁶ − q⁴)`.
-/

open Finset BigOperators

namespace APN
namespace FlystelWalsh

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-
**Flat spectrum bounds second-order collisions.** For any `F : K × K → K × K` over
a finite field `K` (`q = #K`), any nontrivial additive character `ψ`, and any bound
`M` with `Complex.normSq (walsh ψ F a b) ≤ M` for every nonzero mask
`(a, b) ≠ (0, 0)`, the number `N = #(secondOrderCollisions F)` satisfies

`q⁴ · N ≤ q⁸ + M · (q⁶ − q⁴)`.

This is the converse to the SCV lower bound: a flat Walsh spectrum forces few
second-order collisions.
-/
theorem secondOrderCollisions_card_le_of_walsh_sq_le
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : K × K → K × K) (M : ℝ)
    (hM : ∀ a b : K × K, (a, b) ≠ (0, 0) → Complex.normSq (walsh ψ F a b) ≤ M) :
    (Fintype.card K : ℝ) ^ 4 * (secondOrderCollisions F).card
      ≤ (Fintype.card K : ℝ) ^ 8
        + M * ((Fintype.card K : ℝ) ^ 6 - (Fintype.card K : ℝ) ^ 4) := by
  -- Summing the inequality over all nonzero masks $t \ne (0,0)$.
  have h_sum : ∑ t ∈ Finset.univ.erase (0, 0), Complex.normSq (walsh ψ F t.fst t.snd) ^ 2 ≤
      ∑ t ∈ Finset.univ.erase (0, 0), M * Complex.normSq (walsh ψ F t.fst t.snd) := by
        exact Finset.sum_le_sum fun x hx => by nlinarith only [ hM x.1 x.2 ( Finset.ne_of_mem_erase hx ), Complex.normSq_nonneg ( walsh ψ F x.1 x.2 ) ] ;
  have := walsh_fourth_moment ψ hψ F; have := walsh_parseval ψ hψ F; simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ;
  simp_all +decide [ ← Finset.sum_product', walsh_zero_zero ];
  convert h_sum using 1 ; ring

end FlystelWalsh
end APN