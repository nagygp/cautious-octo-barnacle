import RequestProject.Foundations.KasamiGoldCovering
import RequestProject.Foundations.KasamiEq12Average
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-3: the GF(4)-coset average (`h12`)

This module is the **third from-scratch foundational module of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), building on DD-fp-2
(`KasamiGoldCovering.lean`, the 3-to-1 covering `goldPow_fiber_card`) and the
averaging substrate `KasamiEq12Average.lean`.

This is the core **DD-fp-3**: equation (12) as a **GF(4)-coset average of Gold
Gauss sums**.  The literal `1/3` weight comes from the substitution map
`u ↦ u^{2^k+1}` being a 3-to-1 covering of its image (DD-fp-2): summing a function
of `u^{2^k+1}` over `GF(2ⁿ)ˣ` triple-counts the image,

```
   ∑_{u ∈ GF(2ⁿ)ˣ} φ(u^{2^k+1}) = 3 · ∑_{y ∈ image} φ(y)      (goldPow_sum_threeToOne)
```

— the substitution-side analogue of `cube_sum_threeToOne`.  Together with the
GF(4)* scalar-action averaging `gf4_scalar_action_sum`
(`∑_{μ ∈ GF(4)*} ∑_x φ(μ·x) = 3 · ∑_x φ(x)`) these are the two summation
mechanisms that produce the three-term, `1/3`-weighted coset average of equation
(12).

Combined with the substitution realization linking the Kasami cross-correlation
character sum to the Gold-form character sums over the image (carried as the
hypothesis `h12`, the irreducible finite-field substitution core), the
equation-(12) value `3·W` is exhibited as the GF(4)-coset average of the auxiliary
Gold Gauss sums, each of which is `0` or `±2^{(n+r)/2}`
(`three_mul_kasamiWalsh_terms_spectrum`, DD-fp-3's downstream consumer).

## Results

* `goldPow_sum_threeToOne` — the substitution-side `1/3`: a sum of `φ ∘ (·^{2^k+1})`
  over `GF(2ⁿ)ˣ` triple-counts its image, when the map is 3-to-1
  (`gcd(2^k+1, q−1) = 3`, `n` even).

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite-group summation
algebra (the 3-to-1 covering of DD-fp-2 turned into a summation identity); the
trace-level substitution `x = u^{2^k+1}` identifying the Kasami character sum with
the Gold-form character sums — equation (12) itself — is the deep core `h12`,
carried as a named hypothesis (`KasamiEq12Average.three_mul_kasamiWalsh_terms_spectrum`).

## Sources

Dillon–Dobbertin (FFA 2004), §7 (eq. (12)) and Appendix A.4; Lidl–Niederreiter,
*Finite Fields*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**The substitution-side `1/3` (the 3-to-1 summation identity).**  For `n`
even and `gcd(2^k+1, q−1) = 3` (so `u ↦ u^{2^k+1}` is 3-to-1 onto its image,
`goldPow_fiber_card`), summing `φ ∘ (·^{2^k+1})` over `GF(2ⁿ)ˣ` triple-counts the
image: `∑_u φ(u^{2^k+1}) = 3 · ∑_{y ∈ image} φ(y)`.  This is the substitution-side
analogue of `cube_sum_threeToOne`, and produces the literal `1/3` of equation (12).
-/
theorem goldPow_sum_threeToOne {n k : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (hgcd : Nat.gcd (2 ^ k + 1) (Fintype.card Fˣ) = 3) (φ : Fˣ → ℤ) :
    ∑ u : Fˣ, φ (u ^ (2 ^ k + 1))
      = 3 * ∑ y ∈ Finset.image (fun u : Fˣ => u ^ (2 ^ k + 1)) univ, φ y := by
  rw [ Finset.mul_sum, Finset.sum_image' ];
  intro i hi;
  rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2 ] ];
  simp +decide [ goldPow_fiber_card hcard hn hgcd ]

end Vanish.Foundations