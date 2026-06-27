import ConjecturesMTupleTripleCount.Foundations.KasamiAdditiveEnergyBE2
import Mathlib

/-!
# Foundations, Layer BE3 — the AB additive-energy value (preliminaries)

This module implements the **third layer of the direct Fourier-analytic
sub-path for input (B)** laid out in `Docs/VanishFutureDirections.md` §7.

Layer BE1 (`KasamiAdditiveEnergy.lean`) reduced input **(B)** to the single
additive-energy value `16·E(Im Δf_a) = q³ + 2q²` via the collision-count route,
and supplied the *full-frequency* fourth-moment Fourier identity
`∑_s R(s)⁴ = 16·q·E(Im Δf_a)` (`crossCorr_fourthMoment_eq_energy`).  Layer BE2
(`KasamiAdditiveEnergyBE2.lean`) supplied the lower half `q³ ≤ 16·E(Im Δf_a)`
(`additiveEnergy_derivImage_ge`).

This layer assembles the **punctured** fourth-moment identity and reads off the
exact equivalence between the additive-energy value and input (B):

1. **The zero-frequency term.**  `R(0)⁴ = q⁴` (`autocorrScaled_zero_pow_four`),
   since `R(0) = ∑ₓ χ(0·Δf_a x) = q` (`MTuple.autocorrScaled_zero`).

2. **The punctured fourth moment** `∑_{s≠0} R(s)⁴ = 16·q·E(Im Δf_a) − q⁴`
   (`crossCorr_fourthMoment_punctured`): split the full moment of
   `crossCorr_fourthMoment_eq_energy` off the `s = 0` term.

3. **Input (B) as the additive-energy value, directly via Fourier**
   (`additiveEnergy_value_iff_fourthMoment`):
   `16·E(Im Δf_a) = q³ + 2q² ⟺ ∑_{s≠0} R(s)⁴ = 2·q³`.
   (Dividing the punctured identity `16qE − q⁴ = 2q³` by `q > 0` gives
   `16E = q³ + 2q²`.)  This is the **Fourier-analytic** counterpart of BE1's
   combinatorial `fourthMoment_eq_iff_additiveEnergy`: it routes input (B)
   through the additive energy without passing through the derivative
   collision-count, which is the entry point of the direct route.

Combining with BE2's lower bound `q³ ≤ 16·E`, the only remaining content of
input (B) is the **matching upper bound** `16·E(Im Δf_a) ≤ q³ + 2q²` — i.e. the
*exact* additive-energy value `E(Im Δf_a) = q³/16 + q²/8` for an AB function.

## Scope

This layer is sorry-free; it supplies the **punctured-moment reformulation** that
isolates input (B) as the single additive-energy value `16·E = q³ + 2q²`, and
combines with BE2's lower bound `q³ ≤ 16·E`.  The *deep core* of BE3 — the exact
AB additive-energy value `E(Im Δf_a) = q³/16 + q²/8` (equivalently the matching
upper bound `16·E ≤ q³ + 2q²`), which is the AB three-valued-spectrum computation
phrased on the derivative image — requires the MacWilliams / AB-spectrum input
that is **absent from Mathlib**; it is deliberately neither axiomatized nor
`sorry`-ed here, but documented as the open frontier of the sub-path (as the deep
cores of AK3 / AK4 are).

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3, §4.1 (additive energy, the fourth moment
of the Fourier transform); Carlet, Ch. 6 (AB functions and the Walsh spectrum).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The zero-frequency term -/

omit [DecidableEq F] in
/--
**`R(0)⁴ = q⁴`.**  The cross-correlation at the zero frequency is the field size
`R(0) = q` (`MTuple.autocorrScaled_zero`), so its fourth power is `q⁴`.
-/
theorem autocorrScaled_zero_pow_four (f : F → F) (a : F) :
    (autocorrScaled f 0 a) ^ 4 = (Fintype.card F : ℤ) ^ 4 := by
  rw [MTuple.autocorrScaled_zero]

/-! ## 2. The punctured fourth moment -/

/-
**The punctured fourth moment** `∑_{s≠0} R(s)⁴ = 16·q·E(Im Δf_a) − q⁴`.  Split
the full-frequency moment `∑_s R(s)⁴ = 16·q·E(Im Δf_a)`
(`crossCorr_fourthMoment_eq_energy`) off the `s = 0` term `R(0)⁴ = q⁴`.
-/
theorem crossCorr_fourthMoment_punctured (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
      = 16 * (Fintype.card F : ℤ) * (additiveEnergy (derivImage f a) : ℤ)
        - (Fintype.card F : ℤ) ^ 4 := by
  have := @Vanish.Foundations.crossCorr_fourthMoment_eq_energy F;
  rw [ ← this f hf a ha, ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), Vanish.Foundations.autocorrScaled_zero_pow_four f a ] ; ring

/-! ## 3. Input (B) as the additive-energy value (direct Fourier route) -/

/-
**Input (B) ⟺ the additive-energy value, via the punctured moment.**
`16·E(Im Δf_a) = q³ + 2q² ⟺ ∑_{s≠0} R(s)⁴ = 2·q³`.  Substituting the punctured
moment `∑_{s≠0} R(s)⁴ = 16·q·E − q⁴` and dividing by `q > 0`: the right side is
`16qE − q⁴ = 2q³ ⟺ 16qE = 2q³ + q⁴ ⟺ 16E = 2q² + q³`.  This is the
Fourier-analytic counterpart of BE1's `fourthMoment_eq_iff_additiveEnergy`.
-/
theorem additiveEnergy_value_iff_fourthMoment (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    (16 * (additiveEnergy (derivImage f a) : ℤ)
        = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
          = 2 * (Fintype.card F : ℤ) ^ 3) := by
  rw [ Vanish.Foundations.crossCorr_fourthMoment_punctured ];
  · constructor <;> intro h <;> nlinarith [ show 0 < ( Fintype.card F : ℤ ) by exact_mod_cast Fintype.card_pos ];
  · exact hf;
  · exact ha

end Vanish.Foundations