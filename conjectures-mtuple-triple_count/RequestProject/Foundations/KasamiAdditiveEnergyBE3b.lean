import RequestProject.Foundations.KasamiAdditiveEnergyBE3a
import Mathlib

/-!
# Foundations, Layer BE3.2 / BE3.3 — the off-diagonal counts via the APN second derivative

This module continues the **sub-sub-path of Layer BE3** laid out in
`Docs/VanishFutureDirections.md` §7.  Layer BE3.1
(`KasamiAdditiveEnergyBE3a.lean`) split the additive energy of the derivative
image into its diagonal and off-diagonal parts,

`E(S) = |S|² + offDiagEnergy S`,  `offDiagEnergy S = ∑_{z≠0} r_S(z)²`,

and reduced the remaining content of input **(B)** to the *off-diagonal value*
`16·offDiagEnergy(Im Δf_a) = q³ − 2q²`.

This module supplies the structural step **BE3.2** — re-expressing the
off-diagonal representation counts `r_S(z)` of the derivative image
`S = Im Δf_a` through the **APN second-derivative structure**, and the
elementary bookkeeping bounds (**BE3.3** reductions) that turn a bound on those
counts into a bound on `offDiagEnergy`.

## What is established (sorry-free)

1. **The off-diagonal mass.**  `∑_{z≠0} r_S(z) = |S|² − |S|`
   (`reprCount_sum_offDiag`) — split `∑_z r_S(z) = |S|²` (BE2's `reprCount_sum`)
   off its `z = 0` term `r_S(0) = |S|` (BE3.1's `reprCount_zero`).

2. **The 4-to-1 lift to the second derivative.**  For an APN `f` and `a ≠ 0`,
   each image value `Δf_a x` has exactly two preimages (`deriv_fiber_card`), so
   the map `(x,y) ↦ (Δf_a x, Δf_a y)` is **4-to-1** onto pairs of image values.
   Writing
   `derivPairCount f a z = #{(x,y) ∈ F² : Δf_a x + Δf_a y = z}`,
   this gives `4·r_S(z) = derivPairCount f a z`
   (`four_mul_reprCount_eq_derivPairCount`) — the count of additive pairs in the
   image is, up to the forced factor `4`, the count of pairs of *arguments*
   whose derivative values sum to `z`.

3. **The second-derivative reindexing.**  Substituting `y = x + w`,
   `derivPairCount f a z = ∑_w #{x : Δf_a(x+w) + Δf_a x = z}`
   (`derivPairCount_eq_secondDeriv`).  The inner count is the fiber of the
   **second-order derivative** `Δ_w Δf_a (x) = Δf_a(x+w) + Δf_a x` — the
   quantity whose distribution is the AB three-valued-spectrum input.  The two
   forced values `w ∈ {0, a}` contribute only to `z = 0`
   (`secondDeriv_trivial_w`), the precise sense in which `z ≠ 0` sees only
   *genuine* second derivatives.

4. **The energy bound from a count bound (BE3.3 reduction).**  Squares are
   controlled by the maximum off-diagonal count:
   `offDiagEnergy S ≤ M·(|S|² − |S|)` whenever `r_S(z) ≤ M` for all `z ≠ 0`
   (`offDiagEnergy_le_max_mul_mass`).  This is the bookkeeping that converts
   BE3.2's structural bound on the off-diagonal counts into the off-diagonal
   *value* of BE3.3.

## Scope

This layer is sorry-free.  It supplies the second-derivative reformulation of the
off-diagonal counts and the bound bookkeeping.  The *evaluation*
`16·offDiagEnergy(Im Δf_a) = q³ − 2q²` itself requires the exact distribution of
the second-order derivatives — the **AB three-valued spectrum**, which is **not**
implied by APN alone (it fails for APN-but-not-AB functions) and is absent from
Mathlib.  That deep core is documented as the open frontier, deliberately
neither axiomatized nor `sorry`-ed.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (representation function, additive
energy); Carlet, Ch. 6 (APN/AB functions, second-order derivatives).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The off-diagonal representation mass -/

/-
**The off-diagonal mass** `∑_{z≠0} r_S(z) = |S|² − |S|`.  Split the total mass
`∑_z r_S(z) = |S|²` (`reprCount_sum`) off the diagonal term `r_S(0) = |S|`
(`reprCount_zero`).
-/
theorem reprCount_sum_offDiag (S : Finset F) :
    ∑ z ∈ univ.erase (0 : F), reprCount S z = S.card ^ 2 - S.card := by
  rw [ eq_tsub_iff_add_eq_of_le ];
  · convert Vanish.Foundations.reprCount_sum S using 1;
    rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), Vanish.Foundations.reprCount_zero ];
  · nlinarith

/-! ## 2. The second-derivative collision count -/

/-- **Second-derivative collision count**: the number of ordered argument pairs
`(x,y)` whose derivative values sum to `z`, `#{(x,y) ∈ F² : Δf_a x + Δf_a y = z}`. -/
noncomputable def derivPairCount (f : F → F) (a z : F) : ℕ :=
  (univ.filter (fun p : F × F => deriv f a p.1 + deriv f a p.2 = z)).card

/-
**The 4-to-1 lift.**  For an APN `f`, `a ≠ 0`, every image value has exactly two
preimages (`deriv_fiber_card`), so `(x,y) ↦ (Δf_a x, Δf_a y)` is `4`-to-`1` onto
pairs of image values: `4·r_S(z) = derivPairCount f a z`.
-/
theorem four_mul_reprCount_eq_derivPairCount (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) (z : F) :
    4 * reprCount (derivImage f a) z = derivPairCount f a z := by
  convert congr_arg Finset.card ?_ using 1;
  rotate_left;
  exact Finset.biUnion ( Finset.filter ( fun p : F × F => p.1 ∈ derivImage f a ∧ p.2 ∈ derivImage f a ∧ p.1 + p.2 = z ) ( Finset.univ : Finset ( F × F ) ) ) fun p => Finset.product ( Finset.filter ( fun x => MTuple.deriv f a x = p.1 ) Finset.univ ) ( Finset.filter ( fun y => MTuple.deriv f a y = p.2 ) Finset.univ );
  · ext ⟨x, y⟩; simp [Finset.mem_biUnion, Finset.mem_filter];
    exact ⟨ fun h => h.2.2, fun h => ⟨ Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), h ⟩ ⟩;
  · rw [ Finset.card_biUnion ];
    · have h_card : ∀ p : F × F, p.1 ∈ derivImage f a → p.2 ∈ derivImage f a → (Finset.filter (fun x => MTuple.deriv f a x = p.1) Finset.univ).card = 2 ∧ (Finset.filter (fun y => MTuple.deriv f a y = p.2) Finset.univ).card = 2 := by
        exact fun p hp₁ hp₂ => ⟨ MTuple.deriv_fiber_card f hf a ha p.1 hp₁, MTuple.deriv_fiber_card f hf a ha p.2 hp₂ ⟩;
      rw [ Finset.sum_congr rfl fun p hp => by erw [ Finset.card_product ] ];
      rw [ Finset.sum_congr rfl fun p hp => by rw [ h_card p ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hp |>.2.2.1 ) |>.1, h_card p ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hp |>.2.2.1 ) |>.2 ] ] ; simp +decide [ mul_comm, reprCount ];
    · intro p hp q hq hpq; simp_all +decide [ Finset.disjoint_left, Finset.mem_product ] ;
      grind

/-
**The second-derivative reindexing.**  Substituting `y = x + w`, the collision
count is the total fiber count of the second-order derivative
`Δ_w Δf_a (x) = Δf_a(x+w) + Δf_a x`:
`derivPairCount f a z = ∑_w #{x : Δf_a(x+w) + Δf_a x = z}`.
-/
theorem derivPairCount_eq_secondDeriv (f : F → F) (a z : F) :
    derivPairCount f a z
      = ∑ w : F, (univ.filter (fun x : F => deriv f a (x + w) + deriv f a x = z)).card := by
  simp +decide only [derivPairCount, card_filter];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( x.1 + x.2, x.2 ) ) _ _ _ _ <;> simp +decide;
  · aesop;
  · exact fun a b => ⟨ a - b, sub_add_cancel a b ⟩;
  · grind

/-
**The trivial second derivatives.**  For the two forced shifts `w ∈ {0, a}` the
second-order derivative `Δ_w Δf_a` is identically `0` (the derivative is
`a`-periodic), so its fiber over `z ≠ 0` is empty: those shifts contribute only
to `z = 0`.
-/
theorem secondDeriv_trivial_w (f : F → F) (a : F) {z : F} (hz : z ≠ 0) :
    (univ.filter (fun x : F => deriv f a (x + 0) + deriv f a x = z)).card = 0
      ∧ (univ.filter (fun x : F => deriv f a (x + a) + deriv f a x = z)).card = 0 := by
  constructor <;> rw [ Finset.card_eq_zero ];
  · ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_zero, Finset.notMem_empty, iff_false];
    rw [ ← two_smul F, CharTwo.two_eq_zero, zero_smul ] ; aesop;
  · ext x; simp [MTuple.deriv_shift];
    rw [ ← two_smul F, CharTwo.two_eq_zero, zero_smul ] ; aesop

/-! ## 3. The energy bound from a count bound (BE3.3 reduction) -/

/-
**Energy from a uniform count bound.**  If every off-diagonal representation
count is `≤ M`, then `offDiagEnergy S = ∑_{z≠0} r_S(z)² ≤ M·∑_{z≠0} r_S(z) =
M·(|S|² − |S|)`.  This is the bookkeeping that turns BE3.2's structural bound on
the off-diagonal counts into the off-diagonal energy value of BE3.3.
-/
theorem offDiagEnergy_le_max_mul_mass (S : Finset F) (M : ℕ)
    (hM : ∀ z ∈ univ.erase (0 : F), reprCount S z ≤ M) :
    offDiagEnergy S ≤ M * (S.card ^ 2 - S.card) := by
  convert Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left ( hM z hz ) ( Nat.zero_le ( reprCount S z ) ) using 1;
  · exact Finset.sum_congr rfl fun _ _ => pow_two _;
  · rw [ ← Finset.sum_mul _ _ _, ← reprCount_sum_offDiag ];
    ring

end Vanish.Foundations