import ConjecturesMTupleTripleCount.Foundations.KasamiAdditiveEnergyBE3
import Mathlib

/-!
# Foundations, Layer BE3.1 — the off-diagonal additive energy (first sub-sub-layer)

This module opens the **sub-sub-path of Layer BE3** laid out in
`Docs/VanishFutureDirections.md` §7.  Layer BE3
(`KasamiAdditiveEnergyBE3.lean`) reduced the remaining content of input **(B)**
to the single **upper bound** `16·E(Im Δf_a) ≤ q³ + 2q²` (equivalently, with
BE2's matching lower bound, the *exact* AB additive-energy value
`E(Im Δf_a) = q³/16 + q²/8`).  Following the program note, that upper bound is
*not* a one-shot proof: it is the statement that the derivative image has **no
"extra" additive quadruples** beyond the forced (diagonal / transposition) ones.
This module establishes the **first step** of that refined chain — the
diagonal/off-diagonal decomposition of the additive energy that *isolates* the
extra quadruples as a single quantity, the **off-diagonal energy**.

## The decomposition

Recall (Layer BE2) the representation function
`r_S(z) = #{(a,b) ∈ S² : a+b = z}` and `E(S) = ∑_z r_S(z)²`
(`additiveEnergy_eq_sum_sq_reprCount`).  In characteristic `2`:

1. **The diagonal term.**  `r_S(0) = #{(a,b) : a+b = 0} = #{(a,a)} = |S|`
   (`reprCount_zero`), so the `z = 0` summand of `E(S)` is `|S|²`.

2. **The off-diagonal terms are even.**  For `z ≠ 0` the involution
   `(a,b) ↦ (b,a)` on `{(a,b) : a+b = z}` is fixed-point-free (a fixed point
   would force `a = b`, i.e. `z = 0`), so `r_S(z)` is **even**
   (`reprCount_even_of_ne_zero`).  This is the precise sense in which the
   off-diagonal pairs come in *forced transpositions*.

3. **The split.**  Collecting the `z ≠ 0` summands into the **off-diagonal
   energy** `offDiagEnergy S = ∑_{z≠0} r_S(z)²` gives
   `E(S) = |S|² + offDiagEnergy S` (`additiveEnergy_eq_card_sq_add_offDiagEnergy`).

4. **The target, rephrased.**  For the APN derivative image `|Im Δf_a| = q/2`
   (BE2), `16·|S|² = 4q²`, so the exact AB value `16·E = q³ + 2q²` is equivalent
   to the **off-diagonal value** `16·offDiagEnergy(Im Δf_a) = q³ − 2q²`
   (`additiveEnergy_value_iff_offDiagEnergy`).  This pins the remaining deep core
   of input (B) entirely on the off-diagonal energy — the count of genuine
   additive quadruples — which is what the next sub-sub-layer (the AB
   three-valued-spectrum constraint on `Im Δf_a`) must evaluate.

## Scope

This layer is sorry-free.  It supplies the diagonal/off-diagonal **decomposition**
and the off-diagonal reformulation of input (B)'s upper bound; the *evaluation*
of `offDiagEnergy(Im Δf_a)` (the AB three-valued-spectrum input, absent from
Mathlib) is the open deep core, deliberately neither axiomatized nor `sorry`-ed.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3 (additive energy, representation
function, diagonal/off-diagonal split); Carlet, Ch. 6 (AB functions).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The diagonal representation count -/

/-
**`r_S(0) = |S|`.**  In characteristic `2`, `a + b = 0 ⟺ a = b`, so the only
pairs `(a,b) ∈ S²` with `a + b = 0` are the diagonal pairs `(a,a)`.
-/
theorem reprCount_zero (S : Finset F) : reprCount S 0 = S.card := by
  refine' Finset.card_bij ( fun x _ => x.1 ) _ _ _ <;> simp +contextual; all_goals grind

/-! ## 2. The off-diagonal counts are even -/

/-
**The off-diagonal representation counts are even.**  For `z ≠ 0` the
transposition `(a,b) ↦ (b,a)` is a fixed-point-free involution of
`{(a,b) ∈ S² : a+b = z}` (a fixed point would force `a = b`, hence `z = 0`), so
`r_S(z)` is even.
-/
theorem reprCount_even_of_ne_zero (S : Finset F) {z : F} (hz : z ≠ 0) :
    Even (reprCount S z) := by
  -- The involution `(a,b) ↦ (b,a)` pairs up elements, so the cardinality must be even.
  have h_inv : ∃ T : Finset (F × F), (univ.filter (fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = z)) = T ∧ ∀ p ∈ T, (p.2, p.1) ∈ T ∧ p.1 ≠ p.2 := by
    grind;
  obtain ⟨ T, hT₁, hT₂ ⟩ := h_inv;
  -- Since T is paired up, we can partition it into pairs.
  have h_partition : ∃ P : Finset (Finset (F × F)), (∀ p ∈ P, p.card = 2) ∧ (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) ∧ T = Finset.biUnion P id := by
    refine' ⟨ Finset.image ( fun p => { p, ( p.2, p.1 ) } ) T, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind;
    · grind;
    · ext ⟨a, b⟩; simp;
      grind +splitImp;
  obtain ⟨ P, hP₁, hP₂, hP₃ ⟩ := h_partition; rw [ show reprCount S z = T.card from ?_ ] ; rw [ hP₃, Finset.card_biUnion ] ; simp_all +decide [ parity_simps ] ;
  · exact fun p hp q hq hpq => hP₂ p hp q hq hpq;
  · exact congr_arg Finset.card ( by ext; aesop )

/-! ## 3. The off-diagonal energy and the decomposition -/

/-- **Off-diagonal additive energy**: the contribution to `E(S) = ∑_z r_S(z)²`
of the nonzero targets `z ≠ 0`. -/
noncomputable def offDiagEnergy (S : Finset F) : ℕ :=
  ∑ z ∈ univ.erase (0 : F), (reprCount S z) ^ 2

/-
**The diagonal/off-diagonal decomposition** `E(S) = |S|² + offDiagEnergy S`.
Split `E(S) = ∑_z r_S(z)²` off its `z = 0` term `r_S(0)² = |S|²`.
-/
theorem additiveEnergy_eq_card_sq_add_offDiagEnergy (S : Finset F) :
    additiveEnergy S = S.card ^ 2 + offDiagEnergy S := by
  rw [ add_comm, additiveEnergy_eq_sum_sq_reprCount ];
  unfold offDiagEnergy;
  rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), add_comm ];
  rw [ add_comm, reprCount_zero ]

/-! ## 4. The off-diagonal reformulation of input (B)'s upper bound -/

/-
**Input (B)'s exact value, phrased on the off-diagonal energy.**  For an APN
`f`, `a ≠ 0`, and `|F| = 2ⁿ` (so `|Im Δf_a| = q/2`, BE2), the exact AB
additive-energy value `16·E(Im Δf_a) = q³ + 2q²` is equivalent to the
off-diagonal value `16·offDiagEnergy(Im Δf_a) = q³ − 2q²`.
-/
theorem additiveEnergy_value_iff_offDiagEnergy (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    (16 * (additiveEnergy (derivImage f a) : ℤ)
        = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2)
      ↔ (16 * (offDiagEnergy (derivImage f a) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 - 2 * (Fintype.card F : ℤ) ^ 2) := by
  have := derivImage_card_eq_half n hn hcard f hf a ha;
  rw [ Vanish.Foundations.additiveEnergy_eq_card_sq_add_offDiagEnergy ] ; push_cast [ ← this ];
  constructor <;> intro h <;> linarith

end Vanish.Foundations