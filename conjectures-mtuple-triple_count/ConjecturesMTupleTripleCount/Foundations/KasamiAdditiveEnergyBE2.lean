import ConjecturesMTupleTripleCount.Foundations.KasamiAdditiveEnergy
import Mathlib

/-!
# Foundations, Layer B-E2 — the APN derivative image as a 2-to-1 set + energy bounds

This module implements the **second layer of the direct Fourier-analytic
sub-path for input (B)** laid out in `Docs/VanishFutureDirections.md` §7.

Layer BE1 (`KasamiAdditiveEnergy.lean`) reduced input **(B)** to the single
additive-energy value `16·E(Im Δf_a) = q³ + 2q²`.  This layer supplies the two
structural ingredients flagged for BE2:

1. **The derivative image is a 2-to-1 set: `|Im Δf_a| = q/2`.**  For an APN `f`
   and `a ≠ 0` every value of `Δf_a` is hit exactly twice
   (`MTuple.derivImage_card`), so the image has exactly half the field's size
   (`derivImage_card_eq_half`).

2. **The Cauchy–Schwarz energy lower bound `E(S) ≥ |S|⁴/q`.**  Writing the
   additive energy of `S` as `E(S) = ∑_z r_S(z)²` with the representation
   function `r_S(z) = #{(a,b) ∈ S² : a + b = z}` (`reprCount`,
   `additiveEnergy_eq_sum_sq_reprCount`) and `∑_z r_S(z) = |S|²`
   (`reprCount_sum`), Chebyshev/Cauchy–Schwarz
   (`Finset.sq_sum_le_card_mul_sum_sq`) gives
   `|S|⁴ = (∑_z r_S(z))² ≤ q·∑_z r_S(z)² = q·E(S)`
   (`card_pow_four_le_card_mul_additiveEnergy`).

Combining the two, for the derivative image of an APN function
(`|S| = q/2`) the energy bound becomes
`q³ ≤ 16·E(Im Δf_a)` (`additiveEnergy_derivImage_ge`): the lower half of the
target additive-energy value `16·E = q³ + 2q²` of input (B).  (The matching
*upper* bound `16·E ≤ q³ + 2q²`, i.e. the exact value, is the AB three-valued
spectrum computation of Layer BE3, the next layer of the sub-path; it is
deliberately not axiomatized here.)

We also record the second-moment companion of Layer BE1's fourth-moment
identity, the **Parseval identity for an indicator**
`∑_s (∑_{x∈S} χ(s·x))² = q·|S|` (`sum_sqPower_indicator_eq`), the `m = 2`
analogue of `sum_fourthPower_indicator_eq`.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3, §4.1 (additive energy, representation
function, the `E(A) ≥ |A|⁴/|A+A|` Cauchy–Schwarz bound); Carlet, Ch. 6 (APN
derivatives are 2-to-1).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. The derivative image as a 2-to-1 set -/

/-
**`|Im Δf_a| = q/2`.**  For an APN `f` and `a ≠ 0`, every value of `Δf_a` is
hit exactly twice, so its image has exactly half the field's cardinality:
`2·|Im Δf_a| = q`.
-/
theorem derivImage_card_eq_half (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    2 * (derivImage f a).card = Fintype.card F := by
  rcases n <;> simp_all +decide [ Nat.pow_succ' ];
  convert MTuple.derivImage_card ( Nat.succ ‹_› ) ( by simp +decide [ hcard, pow_succ' ] ) f hf a ha using 1

/-! ## 2. The representation function and the additive energy as a sum of squares -/

/-- **Representation function** of `S`: the number of ordered pairs `(a,b) ∈ S²`
with `a + b = z`. -/
noncomputable def reprCount (S : Finset F) (z : F) : ℕ :=
  (univ.filter (fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = z)).card

/-
The representation function sums to `|S|²` over all targets.
-/
omit [CharP F 2] in
theorem reprCount_sum (S : Finset F) :
    ∑ z : F, reprCount S z = S.card ^ 2 := by
  unfold reprCount; simp +decide [ pow_two ] ;
  rw [ ← Finset.card_product ];
  rw [ ← Finset.card_biUnion ] ; congr ; ext ; aesop;
  exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;

/-
**Additive energy as a sum of squares of the representation function.**
In characteristic `2`, `a + b + c + d = 0 ⟺ a + b = c + d`, so the additive
energy `E(S) = #{(a,b,c,d) ∈ S⁴ : a+b+c+d = 0}` decomposes by the common value
`z = a + b = c + d` as `E(S) = ∑_z r_S(z)²`.
-/
theorem additiveEnergy_eq_sum_sq_reprCount (S : Finset F) :
    additiveEnergy S = ∑ z : F, (reprCount S z) ^ 2 := by
  -- Let's rewrite the sum over the fiber in terms of the representation function.
  have h_fiber_sum : ∀ z : F, (Finset.univ.filter (fun y : Fin 4 → F => (∀ i, y i ∈ S) ∧ (∑ i, y i = 0) ∧ y 0 + y 1 = z)).card = (Finset.univ.filter (fun p : F × F => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = z)).card ^ 2 := by
    intro z
    have h_fiber : Finset.univ.filter (fun y : Fin 4 → F => (∀ i, y i ∈ S) ∧ (∑ i, y i = 0) ∧ y 0 + y 1 = z) = Finset.image (fun p : (F × F) × (F × F) => ![p.1.1, p.1.2, p.2.1, p.2.2]) (Finset.univ.filter (fun p : (F × F) × (F × F) => p.1.1 ∈ S ∧ p.1.2 ∈ S ∧ p.1.1 + p.1.2 = z ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S ∧ p.2.1 + p.2.2 = z)) := by
      ext y; simp [Fin.sum_univ_four] at *; (
      constructor <;> intro h
      all_goals generalize_proofs at *;
      · use y 0, y 1, y 2, y 3; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
        grind;
      · rcases h with ⟨ a, b, c, d, ⟨ ha, hb, hab, hc, hd, hcd ⟩, rfl ⟩ ; simp_all +decide [ Fin.forall_fin_succ ] ;
        grind)
    simp [h_fiber] at *; (
    rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    · rw [ sq, ← Finset.card_product ] ; congr ; ext ; aesop;
    · aesop);
  unfold additiveEnergy reprCount; simp +decide only [card_filter] ;
  convert Finset.sum_congr rfl fun z _ => congr_arg ( fun x : ℕ => x * 1 ) ( h_fiber_sum z ) using 1;
  any_goals exact Finset.univ;
  · simp +decide;
    rw [ ← Finset.card_biUnion ];
    · congr with x ; aesop;
    · exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
  · simp +decide

/-! ## 3. The Cauchy–Schwarz energy lower bound -/

/-
**`|S|⁴ ≤ q·E(S)`** (the additive-energy Cauchy–Schwarz / Chebyshev bound).
From `∑_z r_S(z) = |S|²` and `E(S) = ∑_z r_S(z)²`, Chebyshev's sum inequality
`(∑_z r_S(z))² ≤ q·∑_z r_S(z)²` gives `|S|⁴ ≤ q·E(S)`.
-/
theorem card_pow_four_le_card_mul_additiveEnergy (S : Finset F) :
    S.card ^ 4 ≤ Fintype.card F * additiveEnergy S := by
  have h_cauchy_schwarz : (∑ z : F, reprCount S z) ^ 2 ≤ (Fintype.card F) * (∑ z : F, (reprCount S z) ^ 2) := by
    have h_cauchy_schwarz : ∀ (s : Finset F) (f : F → ℕ), (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
      intro s f;
      have h_cauchy_schwarz : ∀ (s : Finset F) (f : F → ℝ), (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
        intro s f; have := Finset.sum_le_sum fun i ( hi : i ∈ s ) => pow_two_nonneg ( f i - ( ∑ j ∈ s, f j ) / s.card ) ; by_cases hs : s = ∅ <;> simp_all +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ;
        simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        nlinarith [ mul_div_cancel₀ ( ∑ i ∈ s, f i ) ( Nat.cast_ne_zero.mpr ( Finset.card_ne_zero_of_mem ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hs ) ) ) ) ];
      exact_mod_cast h_cauchy_schwarz s fun i => f i;
    simpa using h_cauchy_schwarz Finset.univ ( fun z => reprCount S z );
  convert h_cauchy_schwarz using 1 <;> push_cast [ reprCount_sum, additiveEnergy_eq_sum_sq_reprCount ] <;> ring_nf

/-! ## 4. The second-moment Parseval identity for an indicator -/

/-
**Parseval for an indicator** (the `m = 2` companion of
`sum_fourthPower_indicator_eq`): `∑_s (∑_{x∈S} χ(s·x))² = q·|S|`.  Expand the
square, collapse the character product to `χ(s·(x+y))`, swap sums and apply
orthogonality `χ_sum_dual`; in characteristic `2`, `x + y = 0 ⟺ x = y`, leaving
the diagonal of size `|S|`.
-/
theorem sum_sqPower_indicator_eq (S : Finset F) :
    ∑ s : F, (∑ x ∈ S, χ (s * x)) ^ 2 = (Fintype.card F : ℤ) * (S.card : ℤ) := by
  -- Expand the square and swap the order of summation.
  have h_expand : ∑ s : F, (∑ x ∈ S, χ (s * x)) ^ 2 = ∑ x ∈ S, ∑ y ∈ S, ∑ s : F, χ (s * (x + y)) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_add];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    simp +decide only [mul_comm, Finset.mul_sum _ _ _];
    exact fun x hx => Finset.sum_comm.trans ( Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun z hz => by rw [ ← WalshAB.χ_mul ] ; congr 1 ; ring );
  -- By orthogonality of characters, we know that $\sum_{s \in F} \chi(s \cdot (x + y)) = 0$ if $x + y \neq 0$.
  have h_ortho : ∀ x y : F, x + y ≠ 0 → ∑ s : F, χ (s * (x + y)) = 0 := by
    intro x y hxy;
    convert WalshAB.χ_sum_dual ( x + y ) using 1;
    rw [ if_neg hxy ];
  -- Since $x + y = 0$ if and only if $x = y$ in characteristic 2, we can simplify the sum.
  have h_simplify : ∀ x y : F, ∑ s : F, χ (s * (x + y)) = if x = y then (Fintype.card F : ℤ) else 0 := by
    intro x y; split_ifs with hxy <;> simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
    · simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
      exact WalshAB.χ_zero;
    · convert h_ortho x y _;
      grind;
  simp_all +decide [ mul_comm ]

/-! ## 5. The APN derivative-image energy lower bound (the BE2 conclusion) -/

/-
**`q³ ≤ 16·E(Im Δf_a)`.**  For an APN `f` and `a ≠ 0` with `|F| = 2ⁿ`,
combining `|Im Δf_a| = q/2` (`derivImage_card_eq_half`) with the Cauchy–Schwarz
bound `|S|⁴ ≤ q·E(S)` (`card_pow_four_le_card_mul_additiveEnergy`) gives the
lower half of input (B)'s target value `16·E = q³ + 2q²`.
-/
theorem additiveEnergy_derivImage_ge (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    Fintype.card F ^ 3 ≤ 16 * additiveEnergy (derivImage f a) := by
  -- By `derivImage_card_eq_half n hn hcard f hf a ha`, `2 * S.card = q`, hence `q = 2 * S.card`.
  have hq : (Fintype.card F) = 2 * (derivImage f a).card := by
    exact Eq.symm ( derivImage_card_eq_half n hn hcard f hf a ha );
  have := card_pow_four_le_card_mul_additiveEnergy ( derivImage f a );
  rw [ hq ] at this ⊢; nlinarith [ show 0 < Fintype.card F from Fintype.card_pos_iff.mpr ⟨ a ⟩ ] ;

end Vanish.Foundations