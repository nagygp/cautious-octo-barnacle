import ConjecturesMTupleTripleCount.Foundations.KasamiPlessMoments
import ConjecturesMTupleTripleCount.Foundations.KasamiCrossCorrelationGeneralK
import ConjecturesMTupleTripleCount.Core.KasamiAB
import Mathlib

/-!
# Foundations, Layer B-E1 — additive energy / fourth-moment Fourier identity ⟹ input (B)

This module implements the **first layer of the direct Fourier-analytic
sub-path for input (B)** laid out in `Docs/VanishFutureDirections.md` §6.

Input **(B)** is the nonzero-frequency fourth moment
`∑_{s≠0} R(s)⁴ = 2·q³` of the Kasami cross-correlation
`R(s) = autocorrScaled f s a = ∑_x χ(s·Δf_a x)`.  Layer A4
(`KasamiPlessMoments.lean`) already reduced it to the derivative 4-collision
count `preCount 4 f a 1 = q³ + 2q²`.  This module performs the next reduction:
it rewrites that collision count as the **additive energy** of the image of the
derivative, `E(Im Δf_a)`, via the standard Fourier identity for the fourth
moment of the Fourier transform of an indicator function (Tao–Vu, *Additive
Combinatorics*, §4).

## The fourth-moment / additive-energy identity

For any subset `S ⊆ F` (here `F = GF(2ⁿ)`), writing `𝟙̂_S(s) = ∑_{x∈S} χ(s·x)`
for the (real, `±`-integer-valued) Fourier transform of the indicator of `S`,
the classical orthogonality computation gives
```
  ∑_s 𝟙̂_S(s)⁴ = q · E(S),     E(S) := #{(a,b,c,d) ∈ S⁴ : a+b+c+d = 0}.
```
(`sum_fourthPower_indicator_eq`).  In characteristic 2, `a+b+c+d = 0` is the same
as `a+b = c+d`, so `E(S)` is exactly the additive energy of `S`.

## Connection to the cross-correlation and to input (B)

Since `R(s) = 2·𝟙̂_{Im Δf_a}(s)` (`crossCorr_eq_two_mul_image`, APN),
```
  ∑_s R(s)⁴ = 16·q·E(Im Δf_a)                 (crossCorr_fourthMoment_eq_energy)
```
and the derivative 4-collision count is `preCount 4 = 16·E(Im Δf_a)`
(`imgCount_four_eq_additiveEnergy` together with `preCount_eq`).  Hence input
**(B)** is the **single additive-energy value**
```
  16·E(Im Δf_a) = q³ + 2q²                     (fourthMoment_eq_iff_additiveEnergy)
```
i.e. `E(Im Δf_a) = q³/16 + q²/8`.  This isolates the remaining open input to the
additive energy of the derivative image of an AB function — a purely additive-
combinatorial quantity, the entry point of the direct Fourier-analytic route.

## Scope

This layer is sorry-free and supplies the **reformulation** of (B) as an additive
energy.  The *value* of that energy (the AB additive-energy computation that
discharges `hfourth`) is the next layer of the sub-path (BE2/BE3 in §6); it is
deliberately not axiomatized.

## Sources

Tao–Vu, *Additive Combinatorics*, §2.3, §4.1 (additive energy and the fourth
moment of the Fourier transform); Carlet, Ch. 6 (AB functions and the Walsh
spectrum).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Additive energy -/

/-- **Additive energy** (fourth-collision count) of a finite set `S ⊆ F`:
`E(S) = #{ y : Fin 4 → F | (∀ i, y i ∈ S) ∧ ∑ i, y i = 0 }`.  In characteristic
`2` the constraint `∑ i, y i = 0` is `y₀ + y₁ = y₂ + y₃`, so this is the standard
additive energy of `S`. -/
noncomputable def additiveEnergy (S : Finset F) : ℕ :=
  (univ.filter (fun y : Fin 4 → F => (∀ i, y i ∈ S) ∧ ∑ i, y i = 0)).card

/-! ## The fourth-moment Fourier identity (the engine) -/

/-
**The fourth-moment / additive-energy identity.**  For any `S ⊆ F`,
`∑_s (∑_{x∈S} χ(s·x))⁴ = q · E(S)`.  This is the standard orthogonality
computation: expand the fourth power as a sum over quadruples `(a,b,c,d) ∈ S⁴`,
collapse the product of characters to `χ(s·(a+b+c+d))`, and swap the order of
summation so that the inner `∑_s χ(s·(a+b+c+d)) = q·[a+b+c+d = 0]` (character
orthogonality, `χ_sum_dual`).
-/
theorem sum_fourthPower_indicator_eq (S : Finset F) :
    ∑ s : F, (∑ x ∈ S, χ (s * x)) ^ 4
      = (Fintype.card F : ℤ) * (additiveEnergy S : ℤ) := by
  -- Expand the fourth power of the sum into a sum over all 4-tuples of elements from S.
  have h_expand : ∑ s : F, (∑ x ∈ S, (WalshAB.χ (s * x))) ^ 4 = ∑ s : F, ∑ p : Fin 4 → F, (∏ i : Fin 4, if p i ∈ S then WalshAB.χ (s * p i) else 0) := by
    refine' Finset.sum_congr rfl fun s _ => _;
    simp +decide [ Fin.prod_univ_four, Fin.sum_univ_four, pow_succ, Finset.sum_mul ];
    simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_inter, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
    rw [ ← Finset.sum_product', ← Finset.sum_product', ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => fun i => if i = 0 then x.1.1.1 else if i = 1 then x.1.1.2 else if i = 2 then x.1.2 else x.2 ) _ _ _ _ <;> simp +decide [ funext_iff, Fin.forall_fin_succ ];
    · tauto;
    · aesop;
    · tauto;
  -- Apply the character orthogonality relation to the inner sum.
  have h_inner : ∀ p : Fin 4 → F, (∑ s : F, ∏ i : Fin 4, if p i ∈ S then WalshAB.χ (s * p i) else 0) = (Fintype.card F : ℤ) * if (∀ i, p i ∈ S) ∧ (∑ i, p i) = 0 then 1 else 0 := by
    intro p
    by_cases h_all_in_S : ∀ i, p i ∈ S;
    · have h_inner : ∑ s : F, WalshAB.χ (s * (∑ i, p i)) = if (∑ i, p i) = 0 then (Fintype.card F : ℤ) else 0 := by
        convert WalshAB.χ_sum_dual ( ∑ i, p i ) using 1;
      simp_all +decide [ Finset.mul_sum _ _ _, MTuple.chi_sum_prod ];
    · simp_all +decide [ Finset.prod_ite ];
  simp_all +decide;
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun p hp => h_inner p ];
  simp +decide [ Finset.sum_ite, mul_comm, additiveEnergy ]

/-! ## Connection to the cross-correlation -/

/-
**The full-frequency fourth moment as additive energy.**  Using
`R(s) = 2·∑_{v ∈ Im Δf_a} χ(s·v)` (APN), the full fourth moment of the
cross-correlation is `16·q·E(Im Δf_a)`.
-/
theorem crossCorr_fourthMoment_eq_energy (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    ∑ s : F, (autocorrScaled f s a) ^ 4
      = 16 * (Fintype.card F : ℤ) * (additiveEnergy (derivImage f a) : ℤ) := by
  have h_sum : ∑ s : F, (∑ v ∈ MTuple.derivImage f a, χ (s * v)) ^ 4 = (Fintype.card F : ℤ) * (additiveEnergy (MTuple.derivImage f a) : ℤ) := by
    convert sum_fourthPower_indicator_eq ( MTuple.derivImage f a ) using 1;
  convert congr_arg ( fun x : ℤ => 16 * x ) h_sum using 1;
  · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext s ; rw [ crossCorr_eq_two_mul_image f hf a ha s ] ; ring;
  · ring

/-
**The derivative 4-collision count is the image additive energy.**  The image
`m`-tuple count `imgCount 4 f a 1` (with all coefficients `1`) counts exactly the
quadruples in `Im Δf_a` summing to `0`, i.e. the additive energy of the
derivative image.
-/
omit [CharP F 2] in
theorem imgCount_four_eq_additiveEnergy (f : F → F) (a : F) :
    imgCount 4 f a (fun _ => 1) = additiveEnergy (derivImage f a) := by
  refine' Finset.card_bij _ _ _ _;
  use fun y hy => y;
  · grobner;
  · grind;
  · grind +splitImp

/-! ## Input (B) as a single additive-energy value -/

/-
**Input (B) ⟺ the additive-energy value `16·E(Im Δf_a) = q³ + 2q²`.**
Combining `fourthMoment_eq_iff_collisionCount` (Layer A4), `preCount_eq` (APN:
`preCount 4 = 2⁴·imgCount 4`), and `imgCount_four_eq_additiveEnergy`, input **(B)**
is the single additive-energy value `16·E(Im Δf_a) = q³ + 2q²`.
-/
theorem fourthMoment_eq_iff_additiveEnergy (f : F → F) (hf : IsAPN f) (a : F)
    (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ (16 * (additiveEnergy (derivImage f a) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) := by
  convert Vanish.Foundations.fourthMoment_eq_iff_collisionCount f a using 1;
  rw [ ← Vanish.Foundations.imgCount_four_eq_additiveEnergy f a ];
  rw [ MTuple.preCount_eq 4 f hf a ha ] ; norm_cast

/-! ## Kasami specializations -/

variable {n k : ℕ}

/-- **Kasami: input (B) ⟺ the image additive-energy value.**  The Kasami
specialization of `fourthMoment_eq_iff_additiveEnergy`, using that the Kasami map
`x ↦ x^{d k}` is APN. -/
theorem kasami_fourthMoment_iff_additiveEnergy (hcard : Fintype.card F = 2 ^ n)
    (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) (a : F) (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F),
        (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4
        = 2 * (Fintype.card F : ℤ) ^ 3)
      ↔ (16 * (additiveEnergy (derivImage (fun x : F => x ^ d k) a) : ℤ)
          = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2) :=
  fourthMoment_eq_iff_additiveEnergy _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha

end Vanish.Foundations