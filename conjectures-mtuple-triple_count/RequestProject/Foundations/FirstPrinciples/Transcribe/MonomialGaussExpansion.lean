import Mathlib
import RequestProject.Foundations.FirstPrinciples.Transcribe.MulCharDual

/-!
# Transcription — Leaf L1, module 3: the monomial → Gauss-sum expansion (Lidl–Niederreiter Thm 5.30)

This module supplies the **analytic heart** of the additive→multiplicative
character-sum bridge `GaussSumDecomp.kasami_crossCorr_eq_gaussInt` (leaf **L1** in
`FirstPrinciplesTranscriptionRoadmap.md`): the expansion of a monomial additive
character sum into multiplicative-character Gauss sums.

It proves, as **real proofs**, the two elementary ingredients:

* `charSum_mulShift_eq` — the Gauss-sum scaling/substitution
  `∑_y χ(y)·ψ(c·y) = χ⁻¹(c)·g(χ,ψ)` for a unit `c` (Lidl–Niederreiter §5.2);
* `addCharSum_monomial_eq_fibre` — the fibrewise rewrite
  `∑_x ψ(c·xᵐ) = ∑_y (#{x | xᵐ = y})·ψ(c·y)`.

and states, as the single classical **leaf**, the full expansion
`∑_x ψ(c·xᵐ) = ∑_{j=1}^{d-1} (χ₁ʲ)⁻¹(c)·g(χ₁ʲ, ψ)` indexed by the powers of a
character `χ₁` of order `d = gcd(m, q−1)` (Lidl–Niederreiter Thm 5.30, cyclic
form).  Producing such a `χ₁` is roadmap module `MulCharDual` (the dual
orthogonality on the cyclic group `Fˣ`); combining it with the two real lemmas
above and `GaussSumDecomp.powerMap_fibreCount` discharges the leaf.

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 5 (Thm 5.30: monomial character sums).
* Ireland–Rosen, Ch. 8, 14.
* Mathlib: `gaussSum_mulShift`, `Finset.sum_fiberwise`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open MulChar AddChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **Gauss-sum substitution (Lidl–Niederreiter §5.2).**  Scaling the additive
character by a unit `c` rescales the character sum by `χ⁻¹(c)`:
`∑_y χ(y)·ψ(c·y) = χ⁻¹(c)·g(χ,ψ)`.  Real proof from Mathlib's `gaussSum_mulShift`. -/
theorem charSum_mulShift_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (c : Fˣ) :
    ∑ y : F, χ y * ψ ((c : F) * y) = χ⁻¹ (c : F) * gaussSum χ ψ := by
  have h := gaussSum_mulShift χ ψ c
  have hgs : gaussSum χ (mulShift ψ c) = ∑ y : F, χ y * ψ ((c : F) * y) := by
    simp [gaussSum, mulShift_apply]
  have hcne : χ (c : F) ≠ 0 := (IsUnit.map χ c.isUnit).ne_zero
  rw [← hgs, inv_apply_eq_inv' χ (c : F), eq_inv_mul_iff_mul_eq₀ hcne, ← h, mul_comm]

/-- **Fibrewise rewrite of a monomial additive character sum.**  Grouping `x` by
the value of `xᵐ`, `∑_x ψ(c·xᵐ) = ∑_y (#{x | xᵐ = y})·ψ(c·y)`.  Real proof. -/
theorem addCharSum_monomial_eq_fibre (ψ : AddChar F ℂ) (c : F) (m : ℕ) :
    ∑ x : F, ψ (c * x ^ m)
      = ∑ y : F, ((Finset.univ.filter (fun x : F => x ^ m = y)).card : ℂ) * ψ (c * y) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : F => x ^ m) (fun x => ψ (c * x ^ m))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => ψ (c * y))
        (by intro x hx; rw [(Finset.mem_filter.mp hx).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-
**Splitting a field sum off the zero point.**  For `g : F → ℂ`,
`∑_{y:F} g y = g 0 + ∑_{y:Fˣ} g ↑y`.  Real proof (units reindexing).
-/
theorem sum_field_eq_zero_add_units (g : F → ℂ) :
    ∑ y : F, g y = g 0 + ∑ y : Fˣ, g (y : F) := by
  rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), add_comm ];
  refine' congrArg _ ( Finset.sum_bij ( fun x hx => Units.mk0 x ( by aesop ) ) _ _ _ _ ) <;> aesop

/-
**The `m`-th-power fibre over `F` reduces to the fibre over `Fˣ`** for a nonzero
target and `m ≥ 1` (zero is not a solution of `xᵐ = y` when `y ≠ 0`).  Real proof.
-/
theorem fibre_field_card_eq_units (m : ℕ) (hm : 1 ≤ m) (y : Fˣ) :
    (Finset.univ.filter (fun x : F => x ^ m = (y : F))).card
      = (Finset.univ.filter (fun x : Fˣ => x ^ m = y)).card := by
  convert Finset.card_image_iff.mpr _ using 1;
  convert rfl;
  rotate_left;
  exact fun x => x;
  exact instDecidableEqOfLawfulBEq;
  · exact fun x hx y hy hxy => Units.ext hxy;
  · ext x;
    by_cases hx : x = 0 <;> simp +decide [ hx, Units.ext_iff ];
    · cases m <;> simp_all +decide;
      exact Ne.symm y.ne_zero;
    · exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun ha => ⟨ Units.mk0 x hx, ha, rfl ⟩ ⟩

/-
**Character sum over units = scaled Gauss sum.**  Reindexing `charSum_mulShift_eq`
to `Fˣ` (the `y = 0` term vanishes as `χ 0 = 0`):
`∑_{y:Fˣ} χ(↑y)·ψ(↑c·↑y) = χ⁻¹(↑c)·g(χ,ψ)`.  Real proof.
-/
theorem charSum_units_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (c : Fˣ) :
    ∑ y : Fˣ, χ (y : F) * ψ ((c : F) * (y : F)) = χ⁻¹ (c : F) * gaussSum χ ψ := by
  convert charSum_mulShift_eq χ ψ c using 1;
  convert sum_field_eq_zero_add_units ( fun y => χ y * ψ ( c * y ) ) |> Eq.symm using 1;
  simp +decide [ χ.map_zero ]

/-
**Gauss sum of the trivial character is `-1`** for a primitive additive
character (`∑_{y≠0} ψ(y) = -1`).  Real proof.
-/
theorem gaussSum_one_eq_neg_one (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum (1 : MulChar F ℂ) ψ = -1 := by
  -- Since ψ is primitive, it is nontrivial.
  have h_nontrivial : ψ ≠ 1 := by
    intro h; simp_all +decide [ AddChar.IsPrimitive ] ;
    exact hψ ( show ( 1 : F ) ≠ 0 by simp +decide ) ( by ext; simp +decide [ mulShift ] );
  -- Since ψ is nontrivial, we have ∑_{y:F} ψ y = 0.
  have h_sum_zero : ∑ y : F, ψ y = 0 := by
    exact sum_eq_zero_iff_ne_zero.mpr h_nontrivial;
  -- Since ψ is nontrivial, we have ∑_{y:F} ψ y = ψ 0 + ∑_{y:Fˣ} ψ y.
  have h_sum_split : ∑ y : F, ψ y = ψ 0 + ∑ y : Fˣ, ψ (y : F) := by
    convert sum_field_eq_zero_add_units _;
  simp_all +decide [ gaussSum ];
  convert eq_neg_of_add_eq_zero_right h_sum_zero using 1;
  convert sum_field_eq_zero_add_units ( fun y => ( 1 : MulChar F ℂ ) y * ψ y ) using 1;
  simp +decide [ MulChar.one_apply ]

/-- **Fused fibre = character sum over `F`.**  For `y : Fˣ`, the `F`-cardinality of the
`m`-th-power fibre of `↑y` equals `∑_{j<d} χ₁ʲ(↑y)`, combining `fibre_field_card_eq_units`
with `mulChar_pow_sum_eq_fibreCard`.  Real proof. -/
theorem fibre_field_eq_mulCharSum (m : ℕ) (hm : 1 ≤ m) (χ₁ : MulChar F ℂ)
    (hord : orderOf χ₁ = Nat.gcd m (Fintype.card F - 1)) (y : Fˣ) :
    ((Finset.univ.filter (fun x : F => x ^ m = (y : F))).card : ℂ)
      = ∑ j ∈ Finset.range (orderOf χ₁), (χ₁ ^ j) (y : F) := by
  rw [fibre_field_card_eq_units m hm y, ← mulChar_pow_sum_eq_fibreCard m hm χ₁ hord y]

/-
**The monomial → Gauss-sum expansion (Lidl–Niederreiter Thm 5.30, the L1 leaf).**
Let `ψ` be a primitive additive character, `c` a unit, `m ≥ 1`, and let `χ₁` be a
multiplicative character of order exactly `d = gcd(m, q−1)`.  Then the trivial- and
unit-character contributions cancel and
`∑_x ψ(c·xᵐ) = ∑_{j=1}^{d-1} (χ₁ʲ)⁻¹(c)·g(χ₁ʲ, ψ)`.

The proof combines `addCharSum_monomial_eq_fibre`, the character-count of fibres
(`GaussSumDecomp.powerMap_fibreCount` together with the dual orthogonality
`∑_{χᵈ=1} χ(y) = #{x | xᵈ = y}` of roadmap module `MulCharDual`), and
`charSum_mulShift_eq`.  Carried here as the single classical leaf of this module.
-/
theorem monomial_addCharSum_eq_gaussSum_sum
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (c : Fˣ) (m : ℕ) (hm : 1 ≤ m)
    (χ₁ : MulChar F ℂ) (hord : orderOf χ₁ = Nat.gcd m (Fintype.card F - 1)) :
    ∑ x : F, ψ ((c : F) * x ^ m)
      = ∑ j ∈ Finset.Ico 1 (orderOf χ₁), (χ₁ ^ j)⁻¹ (c : F) * gaussSum (χ₁ ^ j) ψ := by
  rw [ addCharSum_monomial_eq_fibre, sum_field_eq_zero_add_units ];
  have h_rewrite : ∑ y : Fˣ, ((Finset.univ.filter (fun x : F => x ^ m = (y : F))).card : ℂ) * ψ ((c : F) * (y : F)) = ∑ j ∈ Finset.range (orderOf χ₁), (χ₁ ^ j)⁻¹ (c : F) * gaussSum (χ₁ ^ j) ψ := by
    have h_rewrite : ∑ y : Fˣ, ((Finset.univ.filter (fun x : F => x ^ m = (y : F))).card : ℂ) * ψ (c * (y : F)) = ∑ j ∈ Finset.range (orderOf χ₁), ∑ y : Fˣ, (χ₁ ^ j) (y : F) * ψ (c * (y : F)) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro y hy; rw [ ← Finset.sum_mul _ _ _ ] ; rw [ fibre_field_eq_mulCharSum m hm χ₁ hord y ] ;
    rw [ h_rewrite ];
    exact Finset.sum_congr rfl fun _ _ => charSum_units_eq _ _ _;
  simp_all +decide [ Finset.sum_range_succ', Finset.filter_eq', Finset.filter_and ];
  rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ hm, hord.symm ];
  · rw [ if_neg ( by linarith ), Finset.inter_univ, Finset.card_singleton, gaussSum_one_eq_neg_one ψ hψ ] ; ring;
  · exact hord.symm ▸ Nat.gcd_pos_of_pos_left _ hm

end Vanish.Foundations.FirstPrinciples.Transcribe