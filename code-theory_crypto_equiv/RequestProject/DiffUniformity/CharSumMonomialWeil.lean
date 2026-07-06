import Mathlib
import RequestProject.DiffUniformity.CharSumBounds
import RequestProject.DiffUniformity.CharSumWeilGaussSum

/-!
# The `d`-th-root character orthogonality and the monomial Weil bound

This module discharges the **sole remaining hypothesis** of the Gauss-sum gate of
`CharSumWeilGaussSum.lean`: the general `d`-th-root multiplicative-character
orthogonality. From it we obtain, *unconditionally*, the one-variable Weil bound
for an arbitrary **monomial** `f(x) = xᵈ`:

```
‖∑_{x ∈ F} ψ(xᵈ)‖ ≤ (d − 1)·√q       (ψ primitive).
```

The mechanism is the classical decomposition of a monomial character sum into
Gauss sums. Writing `T = {χ : χᵈ = 1}` for the group of multiplicative characters
of order dividing `d` and `S = T \ {1}`, character orthogonality on the cyclic
group `Fˣ` gives the **counting identity**

```
∑_{χ ∈ T} χ(y) = #{z ∈ Fˣ : zᵈ = y}        (y ≠ 0),
```

so that, after separating the trivial character and the point `x = 0`,

```
∑_x ψ(xᵈ) = ∑_{χ ∈ S} gaussSum χ ψ.
```

Since `Fˣ` (hence `MulChar F ℂ`) is cyclic, `#T ≤ d`, whence `#S ≤ d − 1`; each
Gauss sum has modulus `√q` (`CharSumBounds.norm_gaussSum`), and
`weilBoundOne_of_eq_sum_gaussSum` delivers the bound.

## Main results

* `sum_mulChar_pow_eq_card` — the `d`-th-root orthogonality / counting identity.
* `card_mulChar_pow_lt` — `#{χ : χᵈ = 1, χ ≠ 1} ≤ d − 1`.
* `charSumOne_monomial_eq_sum_gaussSum` — the Gauss-sum decomposition of `∑ ψ(xᵈ)`.
* `weilBoundOne_monomial` — the unconditional monomial Weil bound.
-/

open Finset BigOperators

open scoped Classical

namespace APN
namespace CharSumBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `MulChar F ℂ` is a finite type (it is finite, being isomorphic to `Fˣ`). -/
noncomputable instance instFintypeMulCharComplex : Fintype (MulChar F ℂ) :=
  Fintype.ofFinite _

/-- `MulChar F ℂ` is a cyclic group (it is isomorphic to the cyclic unit group
`Fˣ`). -/
instance instIsCyclicMulCharComplex : IsCyclic (MulChar F ℂ) := by
  obtain ⟨e⟩ := MulChar.mulEquiv_units F ℂ
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-
**Character separation for non-`d`-th-powers.** If `y ≠ 0` is not a `d`-th
power in the field `F`, then some multiplicative character of order dividing `d`
takes a value `≠ 1` at `y`. This is the dual/duality input (it uses that `ℂ` has
enough roots of unity), obtained by separating the nontrivial class of `y` in the
quotient `Fˣ / (Fˣ)^d`.
-/
theorem exists_mulChar_pow_ne_one (d : ℕ) (hd : 1 ≤ d) (y : F) (hy : y ≠ 0)
    (hnot : ¬ ∃ w : F, w ≠ 0 ∧ w ^ d = y) :
    ∃ χ : MulChar F ℂ, χ ^ d = 1 ∧ χ y ≠ 1 := by
  obtain ⟨χ, hχ⟩ : ∃ χ : (Fˣ ⧸ (MonoidHom.range (powMonoidHom d : Fˣ →* Fˣ))) →* ℂˣ, χ (QuotientGroup.mk (Units.mk0 y hy)) ≠ 1 := by
    have h_quotient : (QuotientGroup.mk (Units.mk0 y hy) : Fˣ ⧸ (MonoidHom.range (powMonoidHom d : Fˣ →* Fˣ))) ≠ 1 := by
      simp +decide [ QuotientGroup.eq_one_iff ];
      exact fun x hx => hnot ⟨ x, by simp, by simpa [ Units.ext_iff ] using hx ⟩;
    have := @CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ( Fˣ ⧸ ( MonoidHom.range ( powMonoidHom d : Fˣ →* Fˣ ) ) ) ℂ
    generalize_proofs at *; (
    convert this h_quotient using 1);
  refine' ⟨ MulChar.ofUnitHom ( χ.comp ( QuotientGroup.mk' _ ) ), _, _ ⟩;
  · ext a;
    rw [ MulChar.pow_apply' ];
    · simp +decide [ MulChar.ofUnitHom_coe ];
      rw [ ← Units.val_pow_eq_pow_val, ← map_pow ];
      erw [ show ( a ^ d : Fˣ ⧸ ( powMonoidHom d : Fˣ →* Fˣ ).range ) = 1 from QuotientGroup.eq.mpr <| by aesop ] ; simp +decide;
    · linarith;
  · simp_all +decide [ MulChar.ofUnitHom ];
    convert hχ using 1;
    congr!;
    exact Units.ext rfl

/-
**`d`-th-root character orthogonality (counting form).** For `y ≠ 0` in a
finite field, the sum of `χ(y)` over all multiplicative characters of order
dividing `d` counts the `d`-th roots of `y`.
-/
theorem sum_mulChar_pow_eq_card (d : ℕ) (hd : 1 ≤ d) (y : F) (hy : y ≠ 0) :
    ∑ χ ∈ univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1), χ y
      = ((univ.filter (fun z : F => z ^ d = y)).card : ℂ) := by
  -- Case 1: Assume there exists $w \in F^\times$ such that $w^d = y$.
  by_cases h_exists : ∃ w : Fˣ, w ^ d = Units.mk0 y hy;
  · -- In this case, each character in the filter has χ y = 1.
    have h_char_one : ∀ χ : MulChar F ℂ, χ ^ d = 1 → χ y = 1 := by
      obtain ⟨ w, hw ⟩ := h_exists;
      intro χ hχ
      have hχ_w : χ w ^ d = 1 := by
        convert congr_arg ( fun f : MulChar F ℂ => f w ) hχ using 1;
        · exact Eq.symm (MulChar.pow_apply_coe χ d w);
        · simp +decide [ MulChar.one_apply ];
      replace hw := congr_arg ( fun x : Fˣ => χ x ) hw ; aesop;
    have h_card_filter : (Finset.filter (fun z : Fˣ => z ^ d = Units.mk0 y hy) Finset.univ).card = (Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ).card := by
      have h_card_filter : (Finset.filter (fun z : Fˣ => z ^ d = 1) Finset.univ).card = (Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ).card := by
        obtain ⟨ e ⟩ := MulChar.mulEquiv_units F ℂ;
        refine' Finset.card_bij ( fun z hz => e.symm z ) _ _ _ <;> simp +decide [ e.symm_apply_eq ];
        · intro a ha; replace ha := congr_arg e.symm ha; simp_all +decide [ ← map_pow ] ;
        · exact fun χ hχ => by simpa using congr_arg e hχ;
      rw [ ← h_card_filter ];
      obtain ⟨ w, hw ⟩ := h_exists;
      refine' Finset.card_bij ( fun z hz => z * w⁻¹ ) _ _ _ <;> simp_all +decide [ mul_pow ];
      exact fun b hb => ⟨ b * w, by simp +decide [ mul_pow, hb, hw ], by simp +decide ⟩;
    have h_card_filter : (Finset.filter (fun z : F => z ^ d = y) Finset.univ).card = (Finset.filter (fun z : Fˣ => z ^ d = Units.mk0 y hy) Finset.univ).card := by
      refine' Finset.card_bij ( fun z hz => Units.mk0 z ( by
        cases d <;> aesop ) ) _ _ _ <;> simp +decide [ Units.ext_iff ];
    rw [ Finset.sum_congr rfl fun x hx => h_char_one x <| Finset.mem_filter.mp hx |>.2 ] ; aesop;
  · obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : MulChar F ℂ, χ₀ ^ d = 1 ∧ χ₀ y ≠ 1 := by
      apply exists_mulChar_pow_ne_one d hd y hy;
      exact fun ⟨ w, hw, hw' ⟩ => h_exists ⟨ Units.mk0 w hw, by simpa [ Units.ext_iff ] using hw' ⟩;
    -- By the properties of characters, we can factor out $\chi_0(y)$ from the sum.
    have h_factor : ∑ χ ∈ Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ, χ y = χ₀ y * ∑ χ ∈ Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ, χ y := by
      have h_factor : Finset.image (fun χ => χ₀ * χ) (Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ) = Finset.filter (fun χ : MulChar F ℂ => χ ^ d = 1) Finset.univ := by
        ext χ; simp [hχ₀];
        simp +decide [ mul_pow, hχ₀.1 ];
      conv_lhs => rw [ ← h_factor, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
      simp +decide [ Finset.mul_sum _ _ _, mul_assoc ];
    by_cases h : ∑ χ ∈ Finset.filter ( fun χ : MulChar F ℂ => χ ^ d = 1 ) Finset.univ, χ y = 0 <;> simp_all +decide;
    rw [ Finset.card_eq_zero.mpr ];
    · norm_num;
    · ext z; simp [h_exists];
      contrapose! h_exists;
      exact ⟨ Units.mk0 z ( by rintro rfl; simp_all +decide [ zero_pow ( by linarith : d ≠ 0 ) ] ), by simpa [ Units.ext_iff ] using h_exists ⟩

/-
The number of nontrivial multiplicative characters of order dividing `d` is at
most `d − 1`.
-/
theorem card_mulChar_pow_lt (d : ℕ) (hd : 1 ≤ d) :
    (univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1 ∧ χ ≠ 1)).card ≤ d - 1 := by
  -- Let A = univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1) and B = univ.filter (fun χ => χ ^ d = 1 ∧ χ ≠ 1).
  set A := Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1)
  set B := Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1 ∧ χ ≠ 1);
  -- Since $B = A \setminus \{1\}$, we have $|B| = |A| - 1$.
  have hB_card : B.card = A.card - 1 := by
    rw [ show B = A \ { 1 } by ext; aesop ] ; rw [ Finset.card_sdiff ] ; aesop;
  exact hB_card.le.trans ( Nat.sub_le_sub_right ( IsCyclic.card_pow_eq_one_le ( by assumption ) ) _ )

/-
**The monomial Gauss-sum decomposition.** For a primitive additive character
`ψ`, the monomial character sum `∑_x ψ(xᵈ)` is the sum of the Gauss sums of the
nontrivial characters of order dividing `d`.
-/
theorem charSumOne_monomial_eq_sum_gaussSum (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (d : ℕ) (hd : 1 ≤ d) :
    charSumOne ψ (fun x => x ^ d)
      = ∑ χ ∈ univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1 ∧ χ ≠ 1), gaussSum χ ψ := by
  -- Let's rewrite the sum using the definition of `gaussSum`.
  have h_sum_gauss : ∑ χ ∈ Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1), gaussSum χ ψ = charSumOne ψ (fun x => x ^ d) - 1 := by
    have h_sum_gauss : ∑ χ ∈ Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1), gaussSum χ ψ = ∑ x ∈ Finset.univ.erase 0, (∑ χ ∈ Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1), χ x) * ψ x := by
      simp +decide [ Finset.sum_mul, gaussSum ];
      rw [ Finset.sum_comm ];
      simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', MulChar.map_zero ];
    -- Apply the counting identity to each term in the sum.
    have h_count : ∀ x ∈ Finset.univ.erase 0, (∑ χ ∈ Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1), χ x) = ((Finset.univ.filter (fun z : F => z ^ d = x)).card : ℂ) := by
      intro x hx; exact sum_mulChar_pow_eq_card d hd x ( Finset.ne_of_mem_erase hx ) ;
    have h_sum_zero : ∑ x ∈ Finset.univ, (∑ z ∈ Finset.univ, (if z ^ d = x then 1 else 0) : ℂ) * ψ x = ∑ z ∈ Finset.univ, ψ (z ^ d) := by
      simp +decide only [Finset.sum_mul _ _ _];
      rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
    simp_all +decide [ Finset.sum_ite ];
    simp +decide [ Finset.filter_eq', Finset.filter_and, hd, charSumOne ];
    rw [ if_neg ( by linarith ), Finset.inter_univ, Finset.card_singleton ];
  rw [ show ( Finset.filter ( fun χ : MulChar F ℂ => χ ^ d = 1 ) Finset.univ ) = Finset.filter ( fun χ : MulChar F ℂ => χ ^ d = 1 ∧ χ ≠ 1 ) Finset.univ ∪ { 1 } from ?_, Finset.sum_union ] at h_sum_gauss <;> norm_num at *;
  · have h_gauss_one : gaussSum (1 : MulChar F ℂ) ψ = -1 := by
      have h_gauss_one : gaussSum (1 : MulChar F ℂ) ψ = ∑ x ∈ Finset.univ.filter (fun x : F => x ≠ 0), ψ x := by
        unfold gaussSum;
        rw [ Finset.sum_filter ] ; congr ; ext x ; by_cases hx : x = 0 <;> simp +decide [ hx ];
        · grind +suggestions;
        · simp +decide [ hx, MulChar.one_apply ];
      have h_sum_zero : ∑ x : F, ψ x = 0 := by
        convert AddChar.sum_eq_zero_of_ne_one _;
        · infer_instance;
        · intro h; simp_all +decide [ AddChar.IsPrimitive ] ;
          exact hψ ( show ( 1 : F ) ≠ 0 by simp +decide ) ( by ext; simp +decide [ AddChar.mulShift_apply ] );
      simp_all +decide [ Finset.filter_ne' ];
    grobner;
  · ext χ; by_cases h : χ = 1 <;> simp +decide [ h ] ;

/-- **The unconditional monomial Weil bound.** Every monomial `f(x) = xᵈ`
(`d ≥ 1`) satisfies the one-variable Weil bound `‖∑_x ψ(xᵈ)‖ ≤ (d − 1)·√q`. -/
theorem weilBoundOne_monomial (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (d : ℕ) (hd : 1 ≤ d) :
    WeilBoundOne ψ (fun x => x ^ d) d :=
  weilBoundOne_of_eq_sum_gaussSum ψ hψ (fun x => x ^ d) d
    (univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1 ∧ χ ≠ 1))
    (card_mulChar_pow_lt d hd) hd
    (fun χ hχ => (mem_filter.mp hχ).2.2)
    (charSumOne_monomial_eq_sum_gaussSum ψ hψ d hd)

end CharSumBounds
end APN