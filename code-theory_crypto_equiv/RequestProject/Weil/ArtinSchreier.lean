import RequestProject.Weil.CharSum

/-!
# The Artin–Schreier curve and the sum-as-point-count dictionary

Fix a finite field `F = 𝔽_q` of characteristic `p = ringChar F`.  For `f ∈ F[X]` the
**Artin–Schreier curve** attached to `f` is
$$ C_f : \quad y^p - y = f(x). $$
The map `℘(y) = y^p - y` (the *Artin–Schreier operator*) is additive `𝔽_p`-linear with kernel the
prime subfield `𝔽_p`, hence every fibre `℘⁻¹(a)` has cardinality `p` or `0` (it is `p` iff
`Tr_{F/𝔽_p}(a) = 0`).  Counting points fibrewise gives
$$ \#C_f(\mathbb F_q) \;=\; \sum_{x} \#\{y : \wp(y) = f(x)\} \;=\; p\cdot\#\{x : \mathrm{Tr}(f(x)) = 0\}. $$

Applying additive orthogonality to the trace condition turns this into a sum of *character sums*,
which is the bridge between the Weil bound for `charSum` and the point-count bound that Stepanov's
method produces.  This module sets up `℘`, the point-count `asPointCount`, the prime subfield and
the curve-point predicate, and states the fibrewise structural facts.

## Main definitions
* `Weil.asOp y = y ^ p - y` — the Artin–Schreier operator `℘`.
* `Weil.primeField F` — the prime subfield, realised as the roots of `Xᵖ - X`.
* `Weil.asPointCount f` — the number of affine `𝔽_q`-points of `C_f`.
* `Weil.IsCurvePoint f x` — `x` lifts to a point of `C_f`, i.e. `f(x) ∈ image ℘`.

## Main statements (skeletons)
* `Weil.asOp_add` — additivity of `℘`.
* `Weil.asOp_fiber_card` — every fibre of `℘` has cardinality `0` or `p`.
* `Weil.asPointCount_eq_sum` — the point count as a fibrewise sum (Fubini).
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil

variable {F : Type*} [Field F] [Fintype F]

/-- The Artin–Schreier operator `℘(y) = y^p - y`, where `p = ringChar F` is the characteristic. -/
noncomputable def asOp (y : F) : F := y ^ (ringChar F) - y

omit [Fintype F] in
@[simp] lemma asOp_apply (y : F) : asOp y = y ^ (ringChar F) - y := rfl

/-- The prime subfield `𝔽_p ⊆ F`, realised as the set of roots of `Xᵖ - X`. -/
noncomputable def primeField (F : Type*) [Field F] [Fintype F] : Finset F :=
  Finset.univ.filter (fun t => t ^ (ringChar F) = t)

/-- `x` is (the `x`-coordinate of) a point of the Artin–Schreier curve `y^p - y = f(x)` iff
`f(x)` lies in the image of `℘`. -/
def IsCurvePoint (f : F[X]) (x : F) : Prop := ∃ y : F, asOp y = f.eval x

/-- The number of affine `𝔽_q`-points of the Artin–Schreier curve `y^p - y = f(x)`. -/
noncomputable def asPointCount (f : F[X]) : ℕ :=
  Nat.card {xy : F × F // asOp xy.2 = f.eval xy.1}

/-
The Artin–Schreier operator is additive: `℘(a + b) = ℘(a) + ℘(b)`.
-/
lemma asOp_add (a b : F) : asOp (a + b) = asOp a + asOp b := by
  convert add_pow_char a b;
  constructor <;> intro h;
  · convert add_pow_char a b;
  · convert congr_arg₂ ( · - · ) ( h ( ringChar F ) ) rfl using 1 ; ring;
    · unfold asOp; ring;
    · exact ⟨ CharP.char_is_prime F _ ⟩

/-
Every fibre of `℘` has cardinality `0` or `p`: since `℘` is additive with kernel the prime
subfield `𝔽_p`, each nonempty fibre is a coset of `𝔽_p`.
-/
lemma asOp_fiber_card (a : F) :
    Nat.card {y : F // asOp y = a} = 0 ∨ Nat.card {y : F // asOp y = a} = ringChar F := by
  -- Let's denote the set of solutions to $asOp y = a$ by $S_a$.
  set Sa := {y : F | asOp y = a};
  by_cases h : ∃ y, asOp y = a <;> simp_all +decide [ Set.ext_iff ];
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, asOp y₀ = a := h
  have h_coset : Sa = {y₀ + t | t ∈ primeField F} := by
    ext y; simp [Sa, primeField];
    constructor <;> intro h;
    · refine' ⟨ y - y₀, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add, asOp ];
      haveI := Fact.mk ( show Nat.Prime ( ringChar F ) from by
                          exact CharP.char_is_prime F _ ) ; simp_all +decide [ sub_pow_char ] ;
    · obtain ⟨ t, ht, rfl ⟩ := h; simp_all +decide [ asOp ] ;
      haveI := Fact.mk ( show Nat.Prime ( ringChar F ) from by
                          have := FiniteField.card F ( ringChar F ) ; aesop; ) ; simp_all +decide [ add_pow_char ] ;
  have h_card_primeField : Fintype.card (primeField F) = ringChar F := by
    have h_primeField_card : (primeField F).card ≤ ringChar F := by
      have h_primeField_card : (primeField F).card ≤ (Polynomial.roots (Polynomial.X ^ (ringChar F) - Polynomial.X : Polynomial F)).toFinset.card := by
        refine Finset.card_le_card ?_;
        simp +decide [ Finset.subset_iff, primeField ];
        exact fun x hx => ⟨ sub_ne_zero_of_ne <| ne_of_apply_ne Polynomial.natDegree <| by simp +decide [ Polynomial.natDegree_X_pow, show ringChar F ≠ 1 from by have := CharP.char_ne_one F ( ringChar F ) ; aesop ], sub_eq_zero.mpr hx ⟩;
      refine' le_trans h_primeField_card ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
      rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ Polynomial.natDegree_X_pow, show ringChar F > 1 from Nat.Prime.one_lt ( by have := CharP.char_is_prime F ( ringChar F ) ; aesop ) ];
    have h_primeField_card : (primeField F).card ≥ ringChar F := by
      have h_primeField_card : (primeField F).card ≥ Finset.card (Finset.image (fun n : ℕ => (n : F)) (Finset.range (ringChar F))) := by
        refine Finset.card_le_card ?_;
        simp +decide [ Finset.subset_iff, primeField ];
        intro a ha; have := ringChar.spec F; simp_all +decide ;
        have := this ( a ^ ringChar F - a ) ; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( show a ≤ a ^ ringChar F from Nat.le_self_pow ( by linarith [ show ringChar F > 0 from Nat.pos_of_ne_zero ( by aesop ) ] ) _ ) ] ;
        simp_all +decide [ sub_eq_iff_eq_add ];
        haveI := Fact.mk ( show Nat.Prime ( ringChar F ) from by
                            exact CharP.char_is_prime F _ ) ; simp +decide [ ← ZMod.natCast_eq_zero_iff ] ;
      rwa [ Finset.card_image_of_injOn, Finset.card_range ] at h_primeField_card;
      intro n hn m hm hnm; simp_all +decide ;
      have := ringChar.spec F ( n - m ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      cases le_total n m <;> simp_all +decide [ Nat.cast_sub ];
      · have := ringChar.spec F ( m - n ) ; simp_all +decide [ Nat.cast_sub ‹_› ] ;
        exact le_antisymm ‹_› ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( Nat.sub_pos_of_lt h ) this; linarith [ Nat.sub_add_cancel ( le_of_lt h ) ] );
      · exact le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( Nat.sub_pos_of_lt h ) this; omega ) ‹_›;
    convert le_antisymm ‹ ( primeField F ).card ≤ ringChar F › ‹ ( primeField F ).card ≥ ringChar F ›;
    rw [ Fintype.card_of_subtype ] ; aesop;
  convert h_card_primeField using 1;
  rw [ Fintype.card_of_subtype ];
  rotate_left;
  exact Finset.image ( fun t => y₀ + t ) ( primeField F );
  · simp_all +decide [ Set.ext_iff ];
    intro x; specialize h_coset x; aesop;
  · rw [ Finset.card_image_of_injective _ ( add_right_injective y₀ ), Fintype.card_of_subtype ] ; aesop

/-
Fubini for the point count: count the curve fibrewise over `x`.
-/
lemma asPointCount_eq_sum (f : F[X]) :
    asPointCount f = ∑ x : F, Nat.card {y : F // asOp y = f.eval x} := by
  simp +decide [ asPointCount, Nat.card_eq_fintype_card, Fintype.card_subtype ];
  rw [ Finset.card_filter ];
  erw [ Finset.sum_product ] ; aesop

end Weil